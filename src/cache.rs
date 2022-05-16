use std::{
    alloc::{alloc, dealloc, Layout},
    collections::hash_map::DefaultHasher,
    hash::{Hash, Hasher},
    marker::PhantomPinned,
    pin::Pin,
    ptr,
    sync::Mutex,
};

use crate::slice::Slice;
type DeleterFn = Box<dyn FnMut(&Slice, *mut u8)>;

pub fn new_lru_cache(capacity: usize) -> Box<dyn Cache> {
    Box::new(ShardedLRUCache::new(capacity))
}

pub struct Handle {}

pub trait Cache {
    fn insert(
        &mut self,
        key: &Slice,
        value: *mut u8,
        charge: usize,
        deleter: DeleterFn,
    ) -> *mut Handle;
    fn lookup(&mut self, key: &Slice) -> *mut Handle;
    fn release(&mut self, handle: *mut Handle);
    fn value(&mut self, handle: *mut Handle) -> *mut u8;
    fn erase(&mut self, key: &Slice);
    fn new_id(&mut self) -> u64;
    fn prune(&mut self);
    /// Return an estimate of the combined charges of all elements stored in the
    /// cache.
    fn total_charge(&self) -> usize;
}

#[repr(C)]
struct LRUHandle {
    value: *mut u8,
    deleter: DeleterFn,

    next_hash: *mut LRUHandle,
    next: *mut LRUHandle,
    prev: *mut LRUHandle,

    charge: usize,
    key_length: usize,
    in_cache: bool,
    refs: u32,
    hash: u32,
    key_data: [u8; 1],
}
// type LRUHandleNode = Option<Rc<RefCell<LRUHandle>>>;
impl LRUHandle {
    fn key(&self) -> Slice {
        // TODO: change
        assert!(!ptr::eq(self.next, self));
        Slice::new(&self.key_data as *const _, self.key_length)
    }
    fn get_layout(key_size: usize) -> Layout {
        let needed = std::mem::size_of::<Self>() + key_size - 1;
        let align = std::mem::align_of::<*mut u8>();
        Layout::from_size_align(needed, align).unwrap()
    }
}
impl Default for LRUHandle {
    fn default() -> Self {
        Self {
            value: ptr::null_mut(),
            deleter: Box::new(|_, _| {}),
            next_hash: ptr::null_mut(),
            next: ptr::null_mut(),
            prev: ptr::null_mut(),
            charge: Default::default(),
            key_length: Default::default(),
            in_cache: Default::default(),
            refs: Default::default(),
            hash: Default::default(),
            key_data: [0],
        }
    }
}

struct HandleTable {
    length: usize,
    elems: usize,
    list: Vec<*mut LRUHandle>,
}

impl HandleTable {
    pub fn new() -> Self {
        Default::default()
    }
    pub fn lookup(&mut self, key: &Slice, hash: u32) -> *mut LRUHandle {
        unsafe { *self.find_pointer(key, hash) }
    }
    pub fn insert(&mut self, h: *mut LRUHandle) -> *mut LRUHandle {
        unsafe {
            let p = self.find_pointer(&(*h).key(), (*h).hash);
            let old = *p;
            (*h).next_hash = if old.is_null() {
                ptr::null_mut()
            } else {
                (*old).next_hash
            };
            *p = h;
            if old.is_null() {
                self.elems += 1;
                if self.elems > self.length {
                    self.resize();
                }
            }
            old
        }
    }
    pub fn remove(&mut self, key: &Slice, hash: u32) -> *mut LRUHandle {
        unsafe {
            let p = self.find_pointer(key, hash);
            let result = *p;
            if !result.is_null() {
                *p = (*result).next_hash;
                self.elems -= 1;
            }
            result
        }
    }
    fn find_pointer(&mut self, key: &Slice, hash: u32) -> *mut *mut LRUHandle {
        unsafe {
            let mut p = self
                .list
                .get_unchecked_mut(hash as usize & (self.length - 1));
            while !p.is_null() && ((**p).hash != hash || &(**p).key() != key) {
                p = &mut (**p).next_hash
            }
            p
        }
    }
    fn resize(&mut self) {
        let mut new_length = 4;
        while new_length < self.elems {
            new_length *= 2;
        }
        let mut new_list: Vec<*mut LRUHandle> = Vec::with_capacity(new_length);
        for _ in 0..new_length {
            new_list.push(ptr::null_mut());
        }
        let mut count = 0;
        for i in 0..self.length {
            unsafe {
                let mut head = *self.list.get_unchecked_mut(i);
                while !head.is_null() {
                    let next = (*head).next_hash;
                    let hash = (*head).hash;
                    let p = new_list.get_unchecked_mut(hash as usize & (new_length - 1));
                    (*head).next_hash = *p;
                    *p = head;
                    head = next;
                    count += 1;
                }
            }
        }
        assert_eq!(self.elems, count);
        self.list = new_list;
        self.length = new_length;
    }
}
impl Default for HandleTable {
    fn default() -> Self {
        let mut list = Self {
            length: 0,
            elems: 0,
            list: Vec::new(),
        };
        list.resize();
        list
    }
}

struct LRUCacheInner {
    capacity: usize,
    usage: usize,
    lru: LRUHandle,
    in_use: LRUHandle,
    table: HandleTable,
    _pin: PhantomPinned,
}

impl LRUCacheInner {
    fn new() -> Pin<Box<Self>> {
        let r = Self {
            capacity: 0,
            usage: 0,
            lru: LRUHandle::default(),
            in_use: LRUHandle::default(),
            table: HandleTable::new(),
            _pin: PhantomPinned,
        };
        let mut r = Box::pin(r);
        let lru = &r.lru as *const _ as *mut LRUHandle;
        let in_use = &r.in_use as *const _ as *mut LRUHandle;
        unsafe {
            let mut_ref: Pin<&mut Self> = Pin::as_mut(&mut r);
            let mut_ref = Pin::get_unchecked_mut(mut_ref);
            mut_ref.lru.next = lru;
            mut_ref.lru.prev = lru;
            mut_ref.in_use.next = in_use;
            mut_ref.in_use.prev = in_use;
        }
        r
    }
    fn lookup(&mut self, key: &Slice, hash: u32) -> *mut Handle {
        let e = self.table.lookup(key, hash);
        if !e.is_null() {
            self.addref(e);
        }
        e as *mut Handle
    }
    fn release(&mut self, handle: *mut Handle) {
        self.unref(handle as *mut LRUHandle);
    }
    fn insert(
        &mut self,
        key: &Slice,
        hash: u32,
        value: *mut u8,
        charge: usize,
        deleter: DeleterFn,
    ) -> *mut Handle {
        unsafe {
            let layout = LRUHandle::get_layout(key.size());
            let e = alloc(layout) as *mut LRUHandle;
            (*e).value = value;
            ptr::write(ptr::addr_of_mut!((*e).deleter), deleter);
            // (*e).deleter = Box::new(|_, _| {});
            // (*e).deleter = deleter;
            (*e).charge = charge;
            (*e).key_length = key.size();
            (*e).hash = hash;
            (*e).in_cache = false;
            (*e).refs = 1;
            ptr::copy_nonoverlapping(key.data(), &mut (*e).key_data as *mut u8, key.size());
            if self.capacity > 0 {
                (*e).refs += 1;
                (*e).in_cache = true;
                self.lru_append(&self.in_use as *const _ as *mut _, e);
                self.usage += charge;
                let t = self.table.insert(e);
                self.finish_erase(t);
            } else {
                (*e).next = ptr::null_mut();
            }
            while self.usage > self.capacity && !ptr::eq(self.lru.next, &self.lru) {
                let old = self.lru.next;
                assert!((*old).refs == 1);
                let t = self.table.remove(&(*old).key(), (*old).hash);
                let erased = self.finish_erase(t);
                if !erased {
                    assert!(erased);
                }
            }
            e as *mut Handle
        }
    }
    fn finish_erase(&mut self, e: *mut LRUHandle) -> bool {
        if !e.is_null() {
            unsafe {
                assert!((*e).in_cache);
                self.lru_remove(e);
                (*e).in_cache = false;
                self.usage -= (*e).charge;
                self.unref(e);
            }
        }
        !e.is_null()
    }
    fn erase(&mut self, key: &Slice, hash: u32) {
        let e = self.table.remove(key, hash);
        self.finish_erase(e);
    }
    fn prune(&mut self) {
        while !ptr::eq(self.lru.next, &self.lru) {
            unsafe {
                let e = self.lru.next;
                assert!((*e).refs == 1);
                let t = self.table.remove(&(*e).key(), (*e).hash);
                let erased = self.finish_erase(t);
                if !erased {
                    assert!(erased);
                }
            }
        }
    }
    fn addref(&mut self, e: *mut LRUHandle) {
        unsafe {
            if (*e).refs == 1 && (*e).in_cache {
                self.lru_remove(e);
                self.lru_append(&self.in_use as *const _ as *mut _, e);
            }
            (*e).refs += 1;
        }
    }
    fn unref(&mut self, e: *mut LRUHandle) {
        unsafe {
            assert!((*e).refs > 0);
            (*e).refs -= 1;
            if (*e).refs == 0 {
                assert!(!(*e).in_cache);
                ((*e).deleter)(&(*e).key(), (*e).value);
                ptr::drop_in_place(&mut (*e).deleter as *mut DeleterFn);
                dealloc(e as *mut u8, LRUHandle::get_layout((*e).key_length));
            } else if (*e).in_cache && (*e).refs == 1 {
                self.lru_remove(e);
                self.lru_append(&self.lru as *const _ as *mut _, e);
            }
        }
    }
    fn lru_remove(&mut self, e: *mut LRUHandle) {
        unsafe {
            (*(*e).next).prev = (*e).prev;
            (*(*e).prev).next = (*e).next;
        }
    }
    fn lru_append(&mut self, list: *mut LRUHandle, e: *mut LRUHandle) {
        unsafe {
            (*e).next = list;
            (*e).prev = (*list).prev;
            (*(*e).prev).next = e;
            (*(*e).next).prev = e;
        }
    }
}
impl Drop for LRUCacheInner {
    fn drop(&mut self) {
        assert!(ptr::eq(self.in_use.next, ptr::addr_of!(self.in_use)));
        let mut e = self.lru.next;
        while !ptr::eq(e, &self.lru) {
            unsafe {
                let next = (*e).next;
                assert!((*e).in_cache);
                (*e).in_cache = false;
                assert!((*e).refs == 1);
                self.unref(e);
                e = next;
            }
        }
    }
}

struct LRUCache {
    inner: Mutex<Pin<Box<LRUCacheInner>>>,
}

impl LRUCache {
    pub fn new() -> Self {
        Self {
            inner: Mutex::new(LRUCacheInner::new()),
        }
    }
    pub fn lookup(&mut self, key: &Slice, hash: u32) -> *mut Handle {
        let mut inner = self.inner.lock().unwrap();
        unsafe {
            let mut_ref: Pin<&mut LRUCacheInner> = Pin::as_mut(&mut inner);
            Pin::get_unchecked_mut(mut_ref).lookup(key, hash)
        }
    }
    pub fn release(&mut self, handle: *mut Handle) {
        let mut inner = self.inner.lock().unwrap();
        unsafe {
            let mut_ref: Pin<&mut LRUCacheInner> = Pin::as_mut(&mut inner);
            Pin::get_unchecked_mut(mut_ref).unref(handle as *mut LRUHandle);
        }
    }
    pub fn insert(
        &mut self,
        key: &Slice,
        hash: u32,
        value: *mut u8,
        charge: usize,
        deleter: DeleterFn,
    ) -> *mut Handle {
        let mut inner = self.inner.lock().unwrap();
        unsafe {
            let mut_ref: Pin<&mut LRUCacheInner> = Pin::as_mut(&mut inner);
            Pin::get_unchecked_mut(mut_ref).insert(key, hash, value, charge, deleter)
        }
    }
    pub fn set_capacity(&self, capacity: usize) {
        let mut inner = self.inner.lock().unwrap();
        unsafe {
            let mut_ref: Pin<&mut LRUCacheInner> = Pin::as_mut(&mut inner);
            Pin::get_unchecked_mut(mut_ref).capacity = capacity
        }
    }
    pub fn erase(&mut self, key: &Slice, hash: u32) {
        let mut inner = self.inner.lock().unwrap();
        unsafe {
            let mut_ref: Pin<&mut LRUCacheInner> = Pin::as_mut(&mut inner);
            Pin::get_unchecked_mut(mut_ref).erase(key, hash)
        }
    }
    pub fn prune(&self) {
        let mut inner = self.inner.lock().unwrap();
        unsafe {
            let mut_ref: Pin<&mut LRUCacheInner> = Pin::as_mut(&mut inner);
            Pin::get_unchecked_mut(mut_ref).prune()
        }
    }
    pub fn total_charge(&self) -> usize {
        let inner = self.inner.lock().unwrap();
        inner.usage
    }
}
impl Default for LRUCache {
    fn default() -> Self {
        Self {
            inner: Mutex::new(LRUCacheInner::new()),
        }
    }
}

const NUM_SHARD_BITS: usize = 4;
const NUM_SHARDS: usize = 1 << NUM_SHARD_BITS;
struct ShardedLRUCache {
    shard: [LRUCache; NUM_SHARDS],
    last_id: Mutex<u64>,
}
impl ShardedLRUCache {
    fn new(capacity: usize) -> Self {
        let r = Self {
            shard: Default::default(),
            last_id: Default::default(),
        };
        let per_shard = (capacity + (NUM_SHARDS - 1)) / NUM_SHARDS;
        for i in 0..NUM_SHARDS {
            r.shard[i].set_capacity(per_shard);
        }
        r
    }
    fn hash_slice(s: &Slice) -> u32 {
        let s: String = (*s).into();
        let mut hasher = DefaultHasher::new();
        s.hash(&mut hasher);
        hasher.finish() as u32
    }
    fn shard(hash: u32) -> usize {
        (hash >> (32 - NUM_SHARD_BITS)) as usize
    }
}
impl Cache for ShardedLRUCache {
    fn insert(
        &mut self,
        key: &Slice,
        value: *mut u8,
        charge: usize,
        deleter: DeleterFn,
    ) -> *mut Handle {
        let hash = Self::hash_slice(key);
        self.shard[Self::shard(hash)].insert(key, hash, value, charge, deleter)
    }

    fn lookup(&mut self, key: &Slice) -> *mut Handle {
        let hash = Self::hash_slice(key);
        self.shard[Self::shard(hash)].lookup(key, hash)
    }

    fn release(&mut self, handle: *mut Handle) {
        let h = handle as *mut LRUHandle;
        unsafe { self.shard[Self::shard((*h).hash)].release(handle) }
    }

    fn value(&mut self, handle: *mut Handle) -> *mut u8 {
        let h = handle as *mut LRUHandle;
        unsafe { (*h).value }
    }

    fn erase(&mut self, key: &Slice) {
        let hash = Self::hash_slice(key);
        self.shard[Self::shard(hash)].erase(key, hash)
    }

    fn new_id(&mut self) -> u64 {
        let mut id = self.last_id.lock().unwrap();
        *id += 1;
        *id
    }

    fn prune(&mut self) {
        for i in 0..NUM_SHARDS {
            self.shard[i].prune();
        }
    }

    fn total_charge(&self) -> usize {
        let mut total = 0;
        for i in 0..NUM_SHARDS {
            total += self.shard[i].total_charge();
        }
        total
    }
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use crate::utils::coding::{decode_fixed_32, put_fixed_32};

    use super::*;

    fn encode_key(k: u32) -> String {
        let mut result = String::new();
        put_fixed_32(&mut result, k);
        result
    }
    fn decode_key(s: &Slice) -> u32 {
        assert!(s.size() == 4);
        decode_fixed_32(s.data())
    }
    fn encode_value(v: *mut u32) -> *mut u8 {
        v as *mut u8
    }
    fn decode_value(v: *mut u8) -> i32 {
        v as i32
    }
    fn deleter(key: &Slice, value: *mut u8) {
        let v = decode_value(value);
        // assert_eq!(v, v);
    }
    const CACHE_SIZE: usize = 1000;
    // const DELETED_KEYS: Arc<Mutex<Vec<u32>>> = Arc::new(Mutex::new(Vec::new()));
    // const DELETED_VALUES: Arc<Mutex<Vec<i32>>> = Arc::new(Mutex::new(Vec::new()));
    // const DELETER = move |key: &Slice, value: *mut u8| {
    //     let mut deleted_keys = DELETED_KEYS.lock().unwrap();
    //     let mut deleted_values = DELETED_VALUES.lock().unwrap();
    //     deleted_keys.push(decode_key(key));
    //     deleted_values.push(decode_value(value));
    // };
    struct CacheTest {
        // current: Box<dyn Fn(&Slice, *mut u8) -> ()>,
        deleted_keys: Arc<Mutex<Vec<u32>>>,
        deleted_values: Arc<Mutex<Vec<i32>>>,
        cache: Box<dyn Cache>,
    }
    impl CacheTest {
        fn new() -> Self {
            let deleted_keys = Arc::new(Mutex::new(Vec::new()));
            let deleted_values = Arc::new(Mutex::new(Vec::new()));
            // let deleter = move |key: &Slice, value: *mut u8| {
            //     let mut deleted_keys = deleted_keys.lock().unwrap();
            //     let mut deleted_values = deleted_values.lock().unwrap();
            //     deleted_keys.push(decode_key(key));
            //     deleted_values.push(decode_value(value));
            // };
            // let x = deleter.clone();
            Self {
                cache: new_lru_cache(CACHE_SIZE),
                // current: Box::new(deleter),
                deleted_keys,
                deleted_values,
            }
        }
        fn insert(&mut self, k: u32, v: u32, charge: usize) {
            let deleted_keys = self.deleted_keys.clone();
            let deleted_values = self.deleted_values.clone();
            let deleter = Box::new(move |key: &Slice, value: *mut u8| {
                let mut deleted_keys = deleted_keys.lock().unwrap();
                let mut deleted_values = deleted_values.lock().unwrap();
                deleted_keys.push(decode_key(key));
                deleted_values.push(decode_value(value));
            });
            let handle = self.cache.insert(
                &Slice::from_str(&encode_key(k)),
                encode_value(v as *mut u32),
                charge,
                deleter,
            );
            self.cache.release(handle);
        }
        fn insert_and_return_handle(&mut self, k: u32, v: u32, charge: usize) -> *mut Handle {
            let deleted_keys = self.deleted_keys.clone();
            let deleted_values = self.deleted_values.clone();
            let deleter: DeleterFn = Box::new(move |key: &Slice, value: *mut u8| {
                let mut deleted_keys = deleted_keys.lock().unwrap();
                let mut deleted_values = deleted_values.lock().unwrap();
                deleted_keys.push(decode_key(key));
                deleted_values.push(decode_value(value));
            });
            self.cache.insert(
                &Slice::from_str(&encode_key(k)),
                encode_value(v as *mut u32),
                charge,
                deleter,
            )
        }
        fn erase(&mut self, k: u32) {
            self.cache.erase(&Slice::from_str(&encode_key(k)));
        }
        fn lookup(&mut self, k: u32) -> i32 {
            let handle = self.cache.lookup(&Slice::from_str(&encode_key(k)));
            let r: i32 = if handle.is_null() {
                -1
            } else {
                decode_value(self.cache.value(handle))
            };
            if !handle.is_null() {
                self.cache.release(handle);
            }
            r
        }
    }

    #[test]
    fn hit_and_miss() {
        let mut test = CacheTest::new();
        assert_eq!(-1, test.lookup(100));
        test.insert(100, 101, 1);
        assert_eq!(101, test.lookup(100));
        assert_eq!(-1, test.lookup(200));
        assert_eq!(-1, test.lookup(300));
        test.insert(200, 201, 1);
        assert_eq!(101, test.lookup(100));
        assert_eq!(201, test.lookup(200));
        assert_eq!(-1, test.lookup(300));
        test.insert(100, 102, 1);
        assert_eq!(102, test.lookup(100));
        assert_eq!(201, test.lookup(200));
        assert_eq!(-1, test.lookup(300));
        assert_eq!(1, test.deleted_keys.lock().unwrap().len());
        assert_eq!(100, test.deleted_keys.lock().unwrap()[0]);
        assert_eq!(101, test.deleted_values.lock().unwrap()[0]);
    }
    #[test]
    fn erase() {
        let mut test = CacheTest::new();
        test.erase(200);
        assert_eq!(0, test.deleted_keys.lock().unwrap().len());

        test.insert(100, 101, 1);
        test.insert(200, 201, 1);
        test.erase(100);
        assert_eq!(-1, test.lookup(100));
        assert_eq!(201, test.lookup(200));
        assert_eq!(1, test.deleted_keys.lock().unwrap().len());
        assert_eq!(100, test.deleted_keys.lock().unwrap()[0]);
        assert_eq!(101, test.deleted_values.lock().unwrap()[0]);

        test.erase(100);
        assert_eq!(-1, test.lookup(100));
        assert_eq!(201, test.lookup(200));
        assert_eq!(1, test.deleted_keys.lock().unwrap().len());
    }
    #[test]
    fn entries_are_pinned() {
        let mut test = CacheTest::new();
        test.insert(100, 101, 1);
        let h1 = test.cache.lookup(&Slice::from_str(&encode_key(100)));
        assert_eq!(101, decode_value(test.cache.value(h1)));
        test.insert(100, 102, 1);
        let h2 = test.cache.lookup(&Slice::from_str(&encode_key(100)));
        assert_eq!(102, decode_value(test.cache.value(h2)));
        assert_eq!(0, test.deleted_keys.lock().unwrap().len());

        test.cache.release(h1);
        assert_eq!(1, test.deleted_keys.lock().unwrap().len());
        assert_eq!(100, test.deleted_keys.lock().unwrap()[0]);
        assert_eq!(101, test.deleted_values.lock().unwrap()[0]);
        test.erase(100);
        assert_eq!(-1, test.lookup(100));
        assert_eq!(1, test.deleted_keys.lock().unwrap().len());

        test.cache.release(h2);
        assert_eq!(2, test.deleted_keys.lock().unwrap().len());
        assert_eq!(100, test.deleted_keys.lock().unwrap()[1]);
        assert_eq!(102, test.deleted_values.lock().unwrap()[1]);
    }
    #[test]
    fn eviction_policy() {
        let mut test = CacheTest::new();
        test.insert(100, 101, 1);
        test.insert(200, 201, 1);
        test.insert(300, 301, 1);
        let h = test.cache.lookup(&Slice::from_str(&encode_key(300)));

        // increase the items to make sure eviction is triggered
        for i in 0..CACHE_SIZE + 300 {
            test.insert(1000 + i as u32, 2000 + i as u32, 1);
            assert_eq!(2000 + i as i32, test.lookup(1000 + i as u32));
            assert_eq!(101, test.lookup(100));
        }
        assert_eq!(101, test.lookup(100));
        assert_eq!(-1, test.lookup(200));
        assert_eq!(301, test.lookup(300));
        test.cache.release(h);
    }
    #[test]
    fn use_exceeds_cache_size() {
        let mut test = CacheTest::new();
        let mut h = Vec::new();
        for i in 0..CACHE_SIZE + 300 {
            h.push(test.insert_and_return_handle(1000 + i as u32, 2000 + i as u32, 1));
        }
        for i in 0..h.len() {
            assert_eq!(2000 + i as i32, test.lookup(1000 + i as u32));
        }
        for item in h {
            test.cache.release(item);
        }
    }
    #[test]
    fn heavy_entries() {
        let mut test = CacheTest::new();
        let light = 1;
        let heavy = 10;
        let mut added = 0;
        let mut index = 0;
        while added < 2 * CACHE_SIZE {
            let weight = if index & 1 != 0 { light } else { heavy };
            test.insert(index as u32, 1000 + index as u32, light);
            added += weight;
            index += 1;
        }
        let mut cached_weight = 0;
        for i in 0..index {
            let weight = if index & 1 != 0 { light } else { heavy };
            let r = test.lookup(i as u32);
            if r >= 0 {
                cached_weight += weight;
                assert_eq!(1000 + i as i32, r);
            }
        }
        assert!(cached_weight <= CACHE_SIZE + CACHE_SIZE / 10);
    }
    #[test]
    fn new_id() {
        let mut test = CacheTest::new();
        let a = test.cache.new_id();
        let b = test.cache.new_id();
        assert!(a != b);
    }
    #[test]
    fn prune() {
        let mut test = CacheTest::new();
        test.insert(1, 100, 1);
        test.insert(2, 200, 1);

        let handle = test.cache.lookup(&Slice::from_str(&encode_key(1)));
        assert!(!handle.is_null());
        test.cache.prune();
        test.cache.release(handle);
        assert_eq!(100, test.lookup(1));
        assert_eq!(-1, test.lookup(2));
    }
    #[test]
    fn zero_size_cache() {
        let mut test = CacheTest::new();
        test.cache = new_lru_cache(0);

        test.insert(1, 100, 1);
        assert_eq!(-1, test.lookup(1));
    }
}
