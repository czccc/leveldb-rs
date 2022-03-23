use std::{
    ops::Index,
    ptr,
    sync::atomic::{AtomicPtr, AtomicUsize, Ordering},
};

use crate::utils::{Arena, Random};

const MAX_HEIGHT: usize = 12;

#[repr(C)]
struct Tower<Key> {
    pointers: [AtomicPtr<Node<Key>>; 1],
}

impl<Key> Index<usize> for Tower<Key> {
    type Output = AtomicPtr<Node<Key>>;
    fn index(&self, index: usize) -> &AtomicPtr<Node<Key>> {
        unsafe { self.pointers.get_unchecked(index) }
    }
}

#[repr(C)]
struct Node<Key> {
    pub key: Key,
    next: Tower<Key>,
}

impl<Key> Node<Key> {
    fn next(&self, level: usize) -> *mut Node<Key> {
        assert!(level < MAX_HEIGHT);
        self.next[level].load(Ordering::Acquire)
    }
    fn set_next(&self, level: usize, next: *mut Node<Key>) {
        assert!(level < MAX_HEIGHT);
        self.next[level].store(next, Ordering::Release);
    }
    fn no_barrier_next(&self, level: usize) -> *mut Node<Key> {
        assert!(level < MAX_HEIGHT);
        self.next[level].load(Ordering::Relaxed)
    }
    fn no_barrier_set_next(&self, level: usize, next: *mut Node<Key>) {
        assert!(level < MAX_HEIGHT);
        self.next[level].store(next, Ordering::Relaxed);
    }
}

pub struct SkipList<Key> {
    head: *mut Node<Key>,
    max_height: AtomicUsize,
    rand: Random,
    arena: Arena,
}

impl<Key> SkipList<Key>
where
    Key: Ord,
{
    pub fn new(arena: Arena) -> Self {
        let mut list = Self {
            head: ptr::null_mut(),
            max_height: AtomicUsize::new(1),
            rand: Random::new(0xdeadbeef),
            arena,
        };
        list.head = list.new_head();
        list
    }
    pub fn insert(&mut self, key: Key) {
        let mut prev = [ptr::null_mut(); MAX_HEIGHT];
        let x = self.find_greater_or_equal(&key, &mut prev);
        assert!(x.is_null() || !self.equal(&key, &unsafe { &*x }.key));
        let height = self.random_height();
        if height > self.get_max_height() {
            for p in prev.iter_mut().take(height).skip(self.get_max_height()) {
                *p = self.head;
            }
            self.max_height.store(height, Ordering::Relaxed);
        }
        let x = self.new_node(key, height);
        for (i, p) in prev.into_iter().enumerate().take(height) {
            assert!(!p.is_null());
            unsafe {
                (*x).no_barrier_set_next(i, (*p).no_barrier_next(i));
                (*p).set_next(i, x)
            }
        }
    }
    pub fn contains(&self, key: &Key) -> bool {
        let x = self.find_greater_or_equal(key, ptr::null_mut());
        !x.is_null() && self.equal(key, &unsafe { &*x }.key)
    }
}

impl<Key> SkipList<Key>
where
    Key: Ord,
{
    fn new_head(&mut self) -> *mut Node<Key> {
        unsafe {
            let node_size = std::mem::size_of::<Node<Key>>();
            let ptr_size = std::mem::size_of::<AtomicPtr<Node<Key>>>();
            let p = self
                .arena
                .alloc_aligned(node_size + ptr_size * (MAX_HEIGHT - 1))
                as *mut Node<Key>;
            ptr::write_bytes(&mut (*p).key, 0, 1);
            ptr::write_bytes((*p).next.pointers.as_mut_ptr(), 0, MAX_HEIGHT);
            p
        }
    }
    fn new_node(&mut self, key: Key, height: usize) -> *mut Node<Key> {
        unsafe {
            let node_size = std::mem::size_of::<Node<Key>>();
            let ptr_size = std::mem::size_of::<AtomicPtr<Node<Key>>>();
            let p = self
                .arena
                .alloc_aligned(node_size + ptr_size * (height - 1))
                as *mut Node<Key>;
            ptr::write(&mut (*p).key, key);
            ptr::write_bytes((*p).next.pointers.as_mut_ptr(), 0, height);
            p
        }
    }
    fn random_height(&mut self) -> usize {
        const BRANCHING_FACTOR: usize = 4;
        let mut height = 1;
        while height < MAX_HEIGHT && self.rand.one_in(BRANCHING_FACTOR as u32) {
            height += 1;
        }
        assert!(height > 0);
        assert!(height <= MAX_HEIGHT);
        height
    }
    fn get_max_height(&self) -> usize {
        self.max_height.load(Ordering::Relaxed)
    }
    fn equal(&self, a: &Key, b: &Key) -> bool {
        a == b
    }
    fn key_is_after_node(&self, key: &Key, n: *mut Node<Key>) -> bool {
        !n.is_null() && (unsafe { &*n }).key.lt(key)
    }
    fn find_greater_or_equal(
        &self,
        key: &Key,
        prev: *mut [*mut Node<Key>; MAX_HEIGHT],
    ) -> *mut Node<Key> {
        let mut x = self.head;
        let mut level = self.get_max_height() - 1;
        loop {
            let next = unsafe { (*x).next(level) };
            if self.key_is_after_node(key, next) {
                x = next;
            } else {
                if !prev.is_null() {
                    unsafe {
                        (*prev)[level] = x;
                    }
                }
                if level == 0 {
                    return next;
                } else {
                    level -= 1;
                }
            }
        }
    }
    fn find_less_than(&self, key: &Key) -> *mut Node<Key> {
        let mut x = self.head;
        let mut level = self.get_max_height() - 1;
        loop {
            assert!(x == self.head || unsafe { &*x }.key.lt(key));
            let next = unsafe { (*x).next(level) };
            if next.is_null() || unsafe { &*next }.key.ge(key) {
                if level == 0 {
                    return x;
                } else {
                    level -= 1;
                }
            } else {
                x = next;
            }
        }
    }
    fn find_last(&self) -> *mut Node<Key> {
        let mut x = self.head;
        let mut level = self.get_max_height() - 1;
        loop {
            let next = unsafe { (*x).next(level) };
            if next.is_null() {
                if level == 0 {
                    return x;
                } else {
                    level -= 1;
                }
            } else {
                x = next;
            }
        }
    }
}

impl<Key> Drop for SkipList<Key> {
    fn drop(&mut self) {
        let mut node = self.head;
        while !node.is_null() {
            unsafe {
                ptr::drop_in_place(&mut (*node).key);
                node = (*node).next(0);
            }
        }
    }
}

pub struct Iter<'a, Key>
where
    Key: Ord,
{
    list: &'a SkipList<Key>,
    node: *mut Node<Key>,
}

impl<'a, Key> Iter<'a, Key>
where
    Key: Ord,
{
    pub fn new(list: &'a SkipList<Key>) -> Self {
        Self {
            list,
            node: ptr::null_mut(),
        }
    }
    pub fn valid(&self) -> bool {
        !self.node.is_null()
    }
    pub fn key(&self) -> &Key {
        assert!(self.valid());
        unsafe { &(*self.node).key }
    }
    pub fn next(&mut self) {
        assert!(self.valid());
        self.node = unsafe { (*self.node).next(0) };
    }
    pub fn prev(&mut self) {
        assert!(self.valid());
        self.node = self.list.find_less_than(unsafe { &(*self.node).key });
        if std::ptr::eq(self.node, self.list.head) {
            self.node = ptr::null_mut();
        }
    }
    pub fn seek(&mut self, target: &Key) {
        self.node = self.list.find_greater_or_equal(target, ptr::null_mut());
    }
    pub fn seek_to_first(&mut self) {
        self.node = unsafe { &*self.list.head }.next(0);
    }
    pub fn seek_to_last(&mut self) {
        self.node = self.list.find_last();
        if std::ptr::eq(self.node, self.list.head) {
            self.node = ptr::null_mut();
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn list_node() {
        let arena = Arena::new();
        let mut list = SkipList::new(arena);
        let node1 = list.new_node(String::from("node1"), MAX_HEIGHT);
        let node2 = list.new_node(String::from("node2"), MAX_HEIGHT);
        let node3 = list.new_node(String::from("node3"), MAX_HEIGHT);
        // let node1 = list.new_node("node1", MAX_HEIGHT);
        // let node2 = list.new_node("node2", MAX_HEIGHT);
        // let node3 = list.new_node("node3", MAX_HEIGHT);
        // let node1 = list.new_node(1, MAX_HEIGHT);
        // let node2 = list.new_node(2, MAX_HEIGHT);
        // let node3 = list.new_node(2, MAX_HEIGHT);
        for i in 0..MAX_HEIGHT {
            assert_eq!(unsafe { &*node1 }.next(i), ptr::null_mut());
            assert_eq!(unsafe { &*node2 }.next(i), ptr::null_mut());
            assert_eq!(unsafe { &*node3 }.next(i), ptr::null_mut());
        }
        for i in 0..(MAX_HEIGHT / 2) {
            unsafe { &*node1 }.set_next(i, node2);
            unsafe { &*node2 }.set_next(i, node3);
        }
        for i in (MAX_HEIGHT / 2)..MAX_HEIGHT {
            unsafe { &*node1 }.set_next(i, node3);
        }
        for i in 0..(MAX_HEIGHT / 2) {
            assert!(unsafe { &*node1 }.next(i) == node2);
            assert!(unsafe { &*node2 }.next(i) == node3);
        }
        for i in (MAX_HEIGHT / 2)..MAX_HEIGHT {
            assert!(unsafe { &*node1 }.next(i) == node3);
            assert!(unsafe { &*node2 }.next(i) == ptr::null_mut());
        }
        unsafe {
            ptr::drop_in_place(&mut (*node1).key);
            ptr::drop_in_place(&mut (*node2).key);
            ptr::drop_in_place(&mut (*node3).key);
        }
    }

    #[test]
    fn list_empty() {
        let arena = Arena::new();
        let list = SkipList::new(arena);
        assert!(!list.contains(&10));

        let mut iter = Iter::new(&list);
        assert!(!iter.valid());
        iter.seek_to_first();
        assert!(!iter.valid());
        iter.seek(&100);
        assert!(!iter.valid());
        iter.seek_to_last();
        assert!(!iter.valid());
    }
    #[test]
    fn list_insert_and_lookup() {
        const N: u32 = 2000;
        const R: u32 = 5000;
        let mut rnd = Random::new(1000);
        let mut keys = std::collections::HashSet::new();
        let arena = Arena::new();
        let mut list = SkipList::new(arena);
        assert!(!list.contains(&10));
        for i in 0..N {
            let key = rnd.next() % R;
            if !keys.contains(&key) {
                keys.insert(key);
                list.insert(key);
            }
        }
        let mut keys = keys.into_iter().collect::<Vec<u32>>();
        keys.sort();

        for i in 0..R {
            if list.contains(&i) {
                assert!(keys.contains(&i));
            } else {
                assert!(!keys.contains(&i));
            }
        }
        {
            let mut iter = Iter::new(&list);
            assert!(!iter.valid());
            iter.seek(&0);
            assert!(iter.valid());
            assert!(iter.key() == keys.iter().nth(0).unwrap());
            iter.seek_to_first();
            assert!(iter.valid());
            assert!(iter.key() == keys.iter().nth(0).unwrap());
            iter.seek_to_last();
            assert!(iter.valid());
            assert!(iter.key() == keys.iter().last().unwrap());
        }
        for i in 0..R {
            let mut iter = Iter::new(&list);
            iter.seek(&i);
            let mut model_iter = keys.iter().skip_while(|k| **k < i);
            for j in 0..3 {
                match model_iter.next() {
                    Some(k) => {
                        assert!(iter.valid());
                        assert_eq!(iter.key(), k);
                        iter.next();
                    }
                    None => {
                        assert!(!iter.valid());
                        break;
                    }
                }
            }
        }
        {
            let mut iter = Iter::new(&list);
            iter.seek_to_last();
            for k in keys.iter().collect::<Vec<&u32>>().iter().rev() {
                assert!(iter.valid());
                assert_eq!(iter.key(), *k);
                iter.prev();
            }
        }
    }
    #[test]
    fn list_string() {
        const N: u32 = 2000;
        const R: u32 = 5000;
        let mut rnd = Random::new(1000);
        let mut keys = std::collections::HashSet::new();
        let arena = Arena::new();
        let mut list = SkipList::new(arena);
        assert!(!list.contains(&String::from("10")));
        for i in 0..N {
            let key = rnd.next() % R;
            if !keys.contains(&key) {
                keys.insert(key);
                list.insert(format!("{:06}", key));
            }
        }
        let mut keys = keys.into_iter().collect::<Vec<u32>>();
        keys.sort();

        for i in 0..R {
            if list.contains(&format!("{:06}", i)) {
                assert!(keys.contains(&i));
            } else {
                assert!(!keys.contains(&i));
            }
        }
        {
            let mut iter = Iter::new(&list);
            assert!(!iter.valid());
            iter.seek(&format!("{:06}", 0));
            assert!(iter.valid());
            assert!(iter.key() == &format!("{:06}", keys.iter().nth(0).unwrap()));
            iter.seek_to_first();
            assert!(iter.valid());
            assert!(iter.key() == &format!("{:06}", keys.iter().nth(0).unwrap()));
            iter.seek_to_last();
            assert!(iter.valid());
            assert!(iter.key() == &format!("{:06}", keys.iter().last().unwrap()));
        }
        for i in 0..R {
            let mut iter = Iter::new(&list);
            iter.seek(&format!("{:06}", i));
            let mut model_iter = keys.iter().skip_while(|k| **k < i);
            for j in 0..3 {
                match model_iter.next() {
                    Some(k) => {
                        assert!(iter.valid());
                        assert_eq!(iter.key(), &format!("{:06}", k));
                        iter.next();
                    }
                    None => {
                        assert!(!iter.valid());
                        break;
                    }
                }
            }
        }
        {
            let mut iter = Iter::new(&list);
            iter.seek_to_last();
            for k in keys.iter().collect::<Vec<&u32>>().iter().rev() {
                assert!(iter.valid());
                assert_eq!(iter.key(), &format!("{:06}", *k));
                iter.prev();
            }
        }
    }
}
