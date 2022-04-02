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

unsafe impl<T> Send for SkipList<T> {}
unsafe impl<T> Sync for SkipList<T> {}

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

#[cfg(test)]
mod concurrent_tests {
    use rand;
    use std::{
        collections::hash_map::DefaultHasher,
        hash::{Hash, Hasher},
        sync::{atomic::AtomicBool, Arc, Condvar, Mutex},
        thread,
    };

    use super::*;

    const K: u64 = 4;
    type Key = u64;
    struct State {
        generation: [AtomicUsize; K as usize],
    }

    impl State {
        fn new() -> Self {
            Self {
                generation: Default::default(),
            }
        }
        fn get(&self, i: usize) -> usize {
            self.generation[i].load(Ordering::Relaxed)
        }
        fn set(&self, i: usize, v: usize) {
            self.generation[i].store(v, Ordering::Relaxed);
        }
    }

    struct ConcurrentTest {
        current: State,
        // arena: Arena,
        list: SkipList<Key>,
    }

    fn key(key: Key) -> u64 {
        key >> 40
    }
    fn gen(key: Key) -> u64 {
        key >> 8 & 0xffffffff
    }
    fn hash(key: Key) -> u64 {
        key & 0xff
    }
    fn hash_number(k: u64, g: u64) -> u64 {
        let data = [k, g];
        let mut hasher = DefaultHasher::new();
        data.hash(&mut hasher);
        hasher.finish()
    }
    fn make_key(k: u64, g: u64) -> Key {
        assert!(k <= K);
        assert!(g <= 0xffffffff);
        (k << 40) | (g << 8) | (hash_number(k, g) & 0xff)
    }
    fn is_valid_key(k: Key) -> bool {
        hash(k) == (hash_number(key(k), gen(k)) & 0xff)
    }
    fn random_target(rnd: &mut Random) -> Key {
        match rnd.next() % 10 {
            0 => make_key(0, 0),
            1 => make_key(K, 0),
            _ => make_key((rnd.next() as u64 % K) as u64, 0),
        }
    }
    impl ConcurrentTest {
        fn new() -> Self {
            Self {
                current: State::new(),
                // arena: Arena::new(),
                list: SkipList::new(Arena::new()),
            }
        }
        // REQUIRES: External synchronization
        fn write_step(&mut self, rnd: &mut Random) {
            let k = rnd.next() % K as u32;
            let g = self.current.get(k as usize) + 1;
            let key = make_key(k as u64, g as u64);
            self.list.insert(key);
            self.current.set(k as usize, g);
        }
        fn read_step(&mut self, rnd: &mut Random) {
            // Remember the initial committed state of the skiplist.
            let initial_state = State::new();
            for i in 0..K as usize {
                initial_state.set(i, self.current.get(i));
            }

            let mut pos = random_target(rnd);
            let mut iter = Iter::new(&self.list);
            iter.seek(&pos);
            loop {
                let current;
                if !iter.valid() {
                    current = make_key(K, 0);
                } else {
                    current = *iter.key();
                    assert!(is_valid_key(current));
                }
                assert!(pos <= current);
                while pos < current {
                    assert!(key(pos) < K);
                    assert!(
                        (gen(pos) == 0) || (gen(pos) > initial_state.get(key(pos) as usize) as u64)
                    );
                    if key(pos) < key(current) {
                        pos = make_key(key(pos) + 1, 0);
                    } else {
                        pos = make_key(key(pos), gen(pos) + 1);
                    }
                }
                if !iter.valid() {
                    break;
                }
                if rnd.next() % 2 == 0 {
                    iter.next();
                    pos = make_key(key(pos), gen(pos) + 1);
                } else {
                    let new_target = random_target(rnd);
                    if new_target > pos {
                        pos = new_target;
                        iter.seek(&new_target);
                    }
                }
            }
        }
    }
    #[test]
    fn concurrent_without_threads() {
        let mut test = ConcurrentTest::new();
        let mut rnd = Random::new(rand::random());
        for i in 0..10000 {
            test.read_step(&mut rnd);
            test.write_step(&mut rnd);
        }
    }
    #[derive(PartialEq)]
    enum ReaderState {
        STARTING,
        RUNNING,
        DONE,
    }
    struct TestState {
        t: ConcurrentTest,
        seed: usize,
        quit_flag: AtomicBool,
        state: Arc<Mutex<ReaderState>>,
        state_cv: Condvar,
    }
    impl TestState {
        fn new(s: usize) -> Self {
            Self {
                t: ConcurrentTest::new(),
                seed: s,
                quit_flag: AtomicBool::new(false),
                state: Arc::new(Mutex::new(ReaderState::STARTING)),
                state_cv: Condvar::new(),
            }
        }
        fn wait(&self, s: ReaderState) {
            let mut locked = self.state.lock().unwrap();
            while *locked != s {
                locked = self.state_cv.wait(locked).unwrap();
            }
        }
        fn change(&self, s: ReaderState) {
            let mut locked = self.state.lock().unwrap();
            *locked = s;
            self.state_cv.notify_all();
        }
    }
    fn concurrent_reader(arg: AtomicPtr<TestState>) {
        let state = unsafe { &mut *(arg.load(Ordering::Relaxed)) };
        // let state = arg;
        let mut rnd = Random::new(state.seed as u32);
        let mut reads = 0;
        state.change(ReaderState::RUNNING);
        while !state.quit_flag.load(Ordering::Acquire) {
            state.t.read_step(&mut rnd);
            reads += 1;
        }
        state.change(ReaderState::DONE);
    }
    fn run_concurrent(run: usize) {
        let seed: usize = rand::random::<usize>() + (run * 100);
        let mut rnd = Random::new(seed as u32);
        const N: usize = 1000;
        const SIZE: usize = 1000;
        for i in 0..N {
            if i % 100 == 0 {
                eprintln!("Run {} of {}", i, N);
            }
            let mut state = TestState::new(seed + i);
            let state_ = AtomicPtr::new(&mut state as *mut _);
            let _t = thread::spawn(move || {
                concurrent_reader(state_);
            });
            state.wait(ReaderState::RUNNING);
            for _ in 0..SIZE {
                state.t.write_step(&mut rnd);
            }
            state.quit_flag.store(true, Ordering::Release);
            state.wait(ReaderState::DONE);
            _t.join().unwrap();
        }
    }
    #[test]
    fn concurrent_with_threads1() {
        run_concurrent(1);
    }
    #[test]
    fn concurrent_with_threads2() {
        run_concurrent(2);
    }
    #[test]
    fn concurrent_with_threads3() {
        run_concurrent(3);
    }
    #[test]
    fn concurrent_with_threads4() {
        run_concurrent(4);
    }
    #[test]
    fn concurrent_with_threads5() {
        run_concurrent(5);
    }
}
