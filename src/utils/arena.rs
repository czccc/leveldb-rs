use std::{
    alloc::{alloc, dealloc, Layout},
    mem, ptr,
    sync::atomic::{AtomicUsize, Ordering},
};

const BLOCK_SIZE: usize = 4096;

pub struct Arena {
    blocks: Vec<(*mut u8, Layout)>,
    alloc_ptr: *mut u8,
    alloc_bytes_remaining: usize,
    memory_usage: AtomicUsize,
}

impl Arena {
    #[must_use]
    pub fn new() -> Self {
        Self {
            blocks: Vec::new(),
            alloc_ptr: ptr::null_mut(),
            alloc_bytes_remaining: 0,
            memory_usage: AtomicUsize::new(0),
        }
    }
    #[inline]
    pub fn alloc(&mut self, bytes: usize) -> *mut u8 {
        assert!(bytes > 0);
        if bytes > self.alloc_bytes_remaining {
            self.alloc_fallback(bytes)
        } else {
            let ptr = self.alloc_ptr;
            self.alloc_ptr = unsafe { self.alloc_ptr.add(bytes) };
            self.alloc_bytes_remaining -= bytes;
            ptr
        }
    }
    #[inline]
    pub fn alloc_aligned(&mut self, bytes: usize) -> *mut u8 {
        assert!(bytes > 0);
        let align = mem::align_of::<*mut u8>();
        assert!(
            (align) & (align - 1) == 0,
            "Pointer size should be a power of 2"
        );
        let offset = self.alloc_ptr.align_offset(align);
        let needed = bytes + offset;
        if needed > self.alloc_bytes_remaining {
            self.alloc_fallback(bytes)
        } else {
            let ptr = unsafe { self.alloc_ptr.add(offset) };
            self.alloc_ptr = unsafe { self.alloc_ptr.add(needed) };
            self.alloc_bytes_remaining -= needed;
            ptr
        }
    }

    /// Get a reference to the arena's memory usage.
    #[must_use]
    fn memory_usage(&self) -> usize {
        self.memory_usage.load(Ordering::Relaxed)
    }
}

impl Arena {
    fn alloc_fallback(&mut self, bytes: usize) -> *mut u8 {
        if bytes > BLOCK_SIZE / 4 {
            self.alloc_new_block(bytes)
        } else {
            self.alloc_ptr = self.alloc_new_block(BLOCK_SIZE);
            self.alloc_bytes_remaining = BLOCK_SIZE;

            let ptr = self.alloc_ptr;
            self.alloc_ptr = unsafe { self.alloc_ptr.add(bytes) };
            self.alloc_bytes_remaining -= bytes;
            ptr
        }
    }
    fn alloc_new_block(&mut self, block_bytes: usize) -> *mut u8 {
        let align = mem::align_of::<*mut u8>();
        let layout = Layout::from_size_align(block_bytes, align).unwrap_or_else(|_| {
            panic!(
                "Layout::from_size_align failed for block_bytes={}, align={}",
                block_bytes, align
            )
        });
        let ptr = unsafe { alloc(layout) };
        self.blocks.push((ptr, layout));
        self.memory_usage.fetch_add(
            block_bytes + mem::size_of::<(*mut u8, Layout)>(),
            Ordering::Relaxed,
        );
        ptr
    }
}

impl Drop for Arena {
    fn drop(&mut self) {
        for (block, layout) in self.blocks.drain(..) {
            unsafe {
                dealloc(block, layout);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::utils::Random;

    #[test]
    fn arena_empty() {
        let mut _arena = Arena::new();
    }

    #[test]
    fn arena_simple() {
        const N: usize = 100000;
        let mut bytes: usize = 0;
        let mut allocated = Vec::new();
        let mut arena = Arena::new();
        let mut rnd = Random::new(301);

        for i in 0..N {
            let mut s: usize;
            if i % (N / 10) == 0 {
                s = i;
            } else {
                s = match rnd.one_in(4000) {
                    true => rnd.uniform(6000),
                    false => match rnd.one_in(10) {
                        true => rnd.uniform(100),
                        false => rnd.uniform(20),
                    },
                } as usize;
            }
            if s == 0 {
                s = 1;
            }
            let r;
            match rnd.one_in(10) {
                true => r = arena.alloc_aligned(s),
                false => r = arena.alloc(s),
            }
            for b in 0..s {
                unsafe { r.add(b).write((i % 256) as u8) };
            }
            bytes += s;
            allocated.push((s, r));
            assert!(arena.memory_usage() >= bytes);
            if i > N / 10 {
                assert!(arena.memory_usage() as f32 <= (bytes as f32) * 1.1);
            }
        }
        for i in 0..allocated.len() {
            let (num_bytes, p) = allocated[i];
            for b in 0..num_bytes {
                assert_eq!(unsafe { p.add(b).read() }, (i % 256) as u8);
            }
        }
    }

    #[test]
    fn arena_align() {
        let mut arena = Arena::new();
        let p1 = arena.alloc(30);
        assert_eq!(p1.align_offset(mem::align_of::<*mut u8>()), 0);
        let p1 = arena.alloc(30);
        assert_eq!(p1.align_offset(mem::align_of::<*mut u8>()), 2);
        let p1 = arena.alloc_aligned(30);
        assert_eq!(p1.align_offset(mem::align_of::<*mut u8>()), 0);
        assert_eq!(
            arena.memory_usage(),
            BLOCK_SIZE + mem::size_of::<(*mut u8, Layout)>()
        );

        let p1 = arena.alloc(BLOCK_SIZE);
        assert_eq!(p1.align_offset(mem::align_of::<*mut u8>()), 0);
        assert_eq!(
            arena.memory_usage(),
            2 * (BLOCK_SIZE + mem::size_of::<(*mut u8, Layout)>())
        );

        let p1 = arena.alloc(BLOCK_SIZE - 10);
        assert_eq!(p1.align_offset(mem::align_of::<*mut u8>()), 0);
        assert_eq!(
            arena.memory_usage(),
            3 * (BLOCK_SIZE + mem::size_of::<(*mut u8, Layout)>()) - 10
        );
    }
}
