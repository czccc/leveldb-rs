use std::{cmp::Ordering, ops::Index, slice};

#[derive(Copy, Clone)]
pub struct Slice {
    data: *const u8,
    size: usize,
}

impl Slice {
    pub fn new(data: *const u8, size: usize) -> Self {
        Self { data, size }
    }
    pub fn from_str(s: &str) -> Self {
        Self {
            data: s.as_ptr(),
            size: s.len(),
        }
    }
    pub fn data(&self) -> *const u8 {
        self.data
    }
    pub fn size(&self) -> usize {
        self.size
    }
    pub fn empty(&self) -> bool {
        self.size == 0
    }
    pub fn clear(&mut self) {
        self.data = "".as_ptr();
        self.size = 0;
    }
    pub fn remove_prefix(&mut self, n: usize) {
        assert!(n <= self.size());
        self.data = unsafe { self.data.add(n) };
        self.size -= n;
    }
    pub fn starts_with(&self, x: &Self) -> bool {
        (self.size >= x.size) && {
            for i in 0..x.size {
                if self[i] != x[i] {
                    return false;
                }
            }
            true
        }
    }
    pub fn compare(&self, x: &Self) -> isize {
        match self.cmp(x) {
            Ordering::Less => -1,
            Ordering::Equal => 0,
            Ordering::Greater => 1,
        }
    }
}
impl Default for Slice {
    fn default() -> Self {
        Self {
            data: "".as_ptr(),
            size: 0,
        }
    }
}
impl From<Slice> for Vec<u8> {
    fn from(val: Slice) -> Self {
        unsafe { slice::from_raw_parts(val.data, val.size).to_owned() }
    }
}
impl From<Slice> for String {
    fn from(val: Slice) -> Self {
        unsafe { String::from_utf8_unchecked(val.into()) }
    }
}
impl Index<usize> for Slice {
    type Output = u8;

    fn index(&self, index: usize) -> &Self::Output {
        assert!(index < self.size());
        unsafe { &*self.data.add(index) }
    }
}
impl PartialEq for Slice {
    fn eq(&self, other: &Self) -> bool {
        (self.size == other.size) && {
            for i in 0..other.size {
                if self[i] != other[i] {
                    return false;
                }
            }
            true
        }
    }
}
impl Eq for Slice {}
impl PartialOrd for Slice {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        let min_len = if self.size < other.size {
            self.size
        } else {
            other.size
        };
        let mut r = Ordering::Equal;
        for i in 0..min_len {
            match self[i].cmp(&other[i]) {
                Ordering::Less => r = Ordering::Less,
                Ordering::Equal => continue,
                Ordering::Greater => r = Ordering::Greater,
            };
        }
        if r == Ordering::Equal {
            Some(self.size.cmp(&other.size))
        } else {
            Some(r)
        }
    }
}
impl Ord for Slice {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.partial_cmp(other).unwrap()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn slice() {
        let raw = "abc123";
        let raw1 = "abb123";

        let s = Slice::default();
        let s1 = Slice::default();
        // assert!(s.data() == "".as_ptr());
        assert!(s.size() == 0);
        assert!(s == s1);
        assert!(s.compare(&s1) == 0);

        let s = Slice::new(raw.as_ptr(), 6);
        let s1 = Slice::new(raw.as_ptr(), 6);
        assert!(s.data() == raw.as_ptr());
        assert!(s.size() == 6);
        let st: String = s.into();
        assert!(st == raw);
        assert!(s == s1);

        let s = Slice::new(raw.as_ptr(), 4);
        assert!(s.data() == raw.as_ptr());
        assert!(s.size() == 4);
        let st: String = s.into();
        assert!(st == raw[..4]);
        let s1 = Slice::new(raw1.as_ptr(), 4);
        assert!(s1.data() == raw1.as_ptr());
        assert!(s1.size() == 4);
        let st: String = s1.into();
        assert!(st == raw1[..4]);
        assert!(s1 < s);
        assert!(s.compare(&s1) == 1);

        let s = Slice::from_str(raw);
        let st: String = s.into();
        assert!(st == raw);
    }
}
