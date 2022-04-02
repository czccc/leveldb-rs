#![allow(dead_code, unused_variables)]

mod skiplist;
mod slice;
mod status;
mod utils;

use slice::Slice;

#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {
        let result = 2 + 2;
        assert_eq!(result, 4);
    }
}
