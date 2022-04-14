use crate::{Slice, Status};

pub trait DbIterator {
    fn valid(&self) -> bool;
    fn key(&self) -> Slice;
    fn value(&self) -> Slice;
    fn status(&self) -> Status;
    fn seek_to_first(&mut self);
    fn seek_to_last(&mut self);
    fn seek(&mut self, target: &Slice);
    fn next(&mut self);
    fn prev(&mut self);
}

#[derive(Debug)]
struct DbIter<T: DbIterator> {
    inner: T,
}

impl<T> Iterator for DbIter<T>
where
    T: DbIterator,
{
    type Item = Slice;

    fn next(&mut self) -> Option<Self::Item> {
        todo!()
    }
}
