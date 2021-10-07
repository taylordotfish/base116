use core::cell::Cell;
use core::iter::FusedIterator;

pub trait InspectBaseIterator {
    type Iter;
    fn base_iterator(&self) -> &Self::Iter;
}

pub struct BaseIterator<I>(pub I);

impl<I> InspectBaseIterator for BaseIterator<I> {
    type Iter = I;

    fn base_iterator(&self) -> &Self::Iter {
        &self.0
    }
}

impl<I: Iterator> Iterator for BaseIterator<I> {
    type Item = I::Item;

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next()
    }

    fn fold<B, F>(self, init: B, f: F) -> B
    where
        F: FnMut(B, Self::Item) -> B,
    {
        self.0.fold(init, f)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}

impl<I: Iterator> FusedIterator for BaseIterator<I> {}

pub struct Flatten<I, Sub> {
    iter: I,
    sub: Option<Sub>,
}

impl<I, Sub> Flatten<I, Sub> {
    pub fn new(iter: I) -> Self {
        Self {
            iter,
            sub: None,
        }
    }
}

impl<I: InspectBaseIterator, Sub> InspectBaseIterator for Flatten<I, Sub> {
    type Iter = I::Iter;

    fn base_iterator(&self) -> &Self::Iter {
        self.iter.base_iterator()
    }
}

impl<I, Sub: Iterator> Iterator for Flatten<I, Sub>
where
    I: Iterator<Item = Sub>,
{
    type Item = Sub::Item;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(sub) = &mut self.sub {
            if let Some(item) = sub.next() {
                return Some(item);
            }
        }
        for mut sub in &mut self.iter {
            if let Some(item) = sub.next() {
                self.sub = Some(sub);
                return Some(item);
            }
        }
        self.sub = None;
        None
    }

    fn fold<B, F>(self, init: B, mut f: F) -> B
    where
        F: FnMut(B, Self::Item) -> B,
    {
        self.iter.fold(init, |b, item| item.fold(b, &mut f))
    }
}

impl<I, Sub: Iterator> FusedIterator for Flatten<I, Sub> where
    I: Iterator<Item = Sub>
{
}

/// Turns an iterator of `Result<T, E>` into an iterator of `T` while allowing
/// any errors to be fetched with [`Self::take_err`].
pub struct ErrAdapter<I, Err> {
    iter: I,
    err: Cell<Option<Err>>,
}

impl<I, Err> ErrAdapter<I, Err> {
    pub fn new(iter: I) -> Self {
        Self {
            iter,
            err: Cell::new(None),
        }
    }

    pub fn take_err(&self) -> Option<Err> {
        self.err.take()
    }
}

impl<I: InspectBaseIterator, Err> InspectBaseIterator for ErrAdapter<I, Err> {
    type Iter = I::Iter;

    fn base_iterator(&self) -> &Self::Iter {
        self.iter.base_iterator()
    }
}

impl<I, Err, T> Iterator for ErrAdapter<I, Err>
where
    I: Iterator<Item = Result<T, Err>>,
{
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next()?.map_or_else(
            |e| {
                self.err.set(Some(e));
                None
            },
            Some,
        )
    }
}

impl<I, Err, T> FusedIterator for ErrAdapter<I, Err> where
    I: Iterator<Item = Result<T, Err>>
{
}
