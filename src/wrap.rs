use super::{END_CHAR, END_UTF8, START_CHAR, START_UTF8};
use std::array;
use std::iter::{once, Chain, Flatten, Once, Skip, Take};
use std::marker::PhantomData;

type RemoveEndWrapper<I> = Flatten<RemoveEnd<I, Utf8Suffix>>;

fn remove_end_wrapper<I>(iter: I) -> RemoveEndWrapper<I>
where
    I: Iterator<Item = u8>,
{
    RemoveEnd::new(iter, Utf8Suffix).flatten()
}

pub type AddInputWrapper<I> = Chain<
    Chain<
        Chain<
            Skip<Take<array::IntoIter<u8, { START_UTF8.len() }>>>,
            Take<array::IntoIter<u8, { START_UTF8.len() * 2 }>>,
        >,
        RemoveEndWrapper<I>,
    >,
    array::IntoIter<u8, { END_UTF8.len() }>,
>;

pub fn add_input_wrapper<I>(mut iter: I) -> AddInputWrapper<I>
where
    I: Iterator<Item = u8>,
{
    let mut start = [0; START_UTF8.len() * 2];
    start[..START_UTF8.len()].copy_from_slice(&START_UTF8);
    let count = iter
        .by_ref()
        .take(START_UTF8.len())
        .enumerate()
        .map(|(i, b)| {
            start[START_UTF8.len() + i] = b;
        })
        .count();

    IntoIterator::into_iter(START_UTF8)
        .take(START_UTF8.len() + count)
        .skip({
            // `START_UTF8.len()` if start was present in `iter`; otherwise 0
            START_UTF8.len()
                & ((start[..count] == START_UTF8) as usize).wrapping_neg()
        })
        .chain(IntoIterator::into_iter(start).take(count))
        .chain(remove_end_wrapper(iter))
        .chain(IntoIterator::into_iter(END_UTF8))
}

pub type RemoveOutputWrapper<I> = RemoveEndWrapper<I>;

pub fn remove_output_wrapper<I>(mut iter: I) -> RemoveOutputWrapper<I>
where
    I: Iterator<Item = u8>,
{
    for _ in START_UTF8 {
        iter.next();
    }
    remove_end_wrapper(iter)
}

type RemoveEndCharWrapper<I> = Flatten<RemoveEnd<I, CharSuffix>>;

fn remove_end_char_wrapper<I>(iter: I) -> RemoveEndCharWrapper<I>
where
    I: Iterator<Item = char>,
{
    RemoveEnd::new(iter, CharSuffix).flatten()
}

pub type AddInputCharWrapper<I> = Chain<
    Chain<Skip<Take<array::IntoIter<char, 2>>>, RemoveEndCharWrapper<I>>,
    Once<char>,
>;

pub fn add_input_char_wrapper<I>(mut iter: I) -> AddInputCharWrapper<I>
where
    I: Iterator<Item = char>,
{
    let first = iter.next();
    IntoIterator::into_iter([START_CHAR, first.unwrap_or('\0')])
        .take(1 + first.is_some() as usize)
        .skip((first == Some(START_CHAR)) as usize)
        .chain(remove_end_char_wrapper(iter))
        .chain(once(END_CHAR))
}

pub type RemoveOutputCharWrapper<I> = RemoveEndCharWrapper<I>;

pub fn remove_output_char_wrapper<I: Iterator<Item = char>>(
    mut iter: I,
) -> RemoveOutputCharWrapper<I> {
    iter.next();
    remove_end_char_wrapper(iter)
}

pub trait Suffix {
    type Type;
    fn suffix() -> Self::Type;
}

pub struct Utf8Suffix;
pub struct CharSuffix;

impl Suffix for CharSuffix {
    type Type = [char; 1];

    fn suffix() -> Self::Type {
        [END_CHAR]
    }
}

impl Suffix for Utf8Suffix {
    type Type = [u8; END_UTF8.len()];

    fn suffix() -> Self::Type {
        END_UTF8
    }
}

pub struct RemoveEnd<I, S> {
    iter: I,
    i: usize,
    phantom: PhantomData<*const S>,
}

impl<I, S> RemoveEnd<I, S> {
    fn new(iter: I, _: S) -> Self {
        Self {
            iter,
            i: 0,
            phantom: Default::default(),
        }
    }
}

impl<I, S, const N: usize> Iterator for RemoveEnd<I, S>
where
    S: Suffix<Type = [I::Item; N]>,
    I: Iterator,
    I::Item: Copy + PartialEq,
{
    #[allow(clippy::type_complexity)]
    type Item = Chain<Take<array::IntoIter<I::Item, N>>, Take<Once<I::Item>>>;

    fn next(&mut self) -> Option<Self::Item> {
        let item = self.iter.next()?;
        let emit = S::suffix().get(self.i) == Some(&item);
        let iter = IntoIterator::into_iter(S::suffix())
            .take(self.i & (emit as usize).wrapping_neg())
            .chain(once(item).take(emit as usize));
        self.i += !emit as usize;
        Some(iter)
    }
}
