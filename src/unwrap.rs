use super::{END_UTF8, START_UTF8};
use std::iter::once;

fn remove_end_wrapper<I>(iter: I) -> impl Iterator<Item = u8>
where
    I: Iterator<Item = u8>,
{
    iter.scan(0, |i, item| {
        let emit = END_UTF8.get(*i) != Some(&item);
        let iter = IntoIterator::into_iter(END_UTF8)
            .take(*i & (emit as usize).wrapping_neg())
            .chain(once(item).take(emit as usize));
        *i += !emit as usize;
        Some(iter)
    })
    .flatten()
}

pub fn add_input_wrapper<I>(mut iter: I) -> impl Iterator<Item = u8>
where
    I: Iterator<Item = u8>,
{
    let mut start = START_UTF8;
    let count = iter
        .by_ref()
        .take(START_UTF8.len())
        .enumerate()
        .map(|(i, b)| {
            start[i] = b;
        })
        .count();

    IntoIterator::into_iter(START_UTF8)
        .take(((start[..count] != START_UTF8) as usize).wrapping_neg())
        .chain(IntoIterator::into_iter(start).take(count))
        .chain(remove_end_wrapper(iter))
        .chain(IntoIterator::into_iter(END_UTF8))
}

pub fn remove_output_wrapper<I>(mut iter: I) -> impl Iterator<Item = u8>
where
    I: Iterator<Item = u8>,
{
    for _ in START_UTF8 {
        iter.next();
    }
    remove_end_wrapper(iter)
}
