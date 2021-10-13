use super::{END_CHAR, END_UTF8, START_CHAR, START_UTF8};
use std::iter::once;

fn remove_end_wrapper<I>(iter: I) -> impl Iterator<Item = u8>
where
    I: Iterator<Item = u8>,
{
    iter.scan(0, |i, item| {
        let emit = END_UTF8.get(*i) != Some(&item);
        let iter = IntoIterator::into_iter(END_UTF8)
            .take({
                // `*i` if `emit`; otherwise 0
                *i & (emit as usize).wrapping_neg()
            })
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

pub fn remove_output_wrapper<I>(mut iter: I) -> impl Iterator<Item = u8>
where
    I: Iterator<Item = u8>,
{
    for _ in START_UTF8 {
        iter.next();
    }
    remove_end_wrapper(iter)
}

pub fn remove_end_char_wrapper<I>(iter: I) -> impl Iterator<Item = char>
where
    I: Iterator<Item = char>,
{
    iter.scan(false, |end_pending, item| {
        let is_end = item == END_CHAR;
        let iter = IntoIterator::into_iter([item, END_CHAR])
            .take(*end_pending as usize + !is_end as usize);
        *end_pending = is_end;
        Some(iter)
    })
    .flatten()
}

pub fn add_input_char_wrapper<I>(mut iter: I) -> impl Iterator<Item = char>
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

pub fn remove_output_char_wrapper<I: Iterator<Item = char>>(
    mut iter: I,
) -> impl Iterator<Item = char> {
    iter.next();
    remove_end_char_wrapper(iter)
}
