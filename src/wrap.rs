/*
 * Copyright (C) 2021 taylor.fish <contact@taylor.fish>
 *
 * This file is part of base116.
 *
 * base116 is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Affero General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * base116 is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Affero General Public License for more details.
 *
 * You should have received a copy of the GNU Affero General Public License
 * along with base116. If not, see <https://www.gnu.org/licenses/>.
 */

use super::iter::{BaseIterator, Flatten, InspectBaseIterator};
use super::{END_CHAR, END_UTF8, START_CHAR, START_UTF8};
use std::iter::{once, Chain, FusedIterator, Once, Take};
use std::marker::PhantomData;
use std::{array, option};

type RemoveEndWrapper<I> = RemoveEnd<I, Utf8Suffix>;

fn remove_end_wrapper<I>(iter: I) -> RemoveEndWrapper<I>
where
    I: Iterator<Item = u8>,
{
    RemoveEnd::new(iter)
}

pub type AddInputWrapper<I> = Chain<
    Chain<
        Take<array::IntoIter<u8, { START_UTF8.len() }>>,
        RemoveEndWrapper<
            Chain<Take<array::IntoIter<u8, { START_UTF8.len() }>>, I>,
        >,
    >,
    array::IntoIter<u8, { END_UTF8.len() }>,
>;

pub fn add_input_wrapper<I>(mut iter: I) -> AddInputWrapper<I>
where
    I: Iterator<Item = u8>,
{
    let mut start = [0; START_UTF8.len()];
    let count = iter
        .by_ref()
        .take(START_UTF8.len())
        .enumerate()
        .map(|(i, b)| {
            start[i] = b;
        })
        .count();

    IntoIterator::into_iter(START_UTF8)
        .take({
            // `0` if `start == START_UTF8`; otherwise `usize::MAX`
            ((start != START_UTF8) as usize).wrapping_neg()
        })
        .chain(remove_end_wrapper(
            IntoIterator::into_iter(start).take(count).chain(iter),
        ))
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

type RemoveEndCharWrapper<I> = RemoveEnd<I, CharSuffix>;

fn remove_end_char_wrapper<I>(iter: I) -> RemoveEndCharWrapper<I>
where
    I: Iterator<Item = char>,
{
    RemoveEnd::new(iter)
}

pub type AddInputCharWrapper<I> = Chain<
    Chain<
        Take<Once<char>>,
        RemoveEndCharWrapper<Chain<option::IntoIter<char>, I>>,
    >,
    Once<char>,
>;

pub fn add_input_char_wrapper<I>(mut iter: I) -> AddInputCharWrapper<I>
where
    I: Iterator<Item = char>,
{
    let first = iter.next();
    once(START_CHAR)
        .take((first != Some(START_CHAR)) as usize)
        .chain(remove_end_char_wrapper(first.into_iter().chain(iter)))
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

pub struct UnflatRemoveEnd<I, S> {
    iter: I,
    i: usize,
    phantom: PhantomData<*const S>,
}

impl<I, S> UnflatRemoveEnd<I, S> {
    pub fn new(iter: I) -> Self {
        Self {
            iter,
            i: 0,
            phantom: Default::default(),
        }
    }
}

impl<I, S, const N: usize> UnflatRemoveEnd<I, S>
where
    S: Suffix<Type = [I::Item; N]>,
    I: Iterator,
    I::Item: Copy + PartialEq,
{
    fn scan(item: I::Item, i: &mut usize) -> <Self as Iterator>::Item {
        let emit = S::suffix().get(*i) != Some(&item);
        let iter = IntoIterator::into_iter(S::suffix())
            .take(*i & (emit as usize).wrapping_neg())
            .chain(once(item).take(emit as usize));
        *i += 1;
        *i &= (!emit as usize).wrapping_neg();
        iter
    }
}

impl<I, S, const N: usize> InspectBaseIterator for UnflatRemoveEnd<I, S>
where
    S: Suffix<Type = [I::Item; N]>,
    I: Iterator + InspectBaseIterator,
    I::Item: Copy + PartialEq,
{
    type Iter = I::Iter;

    fn base_iterator(&self) -> &Self::Iter {
        self.iter.base_iterator()
    }
}

impl<I, S, const N: usize> Iterator for UnflatRemoveEnd<I, S>
where
    S: Suffix<Type = [I::Item; N]>,
    I: Iterator,
    I::Item: Copy + PartialEq,
{
    #[allow(clippy::type_complexity)]
    type Item = Chain<Take<array::IntoIter<I::Item, N>>, Take<Once<I::Item>>>;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().map(|item| Self::scan(item, &mut self.i))
    }

    fn fold<B, F>(mut self, init: B, mut f: F) -> B
    where
        F: FnMut(B, Self::Item) -> B,
    {
        let i = &mut self.i;
        self.iter.fold(init, |b, item| f(b, Self::scan(item, i)))
    }
}

pub struct RemoveEnd<I, S>(
    Flatten<
        UnflatRemoveEnd<BaseIterator<I>, S>,
        <UnflatRemoveEnd<BaseIterator<I>, S> as Iterator>::Item,
    >,
)
where
    UnflatRemoveEnd<BaseIterator<I>, S>: Iterator;

impl<I, S> RemoveEnd<I, S>
where
    UnflatRemoveEnd<BaseIterator<I>, S>: Iterator,
{
    fn new(iter: I) -> Self {
        Self(Flatten::new(UnflatRemoveEnd::new(BaseIterator(iter))))
    }
}

impl<I, S, const N: usize> Iterator for RemoveEnd<I, S>
where
    S: Suffix<Type = [I::Item; N]>,
    I: Iterator,
    I::Item: Copy + PartialEq,
{
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
        let (lower, upper) = self.0.base_iterator().size_hint();
        (lower.saturating_sub(N), upper)
    }
}

impl<I, S, const N: usize> FusedIterator for RemoveEnd<I, S>
where
    S: Suffix<Type = [I::Item; N]>,
    I: FusedIterator,
    I::Item: Copy + PartialEq,
{
}
