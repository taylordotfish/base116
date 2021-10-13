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

use super::iter::{BaseIterator, ErrAdapter, Flatten, InspectBaseIterator};
use super::ranges::{self, RANGES1, RANGES2, RANGES3};
use super::wrap::{add_input_char_wrapper, add_input_wrapper};
use super::wrap::{AddInputCharWrapper, AddInputWrapper};
use super::Digit;
use super::{BYTES_PER_CHUNK, DIGITS_PER_CHUNK, END_CHAR, START_CHAR};
use super::{L1_MULT, L2_MULT};

use core::array;
use core::convert::TryFrom;
use core::fmt::{self, Debug, Display, Formatter};
use core::iter::{FusedIterator, Take};
use core::str::Chars;

#[non_exhaustive]
#[derive(Debug)]
pub enum DecodeError {
    BadChar(char),
    BadLength,
    MissingStart,
    MissingEnd,
    TrailingData(char),
}

pub type DecodeResult<T> = Result<T, DecodeError>;
pub type DecodeBytesResult<T> = Result<T, DecodeBytesError>;
use DecodeError as Error;

impl fmt::Display for DecodeError {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        match self {
            Self::BadChar(c) => write!(f, "bad character: {}", c),
            Self::BadLength => write!(f, "bad input length"),
            Self::MissingStart => {
                write!(f, "missing start character ({})", START_CHAR)
            }
            Self::MissingEnd => {
                write!(f, "missing end character ({})", END_CHAR)
            }
            Self::TrailingData(c) => {
                write!(f, "unexpected data ({:?}) after end character", c)
            }
        }
    }
}

#[cfg(feature = "std")]
#[cfg_attr(feature = "doc_cfg", doc(cfg(feature = "std")))]
impl std::error::Error for DecodeError {}

pub struct InvalidUtf8 {
    bytes: [u8; 4],
    len: u8,
}

impl InvalidUtf8 {
    pub fn bytes(&self) -> &[u8] {
        &self.bytes[..usize::from(self.len)]
    }
}

impl Debug for InvalidUtf8 {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        f.debug_tuple("InvalidUtf8").field(&self.bytes()).finish()
    }
}

impl Display for InvalidUtf8 {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "invalid UTF-8: {:?}", self.bytes())
    }
}

#[cfg(feature = "std")]
#[cfg_attr(feature = "doc_cfg", doc(cfg(feature = "std")))]
impl std::error::Error for InvalidUtf8 {}

#[derive(Debug)]
pub enum DecodeBytesError {
    InvalidUtf8(InvalidUtf8),
    DecodeError(DecodeError),
}

impl fmt::Display for DecodeBytesError {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        match self {
            Self::InvalidUtf8(e) => write!(f, "{}", e),
            Self::DecodeError(e) => write!(f, "{}", e),
        }
    }
}

#[cfg(feature = "std")]
#[cfg_attr(feature = "doc_cfg", doc(cfg(feature = "std")))]
impl std::error::Error for DecodeBytesError {}

enum UnwrapStringState {
    Init,
    Running,
    Done,
}

struct UnwrapString<I> {
    iter: I,
    state: UnwrapStringState,
}

impl<I> UnwrapString<I> {
    pub fn new(iter: I) -> Self {
        Self {
            iter,
            state: UnwrapStringState::Init,
        }
    }
}

impl<I: InspectBaseIterator> InspectBaseIterator for UnwrapString<I> {
    type Iter = I::Iter;

    fn base_iterator(&self) -> &Self::Iter {
        self.iter.base_iterator()
    }
}

impl<I> Iterator for UnwrapString<I>
where
    I: Iterator<Item = char>,
{
    type Item = DecodeResult<char>;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            break match self.state {
                UnwrapStringState::Init => match self.iter.next() {
                    Some(START_CHAR) => {
                        self.state = UnwrapStringState::Running;
                        continue;
                    }
                    Some(_) => Some(Err(Error::MissingStart)),
                    None => {
                        self.state = UnwrapStringState::Done;
                        None
                    }
                },
                UnwrapStringState::Running => match self.iter.next() {
                    Some(END_CHAR) => {
                        self.state = UnwrapStringState::Done;
                        self.iter.next().map(|c| Err(Error::TrailingData(c)))
                    }
                    Some(c) => Some(Ok(c)),
                    None => {
                        self.state = UnwrapStringState::Done;
                        Some(Err(Error::MissingEnd))
                    }
                },
                UnwrapStringState::Done => None,
            };
        }
    }
}

impl<I: Iterator<Item = char>> FusedIterator for UnwrapString<I> {}

struct CharsToUnflatDigits<I>(I);

impl<I> CharsToUnflatDigits<I> {
    pub fn new(iter: I) -> Self {
        Self(iter)
    }
}

impl<I: InspectBaseIterator> InspectBaseIterator for CharsToUnflatDigits<I> {
    type Iter = I::Iter;

    fn base_iterator(&self) -> &Self::Iter {
        self.0.base_iterator()
    }
}

type CharsToUnflatDigitsItem = Take<array::IntoIter<DecodeResult<Digit>, 3>>;

impl<I> Iterator for CharsToUnflatDigits<I>
where
    I: Iterator<Item = DecodeResult<char>>,
{
    type Item = CharsToUnflatDigitsItem;

    fn next(&mut self) -> Option<Self::Item> {
        const D0: Digit = const_digit!(0);

        fn to_digit(n: u16, c: char) -> Digit {
            if let Some(d) = u8::try_from(n).ok().and_then(Digit::new) {
                d
            } else {
                panic!(
                    "char ({:?}) unmapped to bad value: invalid digit: {}",
                    c, n
                );
            }
        }

        self.0.next().map(|c| {
            c.and_then(|c| {
                match c.len_utf8() {
                    1 => ranges::unmap_char(c, RANGES1)
                        .map(|n| ([to_digit(n, c), D0, D0], 1)),
                    2 => ranges::unmap_char(c, RANGES2).map(|n| {
                        let d2 = n % L1_MULT;
                        let d1 = to_digit(n / L1_MULT + 97, c);
                        let d2 = if d2 == L1_MULT - 1 {
                            return ([d1, D0, D0], 1);
                        } else {
                            to_digit(d2, c)
                        };
                        ([d1, d2, D0], 2)
                    }),
                    3 => ranges::unmap_char(c, RANGES3).map(|n| {
                        let d2to3 = n % L2_MULT;
                        let d1 = to_digit(n / L2_MULT + 112, c);
                        if d2to3 == L2_MULT - 1 {
                            return ([d1, D0, D0], 1);
                        };

                        let d3 = d2to3 % L1_MULT;
                        let d2 = to_digit(d2to3 / L1_MULT, c);
                        let d3 = if d3 == L1_MULT - 1 {
                            return ([d1, d2, D0], 2);
                        } else {
                            to_digit(d3, c)
                        };
                        ([d1, d2, d3], 3)
                    }),
                    _ => None,
                }
                .ok_or(Error::BadChar(c))
            })
            .map_or_else(
                |e| IntoIterator::into_iter([Err(e), Ok(D0), Ok(D0)]).take(1),
                |(arr, len)| IntoIterator::into_iter(arr.map(Ok)).take(len),
            )
        })
    }
}

impl<I: FusedIterator<Item = DecodeResult<char>>> FusedIterator
    for CharsToUnflatDigits<I>
{
}

struct DigitsToUnflatBytes<I>(I);

impl<I> DigitsToUnflatBytes<I> {
    pub fn new(iter: I) -> Self {
        Self(iter)
    }
}

impl<I: InspectBaseIterator> InspectBaseIterator for DigitsToUnflatBytes<I> {
    type Iter = I::Iter;

    fn base_iterator(&self) -> &Self::Iter {
        self.0.base_iterator()
    }
}

type DigitsToUnflatBytesItem = Take<array::IntoIter<DecodeResult<u8>, 6>>;

impl<I> Iterator for DigitsToUnflatBytes<I>
where
    I: Iterator<Item = DecodeResult<Digit>>,
{
    type Item = DigitsToUnflatBytesItem;

    fn next(&mut self) -> Option<Self::Item> {
        // SAFETY: `116 - 1` is less than 116.
        let mut digits = [const_digit!(116 - 1); 7];
        let mut len = 0;
        self.0
            .by_ref()
            .enumerate()
            .take(7)
            .try_for_each(|(i, d)| {
                d.map(|d| {
                    digits[i] = d;
                    len += 1;
                })
            })
            .and_then(|_| match len {
                0 => Ok(None),
                1 => Err(Error::BadLength),
                _ => Ok(Some(())),
            })
            .map(|opt| {
                opt.map(|_| {
                    digits
                        .iter()
                        .copied()
                        .fold(0, |sum, d| sum * 116 + u64::from(u8::from(d)))
                        .to_be_bytes()
                })
                .map(|[_, _, a, b, c, d, e, f]| [a, b, c, d, e, f])
            })
            .transpose()
            .map(|res| {
                res.map_or_else(
                    |e| {
                        IntoIterator::into_iter([
                            Err(e),
                            Ok(0),
                            Ok(0),
                            Ok(0),
                            Ok(0),
                            Ok(0),
                        ])
                        .take(1)
                    },
                    |arr| IntoIterator::into_iter(arr.map(Ok)).take(len - 1),
                )
            })
    }
}

impl<I: FusedIterator<Item = DecodeResult<Digit>>> FusedIterator
    for DigitsToUnflatBytes<I>
{
}

#[allow(clippy::type_complexity)]
struct BaseDecoder<I>(
    Flatten<
        DigitsToUnflatBytes<
            Flatten<
                CharsToUnflatDigits<UnwrapString<I>>,
                CharsToUnflatDigitsItem,
            >,
        >,
        DigitsToUnflatBytesItem,
    >,
);

impl<I> BaseDecoder<I> {
    pub fn new(iter: I) -> Self {
        Self(Flatten::new(DigitsToUnflatBytes::new(Flatten::new(
            CharsToUnflatDigits::new(UnwrapString::new(iter)),
        ))))
    }
}

impl<I: InspectBaseIterator> InspectBaseIterator for BaseDecoder<I> {
    type Iter = I::Iter;

    fn base_iterator(&self) -> &Self::Iter {
        self.0.base_iterator()
    }
}

impl<I> Iterator for BaseDecoder<I>
where
    I: Iterator<Item = char>,
{
    type Item = DecodeResult<u8>;

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next()
    }

    fn fold<B, F>(self, init: B, f: F) -> B
    where
        F: FnMut(B, Self::Item) -> B,
    {
        self.0.fold(init, f)
    }
}

impl<I: FusedIterator<Item = char>> FusedIterator for BaseDecoder<I> {}

pub struct CharDecoder<I>(BaseDecoder<BaseIterator<I>>);

impl<I> CharDecoder<I> {
    pub(crate) fn new(iter: I) -> Self {
        Self(BaseDecoder::new(BaseIterator(iter)))
    }
}

impl<I> Iterator for CharDecoder<I>
where
    I: Iterator<Item = char>,
{
    type Item = DecodeResult<u8>;

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
        (
            lower
                .checked_sub([START_CHAR, END_CHAR].len())
                .and_then(|n| n.checked_mul(BYTES_PER_CHUNK))
                .map(|n| n / DIGITS_PER_CHUNK)
                .map_or(0, |n| {
                    // The last char could be a three-byte UTF-8 sequence
                    // that represents only one base-116 digit, so we subtract
                    // 2 here.
                    n - 2
                }),
            upper
                .and_then(|n| {
                    // The input could consist entirely of chars with a UTF-8
                    // length of 3, so we multiply by 3 here.
                    n.checked_mul(3)
                })
                .and_then(|n| n.checked_mul(BYTES_PER_CHUNK))
                .map(|n| n / DIGITS_PER_CHUNK),
        )
    }
}

impl<I: FusedIterator<Item = char>> FusedIterator for CharDecoder<I> {}

fn size_hint_from_utf8_hint(
    hint: (usize, Option<usize>),
) -> (usize, Option<usize>) {
    let (lower, upper) = hint;
    (
        lower
            .checked_sub(START_CHAR.len_utf8() + END_CHAR.len_utf8())
            .and_then(|n| n.checked_mul(BYTES_PER_CHUNK))
            .map(|n| n / DIGITS_PER_CHUNK)
            .map_or(0, |n| {
                // The last char could be a three-byte UTF-8 sequence
                // that represents only one base-116 digit, so we subtract
                // 2 here.
                n - 2
            }),
        upper
            .and_then(|n| n.checked_mul(BYTES_PER_CHUNK))
            .map(|n| n / DIGITS_PER_CHUNK),
    )
}

struct Utf8ToChars<I>(I);

impl<I> Utf8ToChars<I> {
    pub fn new(iter: I) -> Self {
        Self(iter)
    }
}

impl<I: InspectBaseIterator> InspectBaseIterator for Utf8ToChars<I> {
    type Iter = I::Iter;

    fn base_iterator(&self) -> &Self::Iter {
        self.0.base_iterator()
    }
}

impl<I> Iterator for Utf8ToChars<I>
where
    I: Iterator<Item = u8>,
{
    type Item = Result<char, InvalidUtf8>;

    fn next(&mut self) -> Option<Self::Item> {
        let mut bytes = [self.0.next()?, 0, 0, 0];
        let mut len = 1;
        loop {
            match core::str::from_utf8(&bytes[..len]) {
                Ok(s) => break Some(Ok(s.chars().next().unwrap())),
                Err(e) if e.error_len().is_none() && len < bytes.len() => {
                    if let Some(b) = self.0.next() {
                        bytes[len] = b;
                        len += 1;
                        continue;
                    }
                }
                _ => {}
            }
            break Some(Err(InvalidUtf8 {
                bytes,
                len: len as u8,
            }));
        }
    }
}

impl<I: FusedIterator<Item = u8>> FusedIterator for Utf8ToChars<I> {}

pub struct BytesDecoder<I>(
    BaseDecoder<
        BaseIterator<ErrAdapter<Utf8ToChars<BaseIterator<I>>, InvalidUtf8>>,
    >,
);

impl<I> BytesDecoder<I> {
    pub(crate) fn new(iter: I) -> Self {
        Self(BaseDecoder::new(BaseIterator(ErrAdapter::new(
            Utf8ToChars::new(BaseIterator(iter)),
        ))))
    }
}

impl<I> Iterator for BytesDecoder<I>
where
    I: Iterator<Item = u8>,
{
    type Item = DecodeBytesResult<u8>;

    fn next(&mut self) -> Option<Self::Item> {
        let item = self.0.next();
        if let Some(e) = self.0.base_iterator().take_err() {
            return Some(Err(DecodeBytesError::InvalidUtf8(e)));
        }
        match item {
            Some(Ok(b)) => Some(Ok(b)),
            Some(Err(e)) => Some(Err(DecodeBytesError::DecodeError(e))),
            None => None,
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let iter: &I = self.0.base_iterator().base_iterator();
        size_hint_from_utf8_hint(iter.size_hint())
    }
}

impl<I: FusedIterator<Item = u8>> FusedIterator for BytesDecoder<I> {}

pub struct StrDecoder<'a>(BaseDecoder<BaseIterator<Chars<'a>>>);

impl<'a> StrDecoder<'a> {
    pub(crate) fn new(s: &'a str) -> Self {
        Self(BaseDecoder::new(BaseIterator(s.chars())))
    }
}

impl<'a> Iterator for StrDecoder<'a> {
    type Item = DecodeResult<u8>;

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
        let len = self.0.base_iterator().as_str().len();
        size_hint_from_utf8_hint((len, Some(len)))
    }
}

impl<'a> FusedIterator for StrDecoder<'a> {}

pub fn decode_chars<I>(chars: I) -> CharDecoder<I::IntoIter>
where
    I: IntoIterator<Item = char>,
{
    CharDecoder::new(chars.into_iter())
}

pub fn decode_bytes<I>(bytes: I) -> BytesDecoder<I::IntoIter>
where
    I: IntoIterator<Item = u8>,
{
    BytesDecoder::new(bytes.into_iter())
}

pub fn decode_str(s: &str) -> StrDecoder<'_> {
    StrDecoder::new(s)
}

pub struct WrapperlessCharDecoder<I>(CharDecoder<AddInputCharWrapper<I>>)
where
    I: Iterator<Item = char>;

impl<I: Iterator<Item = char>> Iterator for WrapperlessCharDecoder<I> {
    type Item = DecodeResult<u8>;

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

pub fn decode_chars_no_wrapper<I>(
    bytes: I,
) -> WrapperlessCharDecoder<I::IntoIter>
where
    I: IntoIterator<Item = char>,
{
    WrapperlessCharDecoder(decode_chars(add_input_char_wrapper(
        bytes.into_iter(),
    )))
}

pub struct WrapperlessBytesDecoder<I>(BytesDecoder<AddInputWrapper<I>>)
where
    I: Iterator<Item = u8>;

impl<I: Iterator<Item = u8>> Iterator for WrapperlessBytesDecoder<I> {
    type Item = DecodeBytesResult<u8>;

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

pub fn decode_bytes_no_wrapper<I>(
    bytes: I,
) -> WrapperlessBytesDecoder<I::IntoIter>
where
    I: IntoIterator<Item = u8>,
{
    WrapperlessBytesDecoder(decode_bytes(add_input_wrapper(bytes.into_iter())))
}
