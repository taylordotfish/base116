/*
 * Copyright (C) 2021-2022 taylor.fish <contact@taylor.fish>
 *
 * This file is part of Base116.
 *
 * Base116 is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Affero General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * Base116 is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Affero General Public License for more details.
 *
 * You should have received a copy of the GNU Affero General Public License
 * along with Base116. If not, see <https://www.gnu.org/licenses/>.
 */

//! Functions and types for decoding base-116 data.

use super::Digit;
use super::iter::{BaseIterator, ErrAdapter, Flatten, InspectBaseIterator};
use super::ranges::{self, RANGES1, RANGES2, RANGES3};
use super::{BYTES_PER_CHUNK, DIGITS_PER_CHUNK, END_CHAR, START_CHAR};
use super::{L1_MULT, L2_MULT};

use core::array;
use core::convert::TryFrom;
use core::fmt::{self, Debug, Display, Formatter};
use core::iter::{FusedIterator, Take};
use core::str::Chars;

#[cfg(feature = "alloc")]
use alloc::vec::Vec;

/// An error encountered while decoding a [`str`] or sequence of [`char`]s.
#[non_exhaustive]
#[derive(Debug)]
pub enum DecodeError {
    /// Encountered an unexpected character.
    BadChar(char),
    /// The input was not the correct number of characters.
    BadLength,
    /// The starting 'Ǳ' character was required but missing.
    MissingStart,
    /// The ending 'ǲ' character was required but missing.
    MissingEnd,
    /// There was unexpected data after the ending 'ǲ' character, and
    /// [`DecodeConfig::relaxed`] was false.
    TrailingData(char),
}

use DecodeError as Error;

/// Alias of <code>[Result]\<T, [DecodeError]></code>.
pub type DecodeResult<T> = Result<T, DecodeError>;

impl fmt::Display for DecodeError {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        match self {
            Self::BadChar(c) => write!(f, "bad character: {:?}", c),
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

/// Error information for [`DecodeBytesError::InvalidUtf8`].
pub struct InvalidUtf8 {
    bytes: [u8; 4],
    len: u8,
}

impl InvalidUtf8 {
    /// The bytes that were invalid UTF-8.
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

/// An error encountered while decoding a sequence of bytes.
#[derive(Debug)]
pub enum DecodeBytesError {
    /// The provided bytes were not valid UTF-8.
    InvalidUtf8(InvalidUtf8),
    /// A different decoding error occurred.
    DecodeError(DecodeError),
}

/// Alias of <code>[Result]\<T, [DecodeBytesError]></code>.
pub type DecodeBytesResult<T> = Result<T, DecodeBytesError>;

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
    config: DecodeConfig,
    state: UnwrapStringState,
}

impl<I> UnwrapString<I> {
    pub fn new(iter: I, config: DecodeConfig) -> Self {
        Self {
            iter,
            config,
            state: UnwrapStringState::Init,
        }
    }
}

impl<I> UnwrapString<I>
where
    I: Iterator<Item = char>,
{
    fn handle_running(
        &mut self,
        c: Option<char>,
    ) -> Option<DecodeResult<char>> {
        match c {
            Some(END_CHAR) => {
                self.state = UnwrapStringState::Done;
                if self.config.relaxed {
                    None
                } else {
                    self.iter.next().map(|c| Err(Error::TrailingData(c)))
                }
            }
            Some(c) => Some(Ok(c)),
            None => {
                self.state = UnwrapStringState::Done;
                if self.config.require_wrapper {
                    Some(Err(Error::MissingEnd))
                } else {
                    None
                }
            }
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
                UnwrapStringState::Init => {
                    let item = if self.config.require_wrapper
                        && self.config.relaxed
                    {
                        self.iter.find(|c| *c == START_CHAR)
                    } else {
                        self.iter.next()
                    };
                    match item {
                        Some(START_CHAR) => {
                            self.state = UnwrapStringState::Running;
                            continue;
                        }
                        c => {
                            if self.config.require_wrapper {
                                self.state = UnwrapStringState::Done;
                                Some(Err(Error::MissingStart))
                            } else {
                                self.state = UnwrapStringState::Running;
                                self.handle_running(c)
                            }
                        }
                    }
                }
                UnwrapStringState::Running => {
                    let item = self.iter.next();
                    self.handle_running(item)
                }
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
                    c, n,
                );
            }
        }

        self.0.next().map(|c| {
            c.and_then(|c| {
                match c.len_utf8() {
                    1 => ranges::unmap_char(c, RANGES1)
                        .map(|n| {
                            // When encoding digits <= 96, the encoder first
                            // transforms the digit by subtracting it from 96
                            // (so that 0 maps to ~ instead of tab). Here we
                            // reverse that transformation accordingly.
                            96 - n
                        })
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
            .and(match len {
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
                        let arr = [Err(e), Ok(0), Ok(0), Ok(0), Ok(0), Ok(0)];
                        IntoIterator::into_iter(arr).take(1)
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

/// Iterator returned by [`decode_chars`].
#[allow(clippy::type_complexity)]
pub struct CharDecoder<I>(
    Flatten<
        DigitsToUnflatBytes<
            Flatten<
                CharsToUnflatDigits<UnwrapString<BaseIterator<I>>>,
                CharsToUnflatDigitsItem,
            >,
        >,
        DigitsToUnflatBytesItem,
    >,
);

impl<I> CharDecoder<I> {
    pub(crate) fn new(iter: I, config: DecodeConfig) -> Self {
        Self(Flatten::new(DigitsToUnflatBytes::new(Flatten::new(
            CharsToUnflatDigits::new(UnwrapString::new(
                BaseIterator(iter),
                config,
            )),
        ))))
    }
}

impl<I> InspectBaseIterator for CharDecoder<I> {
    type Iter = I;

    fn base_iterator(&self) -> &Self::Iter {
        self.0.base_iterator()
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

// `UnwrapString` implements `FusedIterator`, so `CharDecoder` also can even
// if `I` doesn't.
impl<I: Iterator<Item = char>> FusedIterator for CharDecoder<I> {}

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
                Err(e) => {
                    if e.error_len().is_none() && len < bytes.len() {
                        if let Some(b) = self.0.next() {
                            bytes[len] = b;
                            len += 1;
                            continue;
                        }
                    }
                }
            }
            break Some(Err(InvalidUtf8 {
                bytes,
                len: len as u8,
            }));
        }
    }
}

impl<I: FusedIterator<Item = u8>> FusedIterator for Utf8ToChars<I> {}

/// Iterator returned by [`decode_bytes`].
pub struct BytesDecoder<I>(
    CharDecoder<ErrAdapter<Utf8ToChars<BaseIterator<I>>, InvalidUtf8>>,
);

impl<I> BytesDecoder<I> {
    pub(crate) fn new(iter: I, config: DecodeConfig) -> Self {
        Self(CharDecoder::new(
            ErrAdapter::new(Utf8ToChars::new(BaseIterator(iter))),
            config,
        ))
    }
}

impl<I> Iterator for BytesDecoder<I>
where
    I: Iterator<Item = u8>,
{
    type Item = DecodeBytesResult<u8>;

    fn next(&mut self) -> Option<Self::Item> {
        let item = self.0.next();
        if !matches!(item, Some(Ok(_))) {
            if let Some(e) = self.0.base_iterator().take_err() {
                return Some(Err(DecodeBytesError::InvalidUtf8(e)));
            }
        }
        Some(match item? {
            Ok(b) => Ok(b),
            Err(e) => Err(DecodeBytesError::DecodeError(e)),
        })
    }

    fn fold<B, F>(mut self, mut init: B, mut f: F) -> B
    where
        F: FnMut(B, Self::Item) -> B,
    {
        loop {
            let result = self.0.try_fold(init, |b, item| {
                let item = match item {
                    Ok(item) => item,
                    Err(e) => return Err((b, e)),
                };
                Ok(f(b, Ok(item)))
            });

            let (mut b, err) = match result {
                Ok(b) => (b, None),
                Err((b, e)) => (b, Some(e)),
            };

            if let Some(e) = self.0.base_iterator().take_err() {
                b = f(b, Err(DecodeBytesError::InvalidUtf8(e)));
            }

            if let Some(e) = err {
                b = f(b, Err(DecodeBytesError::DecodeError(e)));
            } else {
                // Iteration is done because `try_fold` returned `Ok`.
                return b;
            }
            init = b;
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let iter: &I = self.0.base_iterator().base_iterator();
        size_hint_from_utf8_hint(iter.size_hint())
    }
}

impl<I: FusedIterator<Item = u8>> FusedIterator for BytesDecoder<I> {}

/// Iterator returned by [`decode_str`].
pub struct StrDecoder<'a>(CharDecoder<Chars<'a>>);

impl<'a> StrDecoder<'a> {
    pub(crate) fn new(s: &'a str, config: DecodeConfig) -> Self {
        Self(CharDecoder::new(s.chars(), config))
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

/// Decodes a sequence of base-116 chars.
pub fn decode_chars<I>(chars: I) -> CharDecoder<I::IntoIter>
where
    I: IntoIterator<Item = char>,
{
    decode_chars_with(chars, DecodeConfig::new())
}

/// Decodes UTF-8 base-116 data.
pub fn decode_bytes<I>(bytes: I) -> BytesDecoder<I::IntoIter>
where
    I: IntoIterator<Item = u8>,
{
    decode_bytes_with(bytes, DecodeConfig::new())
}

/// Decodes a base-116 `str`.
pub fn decode_str(s: &str) -> StrDecoder<'_> {
    decode_str_with(s, DecodeConfig::new())
}

/// Used by the `decode_*_with` functions to configure the decoding process.
#[non_exhaustive]
#[derive(Clone, Copy)]
pub struct DecodeConfig {
    /// Whether to require wrapping ‘Ǳ’ and ‘ǲ’ characters to be present.
    /// [default: true]
    pub require_wrapper: bool,
    /// If true, trailing data after the ending ‘ǲ’ character will be ignored,
    /// rather than causing an error. Additionally, if `require_wrapper` is
    /// true, extra data before the starting ‘Ǳ’ character will also be
    /// ignored. [default: false]
    pub relaxed: bool,
}

impl DecodeConfig {
    /// Returns the default configuration.
    pub const fn new() -> Self {
        Self {
            require_wrapper: true,
            relaxed: false,
        }
    }
}

impl Default for DecodeConfig {
    fn default() -> Self {
        Self::new()
    }
}

/// Decodes a sequence of base-116 chars with the given config.
///
/// This function is like [`decode_chars`], but takes a configuration object.
pub fn decode_chars_with<I>(
    chars: I,
    config: DecodeConfig,
) -> CharDecoder<I::IntoIter>
where
    I: IntoIterator<Item = char>,
{
    CharDecoder::new(chars.into_iter(), config)
}

/// Decodes UTF-8 base-116 data with the given config.
///
/// This function is like [`decode_bytes`], but takes a configuration object.
pub fn decode_bytes_with<I>(
    bytes: I,
    config: DecodeConfig,
) -> BytesDecoder<I::IntoIter>
where
    I: IntoIterator<Item = u8>,
{
    BytesDecoder::new(bytes.into_iter(), config)
}

/// Decodes a base-116 `str` with the given config.
///
/// This function is like [`decode_str`], but takes a configuration object.
pub fn decode_str_with(s: &str, config: DecodeConfig) -> StrDecoder<'_> {
    StrDecoder::new(s, config)
}

/// Takes a decoder and stores the contents in a [`Vec`].
///
/// This is equivalent to calling [`decoder.collect()`](Iterator::collect).
#[cfg(feature = "alloc")]
#[cfg_attr(feature = "doc_cfg", doc(cfg(feature = "alloc")))]
pub fn decode_to_vec<D, E>(decoder: D) -> Result<Vec<u8>, E>
where
    D: Iterator<Item = Result<u8, E>>,
{
    decoder.collect()
}
