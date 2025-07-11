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

//! Functions and types for encoding base-116 data.

use super::Digit;
use super::iter::{BaseIterator, Flatten, InspectBaseIterator};
use super::ranges::{self, RANGES1, RANGES2, RANGES3};
use super::{BYTES_PER_CHUNK, DIGITS_PER_CHUNK, END_CHAR, START_CHAR};
use super::{L1_MULT, L2_MULT};

use core::array;
use core::hint::unreachable_unchecked;
use core::iter::{Fuse, FusedIterator, Take};

#[cfg(feature = "alloc")]
use alloc::{string::String, vec::Vec};

struct BytesToUnflatDigits<I>(I);

impl<I> BytesToUnflatDigits<I> {
    pub fn new(iter: I) -> Self {
        Self(iter)
    }
}

impl<I: InspectBaseIterator> InspectBaseIterator for BytesToUnflatDigits<I> {
    type Iter = I::Iter;

    fn base_iterator(&self) -> &Self::Iter {
        self.0.base_iterator()
    }
}

type BytesToUnflatDigitsItem = Take<array::IntoIter<Digit, 7>>;

impl<I> Iterator for BytesToUnflatDigits<I>
where
    I: FusedIterator<Item = u8>,
{
    type Item = BytesToUnflatDigitsItem;

    fn next(&mut self) -> Option<Self::Item> {
        let mut num_bytes = 0;
        let mut sum = 0_u64;
        self.0
            .by_ref()
            .map(u64::from)
            .enumerate()
            .take(BYTES_PER_CHUNK)
            .for_each(|(i, n)| {
                num_bytes += 1;
                sum |= n << (8 * (BYTES_PER_CHUNK - 1 - i));
            });

        if num_bytes == 0 {
            return None;
        }

        let mut digits = [const_digit!(0); DIGITS_PER_CHUNK];
        digits.iter_mut().rev().for_each(|d| {
            // SAFETY: `sum % 116` is always less than 116.
            *d = unsafe { Digit::new_unchecked((sum % 116) as u8) };
            sum /= 116;
        });
        Some(IntoIterator::into_iter(digits).take(num_bytes + 1))
    }
}

impl<I: FusedIterator<Item = u8>> FusedIterator for BytesToUnflatDigits<I> {}

struct DigitsToChar<I>(I);

impl<I> DigitsToChar<I> {
    pub fn new(iter: I) -> Self {
        Self(iter)
    }
}

impl<I> DigitsToChar<I>
where
    I: Iterator<Item = Digit>,
{
    fn next_u16(&mut self) -> Option<u16> {
        self.0.next().map(u8::from).map(u16::from)
    }
}

impl<I: InspectBaseIterator> InspectBaseIterator for DigitsToChar<I> {
    type Iter = I::Iter;

    fn base_iterator(&self) -> &Self::Iter {
        self.0.base_iterator()
    }
}

impl<I> Iterator for DigitsToChar<I>
where
    I: FusedIterator<Item = Digit>,
{
    type Item = char;

    fn next(&mut self) -> Option<Self::Item> {
        let d = self.next_u16()?;
        match d {
            // Use `96 - d` so that 0 maps to ~ instead of tab.
            0..=96 => Some(ranges::map_char(96 - d, RANGES1).unwrap()),
            97..=111 => {
                let d1 = (d - 97) * L1_MULT;
                let d2 = self.next_u16().unwrap_or(L1_MULT - 1);
                Some(ranges::map_char(d1 + d2, RANGES2).unwrap())
            }
            112..=115 => {
                let d1 = (d - 112) * L2_MULT;
                let d2to3 = self.next_u16().map_or(L2_MULT - 1, |d2| {
                    let d2 = d2 * L1_MULT;
                    let d3 = self.next_u16().unwrap_or(L1_MULT - 1);
                    d2 + d3
                });
                Some(ranges::map_char(d1 + d2to3, RANGES3).unwrap())
            }
            _ => {
                debug_assert!(d < 116);
                // SAFETY: The invariants of `Digit` guarantee that it is
                // less than 116.
                unsafe { unreachable_unchecked() };
            }
        }
    }
}

impl<I: FusedIterator<Item = Digit>> FusedIterator for DigitsToChar<I> {}

enum CharEncoderState {
    Init,
    Running,
    Done,
}

/// Iterator returned by [`encode_to_chars`].
pub struct CharEncoder<I> {
    config: EncodeConfig,
    state: CharEncoderState,
    iter: DigitsToChar<
        Flatten<
            BytesToUnflatDigits<BaseIterator<Fuse<I>>>,
            BytesToUnflatDigitsItem,
        >,
    >,
}

impl<I: Iterator> CharEncoder<I> {
    pub(crate) fn new(iter: I, config: EncodeConfig) -> Self {
        Self {
            config,
            state: if config.add_wrapper {
                CharEncoderState::Init
            } else {
                CharEncoderState::Running
            },
            iter: DigitsToChar::new(Flatten::new(BytesToUnflatDigits::new(
                BaseIterator(iter.fuse()),
            ))),
        }
    }
}

impl<I> InspectBaseIterator for CharEncoder<I> {
    type Iter = Fuse<I>;

    fn base_iterator(&self) -> &Self::Iter {
        self.iter.base_iterator()
    }
}

impl<I> Iterator for CharEncoder<I>
where
    I: Iterator<Item = u8>,
{
    type Item = char;

    fn next(&mut self) -> Option<Self::Item> {
        match self.state {
            CharEncoderState::Init => {
                self.state = CharEncoderState::Running;
                Some(START_CHAR)
            }
            CharEncoderState::Running => self.iter.next().or_else(|| {
                self.state = CharEncoderState::Done;
                self.config.add_wrapper.then(|| END_CHAR)
            }),
            CharEncoderState::Done => None,
        }
    }

    fn fold<B, F>(self, mut init: B, mut f: F) -> B
    where
        F: FnMut(B, Self::Item) -> B,
    {
        if let CharEncoderState::Done = self.state {
            return init;
        }
        if let CharEncoderState::Init = self.state {
            init = f(init, START_CHAR);
        }
        init = self.iter.fold(init, &mut f);
        f(init, END_CHAR)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let (lower, upper) = self.base_iterator().size_hint();
        let lower = lower
            .checked_mul(DIGITS_PER_CHUNK)
            .and_then(|n| n.checked_add(BYTES_PER_CHUNK - 1))
            .map_or(lower, |n| n / BYTES_PER_CHUNK);
        (
            // The output could consist of chars with a UTF-8 length
            // of 3, so we divide by 3 here.
            lower / 3,
            upper
                .and_then(|n| n.checked_mul(DIGITS_PER_CHUNK))
                .and_then(|n| n.checked_add(BYTES_PER_CHUNK - 1))
                .map(|n| n / BYTES_PER_CHUNK)
                .map(|n| {
                    // If the total number of bytes produced by the base
                    // iterator (of type `I`) is congruent to 1 (mod 6),
                    // the corresponding number of base-116 digits will be
                    // ceil(n * 7/6) + 1 rather than ceil(n * 7/6), so we
                    // add 1 here.
                    n + 1
                })
                .map(|n| n + [START_CHAR, END_CHAR].len()),
        )
    }
}

impl<I: Iterator<Item = u8>> FusedIterator for CharEncoder<I> {}

struct CharsToUnflatUtf8<I>(I);

impl<I> CharsToUnflatUtf8<I> {
    pub fn new(iter: I) -> Self {
        Self(iter)
    }
}

impl<I: InspectBaseIterator> InspectBaseIterator for CharsToUnflatUtf8<I> {
    type Iter = I::Iter;

    fn base_iterator(&self) -> &Self::Iter {
        self.0.base_iterator()
    }
}

type CharsToUnflatUtf8Item = Take<array::IntoIter<u8, 4>>;

impl<I> Iterator for CharsToUnflatUtf8<I>
where
    I: Iterator<Item = char>,
{
    type Item = CharsToUnflatUtf8Item;

    fn next(&mut self) -> Option<Self::Item> {
        let mut bytes = [0; 4];
        let len = self.0.next()?.encode_utf8(&mut bytes).len();
        Some(IntoIterator::into_iter(bytes).take(len))
    }
}

impl<I: FusedIterator<Item = char>> FusedIterator for CharsToUnflatUtf8<I> {}

/// Iterator returned by [`encode_to_bytes`].
pub struct Utf8Encoder<I>(
    Flatten<CharsToUnflatUtf8<CharEncoder<I>>, CharsToUnflatUtf8Item>,
);

impl<I: Iterator> Utf8Encoder<I> {
    pub(crate) fn new(iter: I, config: EncodeConfig) -> Self {
        Self(Flatten::new(CharsToUnflatUtf8::new(CharEncoder::new(
            iter,
            config,
        ))))
    }
}

impl<I> Iterator for Utf8Encoder<I>
where
    I: Iterator<Item = u8>,
{
    type Item = u8;

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
                .checked_mul(DIGITS_PER_CHUNK)
                .and_then(|n| n.checked_add(BYTES_PER_CHUNK - 1))
                .map_or(lower, |n| n / BYTES_PER_CHUNK),
            upper
                .and_then(|n| n.checked_mul(DIGITS_PER_CHUNK))
                .and_then(|n| n.checked_add(BYTES_PER_CHUNK - 1))
                .map(|n| n / BYTES_PER_CHUNK + 1)
                .map(|n| {
                    // See `<CharEncoder as Iterator>::size_hint` for why
                    // we add 1 here.
                    n + 1
                })
                .map(|n| {
                    // The last byte produced by the base iterator may end up
                    // having to be encoded as a two- or three-byte UTF-8
                    // sequence, so we also add 2 here.
                    n + 2
                })
                .map(|n| n + START_CHAR.len_utf8() + END_CHAR.len_utf8()),
        )
    }
}

impl<I: Iterator<Item = u8>> FusedIterator for Utf8Encoder<I> {}

/// Encodes `bytes` as a sequence of base-116 [`char`]s.
pub fn encode_to_chars<I>(bytes: I) -> CharEncoder<I::IntoIter>
where
    I: IntoIterator<Item = u8>,
{
    encode_to_chars_with(bytes, EncodeConfig::new())
}

/// Encodes `bytes` to UTF-8 base-116 data.
pub fn encode_to_bytes<I>(bytes: I) -> Utf8Encoder<I::IntoIter>
where
    I: IntoIterator<Item = u8>,
{
    encode_to_bytes_with(bytes, EncodeConfig::new())
}

/// Encodes `bytes` to a base-116 [`String`].
#[cfg(feature = "alloc")]
#[cfg_attr(feature = "doc_cfg", doc(cfg(feature = "alloc")))]
pub fn encode_to_string<I>(bytes: I) -> String
where
    I: IntoIterator<Item = u8>,
{
    encode_to_string_with(bytes, EncodeConfig::new())
}

/// Used by the `encode_*_with` functions to configure the encoding process.
#[non_exhaustive]
#[derive(Clone, Copy)]
pub struct EncodeConfig {
    /// Whether to add wrapping ‘Ǳ’ and ‘ǲ’ characters to the output.
    /// [default: true]
    pub add_wrapper: bool,
}

impl EncodeConfig {
    /// Returns the default configuration.
    pub const fn new() -> Self {
        Self {
            add_wrapper: true,
        }
    }
}

impl Default for EncodeConfig {
    fn default() -> Self {
        Self::new()
    }
}

/// Encodes `bytes` as a sequence of base-116 [`char`]s with the given config.
///
/// This function is like [`encode_to_chars`], but takes a configuration
/// object.
pub fn encode_to_chars_with<I>(
    bytes: I,
    config: EncodeConfig,
) -> CharEncoder<I::IntoIter>
where
    I: IntoIterator<Item = u8>,
{
    CharEncoder::new(bytes.into_iter(), config)
}

/// Encodes `bytes` to UTF-8 base-116 data with the given config.
///
/// This function is like [`encode_to_bytes`], but takes a configuration
/// object.
pub fn encode_to_bytes_with<I>(
    bytes: I,
    config: EncodeConfig,
) -> Utf8Encoder<I::IntoIter>
where
    I: IntoIterator<Item = u8>,
{
    Utf8Encoder::new(bytes.into_iter(), config)
}

/// Encodes `bytes` to a base-116 [`String`] with the given config.
///
/// This function is like [`encode_to_string`], but takes a configuration
/// object.
#[cfg(feature = "alloc")]
#[cfg_attr(feature = "doc_cfg", doc(cfg(feature = "alloc")))]
pub fn encode_to_string_with<I>(bytes: I, config: EncodeConfig) -> String
where
    I: IntoIterator<Item = u8>,
{
    let utf8: Vec<u8> = encode_to_bytes_with(bytes, config).collect();
    if cfg!(debug_assertions) {
        core::str::from_utf8(&utf8).expect("invalid utf-8: this is UB!");
    }

    // SAFETY: `Utf8Encoder` always produces valid UTF-8.
    unsafe { String::from_utf8_unchecked(utf8) }
}
