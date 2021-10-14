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

#![cfg_attr(not(feature = "std"), no_std)]
#![cfg_attr(feature = "doc_cfg", feature(doc_cfg))]

#[macro_use]
mod digit;
use digit::Digit;

pub mod decode;
pub mod encode;
mod iter;
mod ranges;

#[cfg(feature = "alloc")]
extern crate alloc;

const BYTES_PER_CHUNK: usize = 6;
const DIGITS_PER_CHUNK: usize = 7;

const START_CHAR: char = '\u{1f1}';
const END_CHAR: char = '\u{1f2}';

const L1_MULT: u16 = 116 + 1;
const L2_MULT: u16 = 116 * L1_MULT + 1;

pub use decode::decode_bytes;
pub use decode::decode_chars;
pub use decode::decode_str;
#[cfg(feature = "alloc")]
pub use decode::decode_to_vec;

pub use encode::encode_to_bytes;
pub use encode::encode_to_chars;
#[cfg(feature = "alloc")]
pub use encode::encode_to_string;
