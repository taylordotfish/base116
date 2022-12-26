/*
 * Copyright (C) 2021 taylor.fish <contact@taylor.fish>
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

//! Base116 is like Base85, but it increases data size by only 1/6 instead of
//! 1/4.
//!
//! Base116 exploits properties of UTF-8 to convert arbitrary binary data to
//! valid, printable UTF-8, with a lower size overhead than is possible with
//! any printable ASCII encoding.
//!
//! For example, this binary data (in hex):
//!
//! ```text
//! 9329bd4b43da0bfdd1d97bdf081a2d42ec540155
//! ```
//!
//! is encoded as:
//!
//! ```text
//! Ǳ<Oȥґ|yO(WFic{2n㎨r~9*ǲ
//! ```
//!
//! Wrapping ‘Ǳ’ and ‘ǲ’ characters are added by default to make encoded data
//! easier to select, as the data may start or end with combining characters or
//! characters from right-to-left scripts.
//!
//! This crate provides both a binary and a library.

#![cfg_attr(not(feature = "std"), no_std)]
#![cfg_attr(feature = "doc_cfg", feature(doc_cfg))]
#![deny(unsafe_op_in_unsafe_fn)]

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
