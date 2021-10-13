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

pub mod decode;
pub mod encode;
mod iter;
mod ranges;
mod unwrap;

#[cfg(feature = "alloc")]
extern crate alloc;

const BYTES_PER_CHUNK: usize = 6;
const DIGITS_PER_CHUNK: usize = 7;

const START_CHAR: char = '\u{1f1}';
const END_CHAR: char = '\u{1f2}';

const START_UTF8: [u8; 2] = [0xc7, 0xb1];
const END_UTF8: [u8; 2] = [0xc7, 0xb2];

const L1_MULT: u16 = 116 + 1;
const L2_MULT: u16 = 116 * L1_MULT + 1;

#[macro_use]
mod digit {
    #[derive(Clone, Copy)]
    pub struct Digit(u8);

    #[macro_export]
    macro_rules! const_digit {
        ($n:expr) => {{
            use crate::digit::Digit;
            const DIGIT: Digit = Digit::__const($n);
            DIGIT
        }};
    }

    impl Digit {
        pub fn new(x: u8) -> Option<Self> {
            (x < 116).then(|| Self(x))
        }

        /// # Safety
        ///
        /// `x` must be less than 116.
        pub unsafe fn new_unchecked(x: u8) -> Self {
            debug_assert!(x < 116);
            Self(x)
        }

        #[doc(hidden)]
        pub const fn __const(n: u8) -> Self {
            const BOUNDS_CHECK: [u8; 1] = [0];
            Self(n + BOUNDS_CHECK[(n >= 116) as usize])
        }
    }

    impl From<Digit> for u8 {
        fn from(d: Digit) -> u8 {
            d.0
        }
    }
}

use digit::Digit;

pub use decode::decode_bytes;
pub use decode::decode_chars;
pub use decode::decode_str;

pub use encode::encode_to_bytes;
pub use encode::encode_to_chars;
#[cfg(feature = "alloc")]
pub use encode::encode_to_string;
