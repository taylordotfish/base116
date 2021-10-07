#![cfg_attr(not(feature = "std"), no_std)]
#![cfg_attr(feature = "doc_cfg", feature(doc_cfg))]

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

mod digit {
    #[derive(Clone, Copy)]
    pub struct Digit(u8);

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

        pub const fn zero() -> Self {
            Self(0)
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
pub use decode::{DecodeBytesError, DecodeBytesResult};
pub use decode::{DecodeError, DecodeResult};

pub use encode::encode_to_bytes;
pub use encode::encode_to_chars;
#[cfg(feature = "alloc")]
pub use encode::encode_to_string;
