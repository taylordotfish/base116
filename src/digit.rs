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

#[derive(Clone, Copy)]
pub struct Digit(u8);

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
