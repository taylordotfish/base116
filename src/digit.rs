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
