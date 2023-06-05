use super::{QUIET_NAN, SIGN_MASK};
use crate::nan::NEG_QUIET_NAN;
use std::borrow::Borrow;
use std::ops::{Add, Div, Mul, Sub};

/// A 64-bit float type that can only contain one possible NaN value (positive or negative) matching
/// the valid `NaN` values for a [`RawBox`](crate::nan::RawBox). This allows handing out mutable
/// references to the contained float data without allowing users to write invalid data into the box.
#[derive(Copy, Clone)]
#[repr(transparent)]
pub struct SingleNaNF64(f64);

impl SingleNaNF64 {
    /// Create a new `SingleNaNF64` from a float value - this will normalize any `NaN` into the
    /// canonical value used by the type.
    #[must_use]
    pub fn new(val: f64) -> SingleNaNF64 {
        match (val.is_nan(), val.is_sign_positive()) {
            (true, true) => SingleNaNF64(f64::from_bits(QUIET_NAN)),
            (true, false) => SingleNaNF64(f64::from_bits(NEG_QUIET_NAN)),
            (false, _) => SingleNaNF64(val),
        }
    }

    /// Attempt to make a `SingleNaNF64` from a mutable reference to an `f64` - this returns `Some`
    /// if the provided float is either non-`NaN` or the canonical `NaN` value, `None` otherwise.
    #[must_use]
    pub fn from_mut(val: &mut f64) -> Option<&mut SingleNaNF64> {
        if val.is_nan() && (val.to_bits() & SIGN_MASK) != QUIET_NAN {
            None
        } else {
            let ptr = (val as *mut f64).cast::<SingleNaNF64>();
            // SAFETY: We're a repr(transparent) wrapper around an f64
            Some(unsafe { &mut *ptr })
        }
    }

    /// Write a float value into this location - if the float is `NaN`, it will be normalized into
    /// the canonical `NaN` values
    pub fn write(&mut self, val: f64) {
        *self = SingleNaNF64::new(val);
    }

    /// Copy out the contained float value
    #[must_use]
    pub fn get(self) -> f64 {
        self.0
    }
}

impl AsRef<f64> for SingleNaNF64 {
    fn as_ref(&self) -> &f64 {
        &self.0
    }
}

impl Borrow<f64> for SingleNaNF64 {
    fn borrow(&self) -> &f64 {
        &self.0
    }
}

impl Add for SingleNaNF64 {
    type Output = SingleNaNF64;

    fn add(self, rhs: Self) -> Self::Output {
        SingleNaNF64::new(self.0 + rhs.0)
    }
}

impl Add<f64> for SingleNaNF64 {
    type Output = SingleNaNF64;

    fn add(self, rhs: f64) -> Self::Output {
        SingleNaNF64::new(self.0 + rhs)
    }
}

impl Sub for SingleNaNF64 {
    type Output = SingleNaNF64;

    fn sub(self, rhs: Self) -> Self::Output {
        SingleNaNF64::new(self.0 - rhs.0)
    }
}

impl Sub<f64> for SingleNaNF64 {
    type Output = SingleNaNF64;

    fn sub(self, rhs: f64) -> Self::Output {
        SingleNaNF64::new(self.0 - rhs)
    }
}

impl Mul for SingleNaNF64 {
    type Output = SingleNaNF64;

    fn mul(self, rhs: Self) -> Self::Output {
        SingleNaNF64::new(self.0 * rhs.0)
    }
}

impl Mul<f64> for SingleNaNF64 {
    type Output = SingleNaNF64;

    fn mul(self, rhs: f64) -> Self::Output {
        SingleNaNF64::new(self.0 * rhs)
    }
}

impl Div for SingleNaNF64 {
    type Output = SingleNaNF64;

    fn div(self, rhs: Self) -> Self::Output {
        SingleNaNF64::new(self.0 / rhs.0)
    }
}

impl Div<f64> for SingleNaNF64 {
    type Output = SingleNaNF64;

    fn div(self, rhs: f64) -> Self::Output {
        SingleNaNF64::new(self.0 / rhs)
    }
}
