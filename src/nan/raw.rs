use super::{NEG_QUIET_NAN, QUIET_NAN, SIGN_MASK};
use crate::nan::singlenan::SingleNaNF64;
use crate::utils::ArrayExt;
use either::Either;
use sptr::Strict;
use std::fmt;

/// Types that can be easily stored in a [`RawBox`]. This trait is implemented for some common
/// base types that people may want to store, that have 'obvious' ways to write them into storage
/// and can't cause immediate UB if the wrong type is read.
///
/// This means [`char`], references, and types larger than 4 aren't included, so as to not potentially
/// implement something that only works if certain assumptions are made, or is very likely to panic.
/// Pointers are included only because they're very common, and most 64-bit systems cap pointers
/// to 48-bit addresses anyways.
pub trait RawStore: Sized {
    fn to_val(self, value: &mut Value);
    fn from_val(value: &Value) -> Self;
}

impl RawStore for [u8; 6] {
    fn to_val(self, value: &mut Value) {
        value.write(self);
    }

    fn from_val(value: &Value) -> Self {
        value.read()
    }
}

impl RawStore for bool {
    fn to_val(self, value: &mut Value) {
        value.write([1].truncate_to());
    }

    fn from_val(value: &Value) -> Self {
        value.ref_value()[0] == 1
    }
}

macro_rules! int_store {
    ($ty:ty) => {
        impl RawStore for $ty {
            fn to_val(self, value: &mut Value) {
                let bytes = self.to_ne_bytes();
                value.write(bytes.truncate_to());
            }

            fn from_val(value: &Value) -> Self {
                <$ty>::from_ne_bytes(value.ref_value().truncate_to())
            }
        }
    };
}

int_store!(u8);
int_store!(u16);
int_store!(u32);

int_store!(i8);
int_store!(i16);
int_store!(i32);

fn store_ptr<P: Strict + Copy>(value: &mut Value, ptr: P) {
    #[cfg(target_pointer_width = "32")]
    {
        let val = (value.mut_val() as *mut [u8; 6])
            .cast::<*mut T>()
            .byte_offset(2);

        unsafe { val.write(self) };
    }
    #[cfg(target_pointer_width = "64")]
    {
        assert!(
            ptr.addr() <= 0x0000_FFFF_FFFF_FFFF,
            "Pointer too large to store in NaN box"
        );

        // SAFETY: We ensure pointer range will fit in 6 bytes, then mask it to match
        let val = (unsafe { value.mut_whole() } as *mut [u8; 8]).cast::<P>();

        let ptr = Strict::map_addr(ptr, |addr| {
            addr | ((value.header().into_raw() as usize) << 48)
        });

        unsafe { val.write(ptr) };
    }
}

fn load_ptr<P: Strict>(value: &Value) -> P {
    #[cfg(target_pointer_width = "32")]
    {
        let val = (value.ref_val() as *const [u8; 6])
            .cast::<P>()
            .byte_offset(2);

        unsafe { val.read() }
    }
    #[cfg(target_pointer_width = "64")]
    {
        let val = (unsafe { value.ref_whole() } as *const [u8; 8]).cast::<P>();

        let ptr = unsafe { val.read() };
        Strict::map_addr(ptr, |addr| addr & 0x0000_FFFF_FFFF_FFFF)
    }
}

impl<T> RawStore for *const T {
    fn to_val(self, value: &mut Value) {
        store_ptr::<*const T>(value, self);
    }

    fn from_val(value: &Value) -> Self {
        load_ptr::<*const T>(value)
    }
}

impl<T> RawStore for *mut T {
    fn to_val(self, value: &mut Value) {
        store_ptr::<*mut T>(value, self);
    }

    fn from_val(value: &Value) -> Self {
        load_ptr::<*mut T>(value)
    }
}

#[derive(Copy, Clone, PartialEq, Eq)]
enum TagVal {
    _P0,
    _P1,
    _P2,
    _P3,
    _P4,
    _P5,
    _P6,
    _P7,

    _N0,
    _N1,
    _N2,
    _N3,
    _N4,
    _N5,
    _N6,
    _N7,
}

#[derive(Copy, Clone, PartialEq, Eq)]
pub struct RawTag(TagVal);

impl RawTag {
    #[must_use]
    pub fn new(neg: bool, val: u8) -> RawTag {
        // SAFETY: Value truncated into range 0-7
        unsafe { Self::new_unchecked(neg, val & 0x07) }
    }

    #[must_use]
    pub fn new_checked(neg: bool, val: u8) -> Option<RawTag> {
        Some(RawTag(match (neg, val) {
            (false, 0) => TagVal::_P0,
            (false, 1) => TagVal::_P1,
            (false, 2) => TagVal::_P2,
            (false, 3) => TagVal::_P3,
            (false, 4) => TagVal::_P4,
            (false, 5) => TagVal::_P5,
            (false, 6) => TagVal::_P6,
            (false, 7) => TagVal::_P7,

            (true, 0) => TagVal::_N0,
            (true, 1) => TagVal::_N1,
            (true, 2) => TagVal::_N2,
            (true, 3) => TagVal::_N3,
            (true, 4) => TagVal::_N4,
            (true, 5) => TagVal::_N5,
            (true, 6) => TagVal::_N6,
            (true, 7) => TagVal::_N7,

            _ => return None,
        }))
    }

    /// # Safety
    ///
    /// `val` must be in the range `0..8`
    #[must_use]
    pub unsafe fn new_unchecked(neg: bool, val: u8) -> RawTag {
        RawTag(match (neg, val) {
            (false, 0) => TagVal::_P0,
            (false, 1) => TagVal::_P1,
            (false, 2) => TagVal::_P2,
            (false, 3) => TagVal::_P3,
            (false, 4) => TagVal::_P4,
            (false, 5) => TagVal::_P5,
            (false, 6) => TagVal::_P6,
            (false, 7) => TagVal::_P7,

            (true, 0) => TagVal::_N0,
            (true, 1) => TagVal::_N1,
            (true, 2) => TagVal::_N2,
            (true, 3) => TagVal::_N3,
            (true, 4) => TagVal::_N4,
            (true, 5) => TagVal::_N5,
            (true, 6) => TagVal::_N6,
            (true, 7) => TagVal::_N7,

            _ => core::hint::unreachable_unchecked(),
        })
    }

    #[must_use]
    pub fn is_neg(self) -> bool {
        matches!(
            self.0,
            TagVal::_N0
                | TagVal::_N1
                | TagVal::_N2
                | TagVal::_N3
                | TagVal::_N4
                | TagVal::_N5
                | TagVal::_N6
                | TagVal::_N7
        )
    }

    #[must_use]
    pub fn val(self) -> u8 {
        match self.0 {
            TagVal::_P0 | TagVal::_N0 => 0,
            TagVal::_P1 | TagVal::_N1 => 1,
            TagVal::_P2 | TagVal::_N2 => 2,
            TagVal::_P3 | TagVal::_N3 => 3,
            TagVal::_P4 | TagVal::_N4 => 4,
            TagVal::_P5 | TagVal::_N5 => 5,
            TagVal::_P6 | TagVal::_N6 => 6,
            TagVal::_P7 | TagVal::_N7 => 7,
        }
    }

    #[must_use]
    pub fn neg_val(self) -> (bool, u8) {
        match self.0 {
            TagVal::_P0 => (false, 0),
            TagVal::_P1 => (false, 1),
            TagVal::_P2 => (false, 2),
            TagVal::_P3 => (false, 3),
            TagVal::_P4 => (false, 4),
            TagVal::_P5 => (false, 5),
            TagVal::_P6 => (false, 6),
            TagVal::_P7 => (false, 7),
            TagVal::_N0 => (true, 0),
            TagVal::_N1 => (true, 1),
            TagVal::_N2 => (true, 2),
            TagVal::_N3 => (true, 3),
            TagVal::_N4 => (true, 4),
            TagVal::_N5 => (true, 5),
            TagVal::_N6 => (true, 6),
            TagVal::_N7 => (true, 7),
        }
    }
}

impl fmt::Debug for RawTag {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("RawTag")
            .field("neg", &self.is_neg())
            .field("val", &self.val())
            .finish()
    }
}

#[derive(Copy, Clone)]
#[repr(transparent)]
struct Header(u16);

impl Header {
    fn new(tag: RawTag) -> Header {
        let (neg, val) = tag.neg_val();
        Header(0x7FF8 | (u16::from(neg) << 15) | u16::from(val))
    }

    fn tag(self) -> RawTag {
        // SAFETY: tag is guaranteed in range 0-7, we already truncated it
        unsafe { RawTag::new_unchecked(self.get_sign(), self.get_tag()) }
    }

    fn get_sign(self) -> bool {
        self.0 & 0x8000 != 0
    }

    fn get_tag(self) -> u8 {
        (self.0 & 0x0007) as u8
    }

    fn into_raw(self) -> u16 {
        self.0
    }
}

#[derive(Copy, Clone)]
#[repr(C, align(8))]
pub struct Value {
    #[cfg(target_endian = "big")]
    header: Header,
    value: [u8; 6],
    #[cfg(target_endian = "little")]
    header: Header,
}

impl Value {
    #[must_use]
    pub fn tag(&self) -> RawTag {
        self.header.tag()
    }

    fn header(&self) -> &Header {
        &self.header
    }

    pub fn write(&mut self, val: [u8; 6]) {
        self.value = val;
    }

    #[must_use]
    pub fn read(&self) -> [u8; 6] {
        self.value
    }

    #[must_use]
    pub fn ref_value(&self) -> &[u8; 6] {
        &self.value
    }

    pub fn mut_value(&mut self) -> &mut [u8; 6] {
        &mut self.value
    }

    unsafe fn ref_whole(&self) -> &[u8; 8] {
        &*(self as *const Value).cast::<[u8; 8]>()
    }

    unsafe fn mut_whole(&mut self) -> &mut [u8; 8] {
        &mut *(self as *mut Value).cast::<[u8; 8]>()
    }
}

/// A simple 'raw' NaN-boxed type, which provides no type checking of its own,
#[repr(C)]
pub union RawBox {
    bits: u64,
    float: f64,
    val: Value,
}

impl RawBox {
    #[must_use]
    pub fn from_f64(val: f64) -> RawBox {
        match (val.is_nan(), val.is_sign_positive()) {
            (true, true) => RawBox {
                float: f64::from_bits(QUIET_NAN),
            },
            (true, false) => RawBox {
                float: f64::from_bits(NEG_QUIET_NAN),
            },
            (false, _) => RawBox { float: val },
        }
    }

    #[must_use]
    pub fn from_data(tag: RawTag, value: [u8; 6]) -> Option<RawBox> {
        if tag.val() == 0 {
            None
        } else {
            Some(RawBox {
                val: Value {
                    header: Header::new(tag),
                    value,
                },
            })
        }
    }

    #[must_use]
    pub fn from_val<T: RawStore>(tag: RawTag, val: T) -> Option<RawBox> {
        let mut out = Self::from_data(tag, [0; 6])?;
        T::to_val(val, unsafe { &mut out.val });
        Some(out)
    }

    #[must_use]
    pub fn write(tag: RawTag, f: impl FnOnce(&mut Value)) -> Option<RawBox> {
        let mut out = Self::from_data(tag, [0; 6])?;
        f(unsafe { &mut out.val });
        Some(out)
    }

    #[must_use]
    pub fn tag(&self) -> Option<RawTag> {
        if self.is_data() {
            Some(unsafe { self.val.tag() })
        } else {
            None
        }
    }

    #[must_use]
    pub fn is_f64(&self) -> bool {
        (unsafe { !self.float.is_nan() } || unsafe { self.bits & SIGN_MASK == QUIET_NAN })
    }

    #[must_use]
    pub fn is_data(&self) -> bool {
        (unsafe { self.float.is_nan() } && unsafe { self.bits & SIGN_MASK != QUIET_NAN })
    }

    #[must_use]
    pub fn ref_f64(&self) -> Option<&f64> {
        if self.is_f64() {
            // SAFETY: If we pass the check, we contain a float, and since you can't write through
            //         a &f64, can't change this to be NAN and mess it up
            Some(unsafe { &self.float })
        } else {
            None
        }
    }

    pub fn mut_f64(&mut self) -> Option<&mut SingleNaNF64> {
        if self.is_f64() {
            SingleNaNF64::from_mut(unsafe { &mut self.float })
        } else {
            None
        }
    }

    #[must_use]
    pub fn ref_data(&self) -> Option<&[u8; 6]> {
        if self.is_data() {
            // SAFETY: If we pass the check, we contain NaN-boxed data, and can safely access the
            //         tail as raw bytes
            Some(unsafe { &self.val.value })
        } else {
            None
        }
    }

    pub fn mut_data(&mut self) -> Option<&mut [u8; 6]> {
        if self.is_data() {
            // SAFETY: If we pass the check, we contain NaN-boxed data, and can safely access
            //         the tail as raw bytes
            //         We ensure tag != 0 on creation to allow this, writing all 0 bytes to data
            //         can never break our invariants.
            Some(unsafe { &mut self.val.value })
        } else {
            None
        }
    }

    pub fn into_f64(self) -> Result<f64, Self> {
        if self.is_f64() {
            // SAFETY: If we pass the check, we contain a float, and can pull it out
            Ok(unsafe { self.float })
        } else {
            Err(self)
        }
    }

    pub fn into_data(self) -> Result<(RawTag, [u8; 6]), Self> {
        if self.is_data() {
            // SAFETY: If we pass the check, we contain raw data, and can pull it out
            let val = unsafe { self.val };
            Ok((val.header.tag(), val.value))
        } else {
            Err(self)
        }
    }

    pub fn into_val<T: RawStore>(self) -> Result<(RawTag, T), Self> {
        if self.is_data() {
            let val = unsafe { &self.val };
            Ok((val.tag(), T::from_val(val)))
        } else {
            Err(self)
        }
    }

    pub fn read<T>(&self, f: impl FnOnce(&Value) -> T) -> Option<T> {
        if self.is_data() {
            let val = unsafe { &self.val };
            Some(f(val))
        } else {
            None
        }
    }

    pub fn try_read<T>(&self, f: impl FnOnce(&Value) -> Option<T>) -> Option<T> {
        if self.is_data() {
            let val = unsafe { &self.val };
            f(val)
        } else {
            None
        }
    }

    #[must_use]
    pub fn into_f64_or_raw(self) -> Either<f64, (RawTag, [u8; 6])> {
        if self.is_f64() {
            Either::Left(unsafe { self.float })
        } else {
            let val = unsafe { self.val };
            Either::Right((val.header.tag(), val.value))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn size_check() {
        assert_eq!(core::mem::size_of::<RawBox>(), 8);
    }

    #[test]
    fn test_roundtrip_float() {
        let a = RawBox::from_f64(1.0);
        assert_eq!(a.into_f64().ok(), Some(1.0));

        let b = RawBox::from_f64(-1.0);
        assert_eq!(b.into_f64().ok(), Some(-1.0));

        let c = RawBox::from_f64(f64::NAN);
        assert!(c
            .into_f64()
            .ok()
            .is_some_and(|val| val.is_nan() && val.is_sign_positive()));

        let d = RawBox::from_f64(-f64::NAN);
        assert!(d
            .into_f64()
            .ok()
            .is_some_and(|val| val.is_nan() && val.is_sign_negative()));
    }

    #[test]
    fn test_roundtrip_raw() {
        let a = RawBox::from_data(RawTag::new(false, 1), [0; 6]).unwrap();
        assert_eq!(a.into_data().ok(), Some((RawTag::new(false, 1), [0; 6])));

        let b = RawBox::from_data(RawTag::new(true, 1), [0; 6]).unwrap();
        assert_eq!(b.into_data().ok(), Some((RawTag::new(true, 1), [0; 6])));

        let c = RawBox::from_data(RawTag::new(false, 7), [0, 0, 0, 0, 0, 1]).unwrap();
        assert_eq!(
            c.into_data().ok(),
            Some((RawTag::new(false, 7), [0, 0, 0, 0, 0, 1]))
        );

        let d = RawBox::from_data(RawTag::new(false, 4), [0x80, 0, 0, 0, 0, 0]).unwrap();
        assert_eq!(
            d.into_data().ok(),
            Some((RawTag::new(false, 4), [0x80, 0, 0, 0, 0, 0]))
        );
    }

    #[test]
    fn test_invalid_raw() {
        let a = RawBox::from_data(RawTag::new(false, 0), [0; 6]);
        assert!(matches!(a, None));

        let b = RawBox::from_data(RawTag::new(true, 0), [0; 6]);
        assert!(matches!(b, None));

        let c = RawBox::from_data(RawTag::new(false, 0), [0, 0, 0, 0, 0, 1]);
        assert!(matches!(c, None));

        let d = RawBox::from_data(RawTag::new(false, 0), [0x80, 0, 0, 0, 0, 0]);
        assert!(matches!(d, None));
    }

    #[test]
    fn test_roundtrip_u32() {
        let a = RawBox::from_val(RawTag::new(false, 1), 0u32).unwrap();
        assert!(matches!(a.into_val().ok(), Some((_, 0u32))));

        let b = RawBox::from_val(RawTag::new(false, 1), 1u32).unwrap();
        assert!(matches!(b.into_val().ok(), Some((_, 1u32))));

        let c = RawBox::from_val(RawTag::new(false, 1), 0xFFFF_FFFFu32).unwrap();
        assert!(matches!(c.into_val().ok(), Some((_, 0xFFFF_FFFFu32))));
    }

    #[test]
    fn test_roundtrip_i32() {
        let a = RawBox::from_val(RawTag::new(false, 1), 0i32).unwrap();
        assert!(matches!(a.into_val().ok(), Some((_, 0i32))));

        let b = RawBox::from_val(RawTag::new(false, 1), 1i32).unwrap();
        assert!(matches!(b.into_val().ok(), Some((_, 1i32))));

        let c = RawBox::from_val(RawTag::new(false, 1), -1i32).unwrap();
        assert!(matches!(c.into_val().ok(), Some((_, -1i32))));
    }

    #[test]
    fn test_roundtrip_ptr() {
        let mut data = Box::new(1);
        let ptr = &mut *data as *mut i32;

        let a = RawBox::from_val(RawTag::new(false, 1), ptr).unwrap();
        let out = a.into_val::<*mut i32>().ok().unwrap();
        assert_eq!(out, (RawTag::new(false, 1), ptr));

        // Check that we can still read/write through the pointer
        let ptr = out.1;
        assert_eq!(unsafe { *ptr }, 1);
        unsafe { *ptr = 2 };

        assert_eq!(*data, 2);
    }
}
