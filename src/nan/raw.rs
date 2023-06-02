use std::fmt;
use either::Either;
use super::{SIGN_MASK, QUIET_NAN, NEG_QUIET_NAN};

pub trait NaNStore: Sized {
    fn to_bytes(self) -> Option<[u8; 6]>;
    fn from_bytes(bytes: [u8; 6]) -> Option<Self>;
}

impl NaNStore for bool {
    fn to_bytes(self) -> Option<[u8; 6]> {
        Some([1, 0, 0, 0, 0, 0])
    }

    fn from_bytes(bytes: [u8; 6]) -> Option<Self> {
        Some(bytes[0] == 1)
    }
}

impl NaNStore for u32 {
    fn to_bytes(self) -> Option<[u8; 6]> {
        let bytes = self.to_ne_bytes();
        Some([bytes[0], bytes[1], bytes[2], bytes[3], 0, 0])
    }

    fn from_bytes(bytes: [u8; 6]) -> Option<Self> {
        Some(u32::from_ne_bytes([bytes[0], bytes[1], bytes[2], bytes[3]]))
    }
}

impl NaNStore for i32 {
    fn to_bytes(self) -> Option<[u8; 6]> {
        let bytes = self.to_ne_bytes();
        Some([bytes[0], bytes[1], bytes[2], bytes[3], 0, 0])
    }

    fn from_bytes(bytes: [u8; 6]) -> Option<Self> {
        Some(i32::from_ne_bytes([bytes[0], bytes[1], bytes[2], bytes[3]]))
    }
}

impl NaNStore for char {
    fn to_bytes(self) -> Option<[u8; 6]> {
        u32::to_bytes(self as u32)
    }

    fn from_bytes(bytes: [u8; 6]) -> Option<Self> {
        u32::from_bytes(bytes)
            .and_then(char::from_u32)
    }
}

// TODO: API that supports strict provenance better
impl<T> NaNStore for *mut T {
    fn to_bytes(self) -> Option<[u8; 6]> {
        let val = self as usize;
        #[cfg(target_pointer_width = "32")]
        return u32::to_bytes(val as u32);
        #[cfg(target_pointer_width = "64")]
        {
            if val > 0x0000_FFFF_FFFF_FFFF {
                return None;
            }

            let bytes = val.to_ne_bytes();
            return Some([bytes[0], bytes[1], bytes[2], bytes[3], bytes[4], bytes[5]]);
        }
    }

    fn from_bytes(bytes: [u8; 6]) -> Option<Self> {
        #[cfg(target_pointer_width = "32")]
        return u32::from_bytes(bytes) as usize as *mut T;
        #[cfg(target_pointer_width = "64")]
        {
            let val = usize::from_ne_bytes([bytes[0], bytes[1], bytes[2], bytes[3], bytes[4], bytes[5], 0, 0]);
            return Some(val as *mut T);
        }
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
    pub fn new(neg: bool, val: u8) -> Option<RawTag> {
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

    pub fn new_truncate(neg: bool, val: u8) -> RawTag {
        // SAFETY: Value truncated into range 0-7
        unsafe { Self::new_unchecked(neg, val & 0x07) }
    }

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

    pub fn is_neg(self) -> bool {
        matches!(self.0, TagVal::_N0 | TagVal::_N1 | TagVal::_N2 | TagVal::_N3 | TagVal::_N4 | TagVal::_N5 | TagVal::_N6 | TagVal::_N7)
    }

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
        Header(0x7FF8 | ((neg as u16) << 15) | val as u16)
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
}

#[derive(Copy, Clone)]
#[repr(C, align(8))]
struct Value {
    #[cfg(target_endian = "big")]
    header: Header,
    value: [u8; 6],
    #[cfg(target_endian = "little")]
    header: Header,
}

/// A simple 'raw' NaN-boxed type, which provides no type checking of its own,
#[derive(Copy, Clone)]
#[repr(C)]
pub union RawBox {
    bits: u64,
    float: f64,
    val: Value,
}


impl RawBox {
    pub fn from_f64(val: f64) -> RawBox {
        match (val.is_nan(), val.is_sign_positive()) {
            (true, true) => RawBox { float: f64::from_bits(QUIET_NAN) },
            (true, false) => RawBox { float: f64::from_bits(NEG_QUIET_NAN) },
            (false, _) => RawBox { float: val },
        }
    }

    pub fn from_data(tag: RawTag, value: [u8; 6]) -> Option<RawBox> {
        if value.iter().all(|v| *v == 0) && tag.val() == 0 {
            None
        } else {
            Some(RawBox { val: Value { header: Header::new(tag), value } })
        }
    }

    pub fn from_val<T: NaNStore>(tag: RawTag, val: T) -> Option<RawBox> {
        Self::from_data(tag, val.to_bytes()?)
    }

    pub fn is_f64(self) -> bool {
        (unsafe { !self.float.is_nan() } || unsafe { self.bits & SIGN_MASK == QUIET_NAN })
    }

    pub fn is_data(self) -> bool {
        (unsafe { self.float.is_nan() } && unsafe { self.bits & SIGN_MASK != QUIET_NAN })
    }

    pub fn into_f64(self) -> Option<f64> {
        if self.is_f64() {
            Some(unsafe { self.float })
        } else {
            None
        }
    }

    pub fn into_data(self) -> Option<(RawTag, [u8; 6])> {
        if self.is_data() {
            let val = unsafe { self.val };
            Some((val.header.tag(), val.value))
        } else {
            None
        }
    }

    pub fn into_val<T: NaNStore>(self) -> Option<(RawTag, T)> {
        let data = self.into_data()?;
        Some((data.0, T::from_bytes(data.1)?))
    }

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
        assert_eq!(a.into_f64(), Some(1.0));

        let b = RawBox::from_f64(-1.0);
        assert_eq!(b.into_f64(), Some(-1.0));

        let c = RawBox::from_f64(f64::NAN);
        assert!(c.into_f64().is_some_and(|val| val.is_nan() && val.is_sign_positive()));

        let d = RawBox::from_f64(-f64::NAN);
        assert!(d.into_f64().is_some_and(|val| val.is_nan() && val.is_sign_negative()));
    }

    #[test]
    fn test_roundtrip_raw() {
        let a = RawBox::from_data(RawTag::new_truncate(false, 1), [0; 6])
            .unwrap();
        assert_eq!(a.into_data(), Some((RawTag::new_truncate(false, 1), [0; 6])));

        let b = RawBox::from_data(RawTag::new_truncate(true, 1), [0; 6])
            .unwrap();
        assert_eq!(b.into_data(), Some((RawTag::new_truncate(true, 1), [0; 6])));

        let c = RawBox::from_data(RawTag::new_truncate(false, 0), [0, 0, 0, 0, 0, 1])
            .unwrap();
        assert_eq!(c.into_data(), Some((RawTag::new_truncate(false, 0), [0, 0, 0, 0, 0, 1])));

        let d = RawBox::from_data(RawTag::new_truncate(false, 0), [0x80, 0, 0, 0, 0, 0])
            .unwrap();
        assert_eq!(d.into_data(), Some((RawTag::new_truncate(false, 0), [0x80, 0, 0, 0, 0, 0])));
    }

    #[test]
    fn test_invalid_raw() {
        let a = RawBox::from_data(RawTag::new_truncate(false, 0), [0; 6]);
        assert!(matches!(a, None));

        let b = RawBox::from_data(RawTag::new_truncate(true, 0), [0; 6]);
        assert!(matches!(b, None));
    }

    #[test]
    fn test_roundtrip_u32() {
        let a = RawBox::from_val(RawTag::new_truncate(false, 1), 0u32)
            .unwrap();
        assert!(matches!(a.into_val(), Some((_, 0u32))));

        let b = RawBox::from_val(RawTag::new_truncate(false, 1), 1u32)
            .unwrap();
        assert!(matches!(b.into_val(), Some((_, 1u32))));

        let c = RawBox::from_val(RawTag::new_truncate(false, 1), 0xFFFF_FFFFu32)
            .unwrap();
        assert!(matches!(c.into_val(), Some((_, 0xFFFF_FFFFu32))));
    }

    #[test]
    fn test_roundtrip_i32() {
        let a = RawBox::from_val(RawTag::new_truncate(false, 1), 0i32)
            .unwrap();
        assert!(matches!(a.into_val(), Some((_, 0i32))));

        let b = RawBox::from_val(RawTag::new_truncate(false, 1), 1i32)
            .unwrap();
        assert!(matches!(b.into_val(), Some((_, 1i32))));

        let c = RawBox::from_val(RawTag::new_truncate(false, 1), -1i32)
            .unwrap();
        assert!(matches!(c.into_val(), Some((_, -1i32))));
    }
}
