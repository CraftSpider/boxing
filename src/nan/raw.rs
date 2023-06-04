use super::{NEG_QUIET_NAN, QUIET_NAN, SIGN_MASK};
use crate::nan::singlenan::SingleNaNF64;
use crate::utils::ArrayExt;
use sptr::Strict;
use std::fmt;
use std::mem::ManuallyDrop;
use std::num::NonZeroU8;

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
        value.set_data(self);
    }

    fn from_val(value: &Value) -> Self {
        *value.data()
    }
}

impl RawStore for bool {
    fn to_val(self, value: &mut Value) {
        value.set_data([1].truncate_to());
    }

    fn from_val(value: &Value) -> Self {
        value.data()[0] == 1
    }
}

macro_rules! int_store {
    ($ty:ty) => {
        impl RawStore for $ty {
            fn to_val(self, value: &mut Value) {
                let bytes = self.to_ne_bytes();
                value.set_data(bytes.truncate_to());
            }

            fn from_val(value: &Value) -> Self {
                <$ty>::from_ne_bytes(value.data().truncate_to())
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
        let val = (unsafe { value.whole_mut() } as *mut [u8; 8]).cast::<P>();

        let ptr = Strict::map_addr(ptr, |addr| {
            addr | (usize::from(value.header().into_raw()) << 48)
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
        let val = (unsafe { value.whole() } as *const [u8; 8]).cast::<P>();

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
    _P1,
    _P2,
    _P3,
    _P4,
    _P5,
    _P6,
    _P7,

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
    pub fn new(neg: bool, val: NonZeroU8) -> RawTag {
        // SAFETY: Value truncated into range 0-7
        unsafe { Self::new_unchecked(neg, val.get() & 0x07) }
    }

    #[must_use]
    pub fn new_checked(neg: bool, val: u8) -> Option<RawTag> {
        Some(RawTag(match (neg, val) {
            (false, 1) => TagVal::_P1,
            (false, 2) => TagVal::_P2,
            (false, 3) => TagVal::_P3,
            (false, 4) => TagVal::_P4,
            (false, 5) => TagVal::_P5,
            (false, 6) => TagVal::_P6,
            (false, 7) => TagVal::_P7,

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
    /// `val` must be in the range `1..8`
    #[must_use]
    pub unsafe fn new_unchecked(neg: bool, val: u8) -> RawTag {
        RawTag(match (neg, val) {
            (false, 1) => TagVal::_P1,
            (false, 2) => TagVal::_P2,
            (false, 3) => TagVal::_P3,
            (false, 4) => TagVal::_P4,
            (false, 5) => TagVal::_P5,
            (false, 6) => TagVal::_P6,
            (false, 7) => TagVal::_P7,

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
        matches!(self.0, |TagVal::_N1| TagVal::_N2
            | TagVal::_N3
            | TagVal::_N4
            | TagVal::_N5
            | TagVal::_N6
            | TagVal::_N7)
    }

    #[must_use]
    pub fn val(self) -> NonZeroU8 {
        match self.0 {
            TagVal::_P1 | TagVal::_N1 => NonZeroU8::new(1).unwrap(),
            TagVal::_P2 | TagVal::_N2 => NonZeroU8::new(2).unwrap(),
            TagVal::_P3 | TagVal::_N3 => NonZeroU8::new(3).unwrap(),
            TagVal::_P4 | TagVal::_N4 => NonZeroU8::new(4).unwrap(),
            TagVal::_P5 | TagVal::_N5 => NonZeroU8::new(5).unwrap(),
            TagVal::_P6 | TagVal::_N6 => NonZeroU8::new(6).unwrap(),
            TagVal::_P7 | TagVal::_N7 => NonZeroU8::new(7).unwrap(),
        }
    }

    #[must_use]
    pub fn neg_val(self) -> (bool, u8) {
        match self.0 {
            TagVal::_P1 => (false, 1),
            TagVal::_P2 => (false, 2),
            TagVal::_P3 => (false, 3),
            TagVal::_P4 => (false, 4),
            TagVal::_P5 => (false, 5),
            TagVal::_P6 => (false, 6),
            TagVal::_P7 => (false, 7),
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

#[derive(Copy, Clone, Debug, PartialEq)]
#[repr(transparent)]
struct Header(u16);

impl Header {
    fn new(tag: RawTag) -> Header {
        let (neg, val) = tag.neg_val();
        Header(0x7FF8 | (u16::from(neg) << 15) | u16::from(val))
    }

    fn tag(self) -> RawTag {
        // SAFETY: tag is guaranteed in range 1-7, we already truncated it and 0 never happens
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

#[derive(Clone, Debug, PartialEq)]
#[repr(C, align(8))]
pub struct Value {
    #[cfg(target_endian = "big")]
    header: Header,
    data: [u8; 6],
    #[cfg(target_endian = "little")]
    header: Header,
}

impl Value {
    pub fn new(tag: RawTag, data: [u8; 6]) -> Value {
        Value {
            header: Header::new(tag),
            data,
        }
    }

    pub fn empty(tag: RawTag) -> Value {
        Value::new(tag, [0; 6])
    }

    pub fn store<T: RawStore>(tag: RawTag, val: T) -> Value {
        let mut v = Value::new(tag, [0; 6]);
        T::to_val(val, &mut v);
        v
    }

    pub fn load<T: RawStore>(self) -> T {
        T::from_val(&self)
    }

    #[must_use]
    pub fn tag(&self) -> RawTag {
        self.header.tag()
    }

    fn header(&self) -> &Header {
        &self.header
    }

    pub fn set_data(&mut self, val: [u8; 6]) {
        self.data = val;
    }

    #[must_use]
    pub fn data(&self) -> &[u8; 6] {
        &self.data
    }

    #[must_use]
    pub fn data_mut(&mut self) -> &mut [u8; 6] {
        &mut self.data
    }

    #[must_use]
    unsafe fn whole(&self) -> &[u8; 8] {
        &*(self as *const Value).cast::<[u8; 8]>()
    }

    #[must_use]
    unsafe fn whole_mut(&mut self) -> &mut [u8; 8] {
        &mut *(self as *mut Value).cast::<[u8; 8]>()
    }
}

// TODO: Implement Debug
/// A simple 'raw' NaN-boxed type, which provides no type checking of its own,
#[repr(C)]
pub union RawBox {
    float: f64,
    value: ManuallyDrop<Value>,

    // Used for comparisons
    bits: u64,
    // Used when cloning, to preserve provenance
    ptr: *const (),
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
    pub fn from_value(value: Value) -> RawBox {
        RawBox {
            value: ManuallyDrop::new(value),
        }
    }

    #[must_use]
    pub fn tag(&self) -> Option<RawTag> {
        if self.is_value() {
            Some(unsafe { self.value.tag() })
        } else {
            None
        }
    }

    #[must_use]
    pub fn is_float(&self) -> bool {
        (unsafe { !self.float.is_nan() } || unsafe { self.bits & SIGN_MASK == QUIET_NAN })
    }

    #[must_use]
    pub fn is_value(&self) -> bool {
        (unsafe { self.float.is_nan() } && unsafe { self.bits & SIGN_MASK != QUIET_NAN })
    }

    #[must_use]
    pub fn float(&self) -> Option<&f64> {
        if self.is_float() {
            // SAFETY: If we pass the check, we contain a float, and since you can't write through
            //         a &f64, can't change this to be NAN and mess it up
            Some(unsafe { &self.float })
        } else {
            None
        }
    }

    #[must_use]
    pub fn float_mut(&mut self) -> Option<&mut SingleNaNF64> {
        if self.is_float() {
            SingleNaNF64::from_mut(unsafe { &mut self.float })
        } else {
            None
        }
    }

    #[must_use]
    pub fn value(&self) -> Option<&Value> {
        if self.is_value() {
            // SAFETY: If we pass the check, we contain NaN-boxed data, and can safely ourselves as
            //         a data value
            Some(unsafe { &self.value })
        } else {
            None
        }
    }

    #[must_use]
    pub fn value_mut(&mut self) -> Option<&mut Value> {
        if self.is_value() {
            // SAFETY: If we pass the check, we contain NaN-boxed data, and can safely access
            //         the tail as raw bytes
            //         We ensure tag != 0 on creation to allow this, writing all 0 bytes to data
            //         can never break our invariants.
            Some(unsafe { &mut self.value })
        } else {
            None
        }
    }

    pub fn into_float(self) -> Result<f64, Self> {
        if self.is_float() {
            // SAFETY: If we pass the check, we contain a float, and can pull it out
            Ok(unsafe { self.float })
        } else {
            Err(self)
        }
    }

    pub fn into_value(self) -> Result<Value, Self> {
        if self.is_value() {
            // SAFETY: If we pass the check, we contain raw data, and can pull it out
            Ok(ManuallyDrop::into_inner(unsafe { self.value }))
        } else {
            Err(self)
        }
    }
}

impl Clone for RawBox {
    fn clone(&self) -> Self {
        RawBox {
            ptr: unsafe { self.ptr },
        }
    }
}

impl fmt::Debug for RawBox {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.float() {
            Some(val) => f.debug_tuple("RawBox::Float").field(val).finish(),
            None => {
                let val = self.value().unwrap();

                f.debug_struct("RawBox::Data")
                    .field("tag", &val.tag())
                    .field("data", val.data())
                    .finish()
            }
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
        assert_eq!(a.into_float().ok(), Some(1.0));

        let b = RawBox::from_f64(-1.0);
        assert_eq!(b.into_float().ok(), Some(-1.0));

        let c = RawBox::from_f64(f64::NAN);
        assert!(c
            .into_float()
            .is_ok_and(|val| val.is_nan() && val.is_sign_positive()));

        let d = RawBox::from_f64(-f64::NAN);
        assert!(d
            .into_float()
            .is_ok_and(|val| val.is_nan() && val.is_sign_negative()));
    }

    #[test]
    fn test_roundtrip_value() {
        let one = NonZeroU8::new(1).unwrap();
        let four = NonZeroU8::new(4).unwrap();
        let seven = NonZeroU8::new(7).unwrap();

        let a = RawBox::from_value(Value::empty(RawTag::new(false, one)));
        assert_eq!(
            a.into_value().ok(),
            Some(Value::empty(RawTag::new(false, one)))
        );

        let b = RawBox::from_value(Value::empty(RawTag::new(true, seven)));
        assert_eq!(
            b.into_value().ok(),
            Some(Value::empty(RawTag::new(true, seven)))
        );

        let c = RawBox::from_value(Value::new(RawTag::new(false, seven), [0, 0, 0, 0, 0, 1]));
        assert_eq!(
            c.into_value().ok(),
            Some(Value::new(RawTag::new(false, seven), [0, 0, 0, 0, 0, 1]))
        );

        let d = RawBox::from_value(Value::new(RawTag::new(false, four), [0x80, 0, 0, 0, 0, 0]));
        assert_eq!(
            d.into_value().ok(),
            Some(Value::new(RawTag::new(false, four), [0x80, 0, 0, 0, 0, 0]))
        );
    }

    #[test]
    fn test_roundtrip_u32() {
        let one = NonZeroU8::MIN;

        let a = RawBox::from_value(Value::store(RawTag::new(false, one), 0u32));
        assert_eq!(a.into_value().unwrap().load::<u32>(), 0u32);

        let b = RawBox::from_value(Value::store(RawTag::new(false, one), 1u32));
        assert_eq!(b.into_value().unwrap().load::<u32>(), 1u32);

        let c = RawBox::from_value(Value::store(RawTag::new(false, one), 0xFFFF_FFFFu32));
        assert_eq!(c.into_value().unwrap().load::<u32>(), 0xFFFF_FFFFu32);
    }

    #[test]
    fn test_roundtrip_i32() {
        let one = NonZeroU8::MIN;

        let a = RawBox::from_value(Value::store(RawTag::new(false, one), 0i32));
        assert_eq!(a.into_value().unwrap().load::<i32>(), 0i32);

        let b = RawBox::from_value(Value::store(RawTag::new(false, one), 1i32));
        assert_eq!(b.into_value().unwrap().load::<i32>(), 1i32);

        let c = RawBox::from_value(Value::store(RawTag::new(false, one), -1i32));
        assert_eq!(c.into_value().unwrap().load::<i32>(), -1i32);
    }

    #[test]
    fn test_roundtrip_ptr() {
        let mut data = Box::new(1);
        let ptr = &mut *data as *mut i32;

        let a = RawBox::from_value(Value::store(RawTag::new(false, NonZeroU8::MIN), ptr));
        let new_ptr = a.into_value().unwrap().load::<*mut i32>();
        assert_eq!(new_ptr, ptr);

        // Check that we can still read/write through the pointer
        assert_eq!(unsafe { *new_ptr }, 1);
        unsafe { *new_ptr = 2 };

        assert_eq!(*data, 2);
    }

    #[test]
    fn test_clone_ptr() {
        // This test is mostly for miri - it ensures we preserve provenance across cloning the underlying box

        let val = 1;

        let a = RawBox::from_value(Value::store(
            RawTag::new(false, NonZeroU8::MIN),
            &val as *const i32,
        ));

        let b = a.clone();

        let ptr = b.into_value().unwrap().load::<*const i32>();
        assert_eq!(unsafe { *ptr }, 1);
    }

    #[test]
    fn test_clone_f64() {
        let a = RawBox::from_f64(1.0);
        let b = a.clone();
        assert_eq!(b.into_float().ok(), Some(1.0));
    }
}
