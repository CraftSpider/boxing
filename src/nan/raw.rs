//! A base-level sound implementation of a NaN Box, capable of storing pointers and integer values,
//! while providing minimal overhead. An effective primitive for implementing more usage-specific
//! boxes on top of.

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
/// This means [`char`], references, and most types larger than 4 aren't included, so as to not
/// potentially implement something that only works if certain assumptions are made, or is very
/// likely to panic. Pointers are included only because they're very common, and most 64-bit systems
/// cap pointers to 48-bit addresses anyways.
pub trait RawStore: Sized {
    /// Store an instance of this type into a [`Value`]. This must always be sound, no matter the
    /// value of `self`.
    fn to_val(self, value: &mut Value);

    /// Read an instance of this type out of a [`Value`]. This must always be sound, even if the
    /// `Value` actually stores an instance of a different type.
    fn from_val(value: &Value) -> Self;
}

impl RawStore for [u8; 6] {
    #[inline]
    fn to_val(self, value: &mut Value) {
        value.set_data(self);
    }

    #[inline]
    fn from_val(value: &Value) -> Self {
        *value.data()
    }
}

impl RawStore for bool {
    #[inline]
    fn to_val(self, value: &mut Value) {
        value.set_data([1].truncate_to());
    }

    #[inline]
    fn from_val(value: &Value) -> Self {
        value.data()[0] == 1
    }
}

macro_rules! int_store {
    ($ty:ty) => {
        impl RawStore for $ty {
            #[inline]
            fn to_val(self, value: &mut Value) {
                let bytes = self.to_ne_bytes();
                value.set_data(bytes.truncate_to());
            }

            #[inline]
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

        // SAFETY: We ensure pointer range will fit in 6 bytes, then mask it to match required NaN header rules
        let val = (unsafe { value.whole_mut() } as *mut [u8; 8]).cast::<P>();

        let ptr = Strict::map_addr(ptr, |addr| {
            addr | (usize::from(value.header().into_raw()) << 48)
        });

        // SAFETY: The pointer was derived from a valid mutable reference, and is guaranteed aligned
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
        // SAFETY: We promise to use the byte range carefully
        let val = (unsafe { value.whole() } as *const [u8; 8]).cast::<P>();

        // SAFETY: The pointer returned by `whole` is guaranteed 8-byte aligned
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

/// The 'tag' of a [`RawBox`] - this is the sign bit and 3 unused bits of the top two bytes in an
/// [`f64`]. The sign bit may be either true or false, but the 3 bit value will never be `0`, so as
/// to prevent possible errors where an all-zero stored value becomes identical to the standard
/// `NaN` used by floats.
#[derive(Copy, Clone, PartialEq, Eq)]
pub struct RawTag(TagVal);

impl RawTag {
    /// Create a new tag from a sign bit and a trailing tag value. If the provided value is greater
    /// than 7, it will be masked by `0b111` to convert it into the range `1..8`.
    #[inline]
    #[must_use]
    pub fn new(neg: bool, val: NonZeroU8) -> RawTag {
        // SAFETY: Value truncated into range 0-7
        unsafe { Self::new_unchecked(neg, val.get() & 0x07) }
    }

    /// Create a new tag from a sign bit and a trailing tag value. If the provided value is outside
    /// the range `1..8`, `None` will be returned.
    #[inline]
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

    /// Create a new tag from a sign bit and a trailing tag value, performing no validation.
    ///
    /// # Safety
    ///
    /// `val` must be in the range `1..8`
    #[inline]
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

            // SAFETY: Caller contract requires val is in range 1..8, so this is never hit
            _ => unsafe { core::hint::unreachable_unchecked() },
        })
    }

    /// Return sign bit of this tag
    #[inline]
    #[must_use]
    pub fn is_neg(self) -> bool {
        matches!(self.0, |TagVal::_N1| TagVal::_N2
            | TagVal::_N3
            | TagVal::_N4
            | TagVal::_N5
            | TagVal::_N6
            | TagVal::_N7)
    }

    /// Return the trailing value of this tag. The value is guaranteed to be in the range `1..8`.
    #[inline]
    #[must_use]
    pub fn val(self) -> NonZeroU8 {
        match self.0 {
            TagVal::_P1 | TagVal::_N1 => NonZeroU8::MIN,
            TagVal::_P2 | TagVal::_N2 => NonZeroU8::MIN.saturating_add(1),
            TagVal::_P3 | TagVal::_N3 => NonZeroU8::MIN.saturating_add(2),
            TagVal::_P4 | TagVal::_N4 => NonZeroU8::MIN.saturating_add(3),
            TagVal::_P5 | TagVal::_N5 => NonZeroU8::MIN.saturating_add(4),
            TagVal::_P6 | TagVal::_N6 => NonZeroU8::MIN.saturating_add(5),
            TagVal::_P7 | TagVal::_N7 => NonZeroU8::MIN.saturating_add(6),
        }
    }

    /// Return the combination sign bit and trailing value of this tag. The value is guaranteed to
    /// be in the range `1..8`.
    #[inline]
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
    #[inline]
    fn new(tag: RawTag) -> Header {
        let (neg, val) = tag.neg_val();
        Header(0x7FF8 | (u16::from(neg) << 15) | u16::from(val))
    }

    #[inline]
    fn tag(self) -> RawTag {
        // SAFETY: tag is guaranteed in range 1-7, we already truncated it and 0 never happens
        unsafe { RawTag::new_unchecked(self.get_sign(), self.get_tag()) }
    }

    #[inline]
    fn get_sign(self) -> bool {
        self.0 & 0x8000 != 0
    }

    #[inline]
    fn get_tag(self) -> u8 {
        (self.0 & 0x0007) as u8
    }

    #[inline]
    fn into_raw(self) -> u16 {
        self.0
    }
}

/// A non-float value stored in a NaN Box. This encompasses both the 'tag' stored in the top two
/// bytes and the trailing 6-byte stored value.
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
    /// Create a new `Value` with the specified tag and contained data.
    #[inline]
    pub fn new(tag: RawTag, data: [u8; 6]) -> Value {
        Value {
            header: Header::new(tag),
            data,
        }
    }

    /// Create a new `Value` with the specified tag and all-zero contained data.
    #[inline]
    pub fn empty(tag: RawTag) -> Value {
        Value::new(tag, [0; 6])
    }

    /// Create a new `Value` with the specified tag, and containing the provided value.
    pub fn store<T: RawStore>(tag: RawTag, val: T) -> Value {
        let mut v = Value::new(tag, [0; 6]);
        T::to_val(val, &mut v);
        v
    }

    /// Load the specified type out of this `Value`. This performs no checking of the tag.
    pub fn load<T: RawStore>(self) -> T {
        T::from_val(&self)
    }

    /// Retrieve the [`RawTag`] of this `Value`. Downstream users should generally check this before
    /// calling [`load`](Self::load), as this type doesn't actually handle ensuring stored and
    /// loaded tag values match.
    #[inline]
    #[must_use]
    pub fn tag(&self) -> RawTag {
        self.header.tag()
    }

    #[inline]
    fn header(&self) -> &Header {
        &self.header
    }

    /// Set the contained data to the provided byte array
    #[inline]
    pub fn set_data(&mut self, val: [u8; 6]) {
        self.data = val;
    }

    /// Retrieve the data stored in this value as a byte array.
    ///
    /// # Alignment
    ///
    /// The byte array is guaranteed 2-byte aligned on all systems, and 4 byte aligned at either the
    /// start or at 2-byte offset depending on whether the system is little or big endian.
    #[inline]
    #[must_use]
    pub fn data(&self) -> &[u8; 6] {
        &self.data
    }

    /// Retrieve the data stored in this value as a mutable byte array.
    ///
    /// # Alignment
    /// The byte array is guaranteed 2-byte aligned on all systems, and 4 byte aligned at either the
    /// start or at 2-byte offset depending on whether the system is little or big endian.
    #[inline]
    #[must_use]
    pub fn data_mut(&mut self) -> &mut [u8; 6] {
        &mut self.data
    }

    /// This provides access to the whole `Value` as a byte array, which will be 8-byte aligned and
    /// filled with a valid `Value` (See the documentation on [`RawBox`] for more details on the
    /// exact layout)
    ///
    /// # Safety
    ///
    /// Strictly, this function is safe, as it doesn't allow mutation, but it is marked unsafe in
    /// combination with [`whole_mut`](Self::whole_mut) - the return of this value is guaranteed a
    /// valid value to write into the pointer returned by [`whole_mut`](Self::whole_mut). If you
    /// only need access to the 6 data bytes, prefer [`data`](Self::data)
    #[inline]
    #[must_use]
    pub unsafe fn whole(&self) -> &[u8; 8] {
        let ptr = (self as *const Value).cast::<[u8; 8]>();
        // SAFETY: `Value` contains no padding bytes, and is exactly 8 bytes long
        unsafe { &*ptr }
    }

    /// This provides access to the whole `Value` as a mutable byte array, which will be 8-byte
    /// aligned and filled with a valid `Value` (See the documentation on [`RawBox`] for more
    /// details on the exact layout)
    ///
    /// # Safety
    ///
    /// Any value written to this byte array must be a valid `Value`. This means the whole array,
    /// interpreted as a native-endian float, must be a `NaN`, and the 'tag' bits must be non-zero.
    /// There are no requirements on the value of the other 6 bytes. If you only need access to
    /// those bytes, prefer [`data_mut`](Self::data_mut).
    #[inline]
    #[must_use]
    pub unsafe fn whole_mut(&mut self) -> &mut [u8; 8] {
        let ptr = (self as *mut Value).cast::<[u8; 8]>();
        // SAFETY: `Value` contains no padding bytes, and is exactly 8 bytes long
        unsafe { &mut *ptr }
    }
}

/// A simple 'raw' NaN-boxed type, which provides no type checking of its own, but acts as a
/// primitive for easily implementing checked NaN Boxes on top of it.
///
/// # Layout
///
/// The contained value is laid out the same as an `f64` at minimum - 8 byte alignment, and reading
/// it as a float will always return either a correctly stored float value or NaN.
///
/// When storing a `NaN` float, it will be normalized into either `0x7FF8_0000_0000_0000` or
/// `0xFFF8_0000_0000_0000`, preserving only the sign bit of the provided value. All other float
/// values will be stored 'as-is'.
///
/// Non-float values will be any quiet `NaN` float value that has non-zero bits in the trailing 51
/// bit significand. This specific implementation requires that at least one of the first three bits,
/// which act as a 'tag' for determining the type of the remaining data normally, be set.
///
/// # Limitations
///
/// This type attempts to impose a minimal set of limitations to allow downstream users as much
/// freedom as possible, however some trade-off decisions must be made.
///
/// - All NaN float values are normalized to either `0x7FF8_0000_0000_0000` or `0xFFF8_0000_0000_0000`
///   - This preserves the signedness of a `NaN`, but otherwise discards any information. This should
///     be a fairly obvious necessity for function
/// - The stored 'tag' in the first two bytes of the `NaN` must have a non-zero trailing value
///   - This allows returning mutable references to contained values in many situations - without
///     this restriction, returning a mutable reference to the contained [`Value`] would require
///     a lot more checks, as setting the value to all-zero byte pattern could turn it into a valid
///     float NaN
///
#[repr(C)]
pub union RawBox {
    float: f64,
    value: ManuallyDrop<Value>,

    // Used for comparisons
    bits: u64,
    // Used when cloning, to preserve provenance
    #[cfg(target_pointer_width = "64")]
    ptr: *const (),
    #[cfg(target_pointer_width = "32")]
    ptr: (u32, *const ()),
}

impl RawBox {
    /// Create a new [`RawBox`] from a float value. All `NaN` float values will be normalized as
    /// specified in the layout section of the type documentation.
    #[inline]
    #[must_use]
    pub fn from_float(val: f64) -> RawBox {
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

    /// Create a new [`RawBox`] from a non-float value stored in a `NaN` float representation.
    #[inline]
    #[must_use]
    pub fn from_value(value: Value) -> RawBox {
        RawBox {
            value: ManuallyDrop::new(value),
        }
    }

    /// Get the tag of the contained value, if the stored value isn't a float. Helper for
    /// `self.value().map(Value::tag)`.
    #[inline]
    #[must_use]
    pub fn tag(&self) -> Option<RawTag> {
        if self.is_value() {
            // SAFETY: We have ensured we contain a valid value
            Some(unsafe { self.value.tag() })
        } else {
            None
        }
    }

    /// Check whether the contained value is a float
    #[inline]
    #[must_use]
    pub fn is_float(&self) -> bool {
        // SAFETY: It is always sound to read this type as a float, or as raw bits
        (unsafe { !self.float.is_nan() } || unsafe { self.bits & SIGN_MASK == QUIET_NAN })
    }

    /// Check whether the contained value is a non-float value
    #[inline]
    #[must_use]
    pub fn is_value(&self) -> bool {
        // SAFETY: It is always sound to read this type as a float, or as raw bits
        (unsafe { self.float.is_nan() } && unsafe { self.bits & SIGN_MASK != QUIET_NAN })
    }

    /// Get a reference to this type as a float. Returns `Some` if a float is currently stored,
    /// `None` otherwise.
    #[inline]
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

    /// Get a mutable reference to this type as a float. Returns `Some` if a float is currently
    /// stored, `None` otherwise.
    ///
    /// This doesn't return a raw `f64` because then it would be possible for downstream users to
    /// write a non-normalized `NaN` value into it, breaking the contract of this type. The
    /// [`SingleNaNF64`] type exposes the value mutably while preventing that from happening.
    #[inline]
    #[must_use]
    pub fn float_mut(&mut self) -> Option<&mut SingleNaNF64> {
        if self.is_float() {
            // SAFETY: We have ensured we contain a valid float value
            SingleNaNF64::from_mut(unsafe { &mut self.float })
        } else {
            None
        }
    }

    /// Get a reference to this type as a non-float stored value. Returns `Some` if a non-float
    /// value is currently stored, `None` otherwise.
    #[inline]
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

    /// Get a mutable reference to this type as a non-float stored value. Returns `Some` if a
    /// non-float value is currently stored, `None` otherwise.
    #[inline]
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

    /// Convert this type into the inner float, if possible. Returns `Ok` if the stored type is
    /// currently a float, `Err(self)` otherwise.
    #[inline]
    pub fn into_float(self) -> Result<f64, Self> {
        if self.is_float() {
            // SAFETY: If we pass the check, we contain a float, and can pull it out
            Ok(unsafe { self.float })
        } else {
            Err(self)
        }
    }

    /// Convert this type into the inner value, if possible. Returns `Ok` if the stored type is
    /// currently a non-float value, `Err(self)` otherwise.
    #[inline]
    pub fn into_value(self) -> Result<Value, Self> {
        if self.is_value() {
            // SAFETY: If we pass the check, we contain raw data, and can pull it out
            Ok(ManuallyDrop::into_inner(unsafe { self.value }))
        } else {
            Err(self)
        }
    }

    /// Convert this type into the inner float, performing no checking. This is safe because
    /// non-float values are stored as `NaN` representation floats, meaning they are always valid
    /// to read as a floating-point value and cannot accidentally appear as a 'normal' value,
    /// instead poisoning future operations performed with them.
    #[inline]
    pub fn into_float_unchecked(self) -> f64 {
        // SAFETY: The inner value is *always* a valid float, if stored as a non-float this will
        //         simply return 'some NaN float value'
        unsafe { self.float }
    }

    /// Convert this value into an enum containing either a float or the raw value that was stored
    pub fn into_enum(self) -> RawOwn {
        if self.is_float() {
            // SAFETY: If we pass the check, we contain a float
            RawOwn::Float(unsafe { self.float })
        } else {
            // SAFETY: If we don't pass the check, we contain a value
            RawOwn::Value(ManuallyDrop::into_inner(unsafe { self.value }))
        }
    }

    /// Get a reference to this instance as either a float or as the non-float value that was stored
    pub fn enum_ref(&self) -> RawRef<'_> {
        if self.is_float() {
            // SAFETY: If we pass the check, we contain a float
            RawRef::Float(unsafe { &self.float })
        } else {
            // SAFETY: If we don't pass the check, we contain a value
            RawRef::Value(unsafe { &self.value })
        }
    }

    /// Get a mutable reference to this instance as either a float or as the non-float value that was
    /// stored
    pub fn enum_mut(&mut self) -> RawMut<'_> {
        if self.is_float() {
            // SAFETY: If we pass the check, we contain a float
            let single = SingleNaNF64::from_mut(unsafe { &mut self.float });
            // SAFETY: If we pass the check, we're guaranteed to contain a valid float for SingleNaN
            RawMut::Float(unsafe { single.unwrap_unchecked() })
        } else {
            // SAFETY: If we don't pass the check, we contain a value
            RawMut::Value(unsafe { &mut self.value })
        }
    }
}

impl Clone for RawBox {
    #[inline]
    fn clone(&self) -> Self {
        RawBox {
            // SAFETY: It is always sound to read this type as bits, which
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

/// Enum for the two possible states of a [`RawBox`], for matching convenience
pub enum RawOwn {
    /// A float value
    Float(f64),
    /// A non-float value
    Value(Value),
}

/// Enum for possible references into a [`RawBox`] .
pub enum RawRef<'a> {
    /// A reference to a stored float
    Float(&'a f64),
    /// A reference to non-float data
    Value(&'a Value),
}

/// Enum for possible mutable references into a [`RawBox`].
pub enum RawMut<'a> {
    /// A mutable reference to a stored float
    Float(&'a mut SingleNaNF64),
    /// A mutable reference to non-float data
    Value(&'a mut Value),
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
        let a = RawBox::from_float(1.0);
        assert_eq!(a.into_float().ok(), Some(1.0));

        let b = RawBox::from_float(-1.0);
        assert_eq!(b.into_float().ok(), Some(-1.0));

        let c = RawBox::from_float(f64::NAN);
        assert!(c
            .into_float()
            .is_ok_and(|val| val.is_nan() && val.is_sign_positive()));

        let d = RawBox::from_float(-f64::NAN);
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
    fn test_clone_float() {
        let a = RawBox::from_float(1.0);
        let b = a.clone();
        assert_eq!(b.into_float().ok(), Some(1.0));
    }
}
