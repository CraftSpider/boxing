//! A safe wrapper around a [`RawBox`] which can store a float, integer types of size >= 32, or
//! references to/an owned value of a type of any size.

use crate::nan::raw::{RawStore, RawTag, Value};
use crate::nan::{RawBox, SingleNaNF64};
use crate::utils::ArrayExt;
use std::marker::PhantomData;
use std::num::NonZeroU8;
use std::ops::Deref;
use std::{fmt, mem};

mod sealed {
    use super::*;

    #[derive(PartialEq)]
    pub enum HeapType {
        /// Max stored integer is 4 bytes, remaining
        /// two are used for more info
        Int = 1,

        Ptr = 2,
        MutPtr = 3,
        Ref = 4,
        // No MutRef because it means we can't implement `Clone`
        Box = 6,
    }

    pub trait HeapInlineSealed<T>: Sized {
        fn ty() -> HeapType;

        /// Write this type into a [`Value`].
        fn write(self, value: &mut Value);

        /// Read this type from a [`Value`].
        ///
        /// # Safety
        ///
        /// The caller must have ensured that the value contains a valid instance of this type
        unsafe fn try_read(value: &Value) -> Option<Self>;
    }
}

use sealed::{HeapInlineSealed, HeapType};

#[inline]
fn int_ty(bytes: impl Deref<Target = [u8; 6]>) -> IntType {
    #[cfg(target_endian = "big")]
    let ty = u16::from_ne_bytes([bytes[0], bytes[1]]);
    #[cfg(target_endian = "little")]
    let ty = u16::from_ne_bytes([bytes[4], bytes[5]]);
    IntType::from_u16(ty)
}

#[inline]
fn int_data(bytes: &[u8; 6]) -> &[u8; 4] {
    #[cfg(target_endian = "big")]
    // SAFETY: We're offsetting by 2 and shrinking, which is legal
    let data = unsafe {
        &*(bytes as *const [u8; 6])
            .cast::<u8>()
            .offset(2)
            .cast::<[u8; 4]>()
    };
    #[cfg(target_endian = "little")]
    // SAFETY: We're just shrinking the array, which is legal
    let data = unsafe { &*(bytes as *const [u8; 6]).cast::<[u8; 4]>() };
    data
}

#[inline]
fn int_data_mut(bytes: &mut [u8; 6]) -> &mut [u8; 4] {
    #[cfg(target_endian = "big")]
    // SAFETY: We're offsetting by 2 and shrinking, which is legal
    let data = unsafe {
        &mut *(bytes as *mut [u8; 6])
            .cast::<u8>()
            .offset(2)
            .cast::<[u8; 4]>()
    };
    #[cfg(target_endian = "little")]
    // SAFETY: We're just shrinking the array, which is legal
    let data = unsafe { &mut *(bytes as *mut [u8; 6]).cast::<[u8; 4]>() };
    data
}

#[inline]
fn write_int<I: IntInline>(val: I) -> [u8; 6] {
    let ty = (I::ty() as u16).to_ne_bytes();
    let val = val.to_bytes();
    #[cfg(target_endian = "big")]
    return [ty[0], ty[1], val[0], val[1], val[2], val[3]];
    #[cfg(target_endian = "little")]
    return [val[0], val[1], val[2], val[3], ty[0], ty[1]];
}

#[inline]
fn read_int<I: IntInline>(bytes: &[u8; 6]) -> Option<I> {
    let ty = int_ty(bytes);
    let data = int_data(bytes);

    if ty == I::ty() {
        // SAFETY: Data is guaranteed valid for I, since the type is that of I, and 4-byte aligned
        Some(unsafe { I::from_bytes(*data) })
    } else {
        None
    }
}

impl HeapType {
    #[inline]
    fn raw_tag(self) -> RawTag {
        // SAFETY: `HeapType` discriminant is in the range 1..7
        RawTag::new(false, unsafe { NonZeroU8::new_unchecked(self as u8) })
    }

    #[inline]
    fn from_raw_tag(tag: RawTag) -> Option<HeapType> {
        if tag.is_neg() {
            return None;
        }

        Some(match tag.val().get() {
            1 => HeapType::Int,
            2 => HeapType::Ptr,
            3 => HeapType::MutPtr,
            4 => HeapType::Ref,
            6 => HeapType::Box,
            _ => return None,
        })
    }
}

#[derive(PartialEq)]
#[repr(u16)]
enum IntType {
    Bool = 0,
    Char = 1,

    U8 = 2,
    U16 = 3,
    U32 = 4,

    I8 = 5,
    I16 = 6,
    I32 = 7,

    F32 = 8,
}

impl IntType {
    #[inline]
    fn from_u16(val: u16) -> IntType {
        match val {
            0 => IntType::Bool,
            1 => IntType::Char,
            2 => IntType::U8,
            3 => IntType::U16,
            4 => IntType::U32,
            5 => IntType::I8,
            6 => IntType::I16,
            7 => IntType::I32,
            8 => IntType::F32,
            _ => unreachable!(),
        }
    }
}

trait IntInline: Sized {
    fn ty() -> IntType;
    fn to_bytes(self) -> [u8; 4];

    /// # Safety
    ///
    /// The provided bytes must be a valid instance of this type, obeying niche requirements
    unsafe fn from_bytes(bytes: [u8; 4]) -> Self;

    #[inline]
    unsafe fn ref_bytes(bytes: &[u8; 4]) -> &Self {
        // SAFETY: All `IntInline` implementors allow this
        unsafe { &*bytes.as_ptr().cast() }
    }

    #[inline]
    unsafe fn mut_bytes(bytes: &mut [u8; 4]) -> &mut Self {
        // SAFETY: All `IntInline` implementors allow this
        unsafe { &mut *bytes.as_mut_ptr().cast() }
    }
}

/// Trait for types that can be stored inline in a [`NanBox`].
///
/// This trait is sealed - the types that can be stored in a [`NanBox`] are
/// determined by the library, if you wish to store other types, consider using [`RawBox`]
/// to implement a custom version of this type.
pub trait HeapInline<T>: HeapInlineSealed<T> {}

/// Trait for types that can have a reference to them taken while they are in a [`NanBox`]
pub trait HeapInlineRef<T>: HeapInline<T> {
    #[doc(hidden)]
    fn try_ref(value: &Value) -> Option<&Self>;
    #[doc(hidden)]
    fn try_mut(value: &mut Value) -> Option<&mut Self>;
}

macro_rules! impl_int {
    ($ty:ty, $variant:ident) => {
        impl<T> HeapInlineSealed<T> for $ty {
            #[inline]
            fn ty() -> HeapType {
                HeapType::Int
            }

            #[inline]
            fn write(self, value: &mut Value) {
                value.set_data(write_int(self))
            }

            #[inline]
            unsafe fn try_read(value: &Value) -> Option<Self> {
                read_int(value.data())
            }
        }

        impl<T> HeapInline<T> for $ty {}

        impl IntInline for $ty {
            fn ty() -> IntType {
                IntType::$variant
            }

            #[inline]
            fn to_bytes(self) -> [u8; 4] {
                self.to_ne_bytes().truncate_to()
            }

            #[inline]
            unsafe fn from_bytes(bytes: [u8; 4]) -> Self {
                <$ty>::from_ne_bytes(bytes.truncate_to())
            }
        }

        impl<T> HeapInlineRef<T> for $ty {
            #[inline]
            fn try_ref(value: &Value) -> Option<&Self> {
                let ty = int_ty(value.data());
                let data = int_data(value.data());
                if ty == <Self as IntInline>::ty() {
                    // SAFETY: Since types match, data is a valid instance of Self
                    Some(unsafe { Self::ref_bytes(data) })
                } else {
                    None
                }
            }

            #[inline]
            fn try_mut(value: &mut Value) -> Option<&mut Self> {
                let ty = int_ty(value.data());
                let data = int_data_mut(value.data_mut());
                if ty == <Self as IntInline>::ty() {
                    // SAFETY: Since types match, data is a valid instance of Self
                    Some(unsafe { Self::mut_bytes(data) })
                } else {
                    None
                }
            }
        }
    };
}

impl_int!(u8, U8);
impl_int!(u16, U16);
impl_int!(u32, U32);

impl_int!(i8, I8);
impl_int!(i16, I16);
impl_int!(i32, I32);

impl_int!(f32, F32);

impl IntInline for bool {
    #[inline]
    fn ty() -> IntType {
        IntType::Bool
    }

    #[inline]
    fn to_bytes(self) -> [u8; 4] {
        [u8::from(self), 0, 0, 0]
    }

    #[inline]
    unsafe fn from_bytes(bytes: [u8; 4]) -> Self {
        bytes[0] == 1
    }
}

impl<T> HeapInlineSealed<T> for bool {
    #[inline]
    fn ty() -> HeapType {
        HeapType::Int
    }

    #[inline]
    fn write(self, value: &mut Value) {
        value.set_data(write_int(self));
    }

    #[inline]
    unsafe fn try_read(value: &Value) -> Option<Self> {
        read_int(value.data())
    }
}

impl<T> HeapInline<T> for bool {}

impl IntInline for char {
    #[inline]
    fn ty() -> IntType {
        IntType::Char
    }

    #[inline]
    fn to_bytes(self) -> [u8; 4] {
        u32::to_bytes(self as u32)
    }

    #[inline]
    unsafe fn from_bytes(bytes: [u8; 4]) -> Self {
        // SAFETY: Caller contract requires provided bytes form a valid char
        unsafe { char::from_u32_unchecked(u32::from_bytes(bytes)) }
    }
}

impl<T> HeapInlineSealed<T> for char {
    #[inline]
    fn ty() -> HeapType {
        HeapType::Int
    }

    #[inline]
    fn write(self, value: &mut Value) {
        value.set_data(write_int(self));
    }

    #[inline]
    unsafe fn try_read(value: &Value) -> Option<Self> {
        read_int(value.data())
    }
}

impl<T> HeapInline<T> for char {}

impl<T> HeapInlineSealed<T> for *const T {
    #[inline]
    fn ty() -> HeapType {
        HeapType::Ptr
    }

    #[inline]
    fn write(self, value: &mut Value) {
        RawStore::to_val(self, value);
    }

    #[inline]
    unsafe fn try_read(value: &Value) -> Option<Self> {
        Some(RawStore::from_val(value))
    }
}

impl<T> HeapInline<T> for *const T {}

impl<T> HeapInlineSealed<T> for *mut T {
    #[inline]
    fn ty() -> HeapType {
        HeapType::MutPtr
    }

    #[inline]
    fn write(self, value: &mut Value) {
        RawStore::to_val(self, value);
    }

    #[inline]
    unsafe fn try_read(value: &Value) -> Option<Self> {
        Some(RawStore::from_val(value))
    }
}

impl<T> HeapInline<T> for *mut T {}

impl<'a, T> HeapInlineSealed<T> for &'a T {
    #[inline]
    fn ty() -> HeapType {
        HeapType::Ref
    }

    #[inline]
    fn write(self, value: &mut Value) {
        RawStore::to_val(self as *const T, value);
    }

    #[inline]
    unsafe fn try_read(value: &Value) -> Option<Self> {
        // SAFETY: Caller is required to ensure value contains a valid reference
        Some(unsafe { &*<*const T as RawStore>::from_val(value) })
    }
}

impl<'a, T> HeapInline<T> for &'a T {}

/// A NaN Box capable of safely storing a float, integer values of size <= <u class="mousetext" text="32 bits">4 bytes</u>,
/// or an owned value of any size or pointers/references to it. This doesn't support storing
/// mutable references as a trade-off to allow cloning.
///
/// This type acts basically like the following Rust enum:
///
/// ```
/// # use boxing::nan::SingleNaNF64;
///
/// enum NanBox<'a, T> {
///     Float(SingleNaNF64),
///     I8(i8),
///     I16(i16),
///     I32(i32),
///     U8(u8),
///     U16(u16),
///     U32(u32),
///     Bool(bool),
///     Char(char),
///     Ptr(*const T),
///     MutPtr(*mut T),
///     Ref(&'a T),
///     Box(Box<T>),
/// }
/// ```
///
/// We can't actually define ourselves as that because `SingleNaNF64` doesn't actually have a
/// niche, and even if it did, special work is required to make pointers and references act as if
/// they're 48 bits instead of 64 bits long.
///
/// This handles storing a `T` of any sized by keeping it on the heap if owned by the box, or
/// alternatively holding a reference to a `T` that lives for up to `'a`.
pub struct NanBox<'a, T>(RawBox, PhantomData<&'a mut T>);

impl<'a, T> NanBox<'a, T> {
    #[inline]
    fn from_raw(b: RawBox) -> NanBox<'a, T> {
        NanBox(b, PhantomData)
    }

    /// Store an [`f64`] value in this [`NanBox`]. If the value of the float is `NaN`, then it will
    /// be normalized to the standard quiet `NaN` representation used by the box, otherwise it will
    /// be stored as-is.
    #[inline]
    #[must_use]
    pub fn from_float(val: f64) -> NanBox<'a, T> {
        NanBox::from_raw(RawBox::from_float(val))
    }

    /// Store one of the possible inline values in this [`NanBox`]. This would be any implementor
    /// of [`HeapInline`].
    #[must_use]
    pub fn from_inline<U: HeapInline<T> + 'a>(val: U) -> NanBox<'a, T> {
        let ty = U::ty();
        let mut value = Value::empty(ty.raw_tag());
        U::write(val, &mut value);
        let raw = RawBox::from_value(value);
        NanBox::from_raw(raw)
    }

    /// Store an owned, boxed value in this [`NanBox`].
    #[must_use]
    pub fn from_box(val: Box<T>) -> NanBox<'a, T> {
        let tag = HeapType::Box.raw_tag();
        let value = Value::store(tag, Box::into_raw(val));
        let raw = RawBox::from_value(value);
        NanBox::from_raw(raw)
    }

    /// Check whether this box currently contains a float
    #[inline]
    #[must_use]
    pub fn is_float(&self) -> bool {
        self.0.is_float()
    }

    /// Attempt to get a reference to a contained floating-point value. This returns `Some` if the
    /// contained value is a float.
    #[inline]
    #[must_use]
    pub fn try_ref_float(&self) -> Option<&f64> {
        self.0.float()
    }

    /// Attempt to get a mutable reference to a contained floating-point value. This returns `Some`
    /// if the contained value is a float.
    ///
    /// This doesn't return a raw `f64` because then it would be possible to write `NaN` values
    /// into it which break our safety requirements. The [`SingleNaNF64`] type supports most float
    /// operations, but can only be written to a single `NaN` value which matches our chosen
    /// normalized `NaN`.
    #[inline]
    #[must_use]
    pub fn try_mut_float(&mut self) -> Option<&mut SingleNaNF64> {
        self.0.float_mut()
    }

    /// Attempt to get a reference to a value stored inline. This returns `Some` if the contained
    /// value is of the specified type.
    #[must_use]
    pub fn try_ref_inline<U: HeapInlineRef<T> + 'a>(&self) -> Option<&U> {
        self.0.value().and_then(|val| {
            if HeapType::from_raw_tag(val.tag()) == Some(<U as HeapInlineSealed<_>>::ty()) {
                U::try_ref(val)
            } else {
                None
            }
        })
    }

    /// Attempt to get a mutable reference to a value stored inline. This returns `Some` if the
    /// contained value is of the specified type.
    #[must_use]
    pub fn try_mut_inline<U: HeapInlineRef<T> + 'a>(&mut self) -> Option<&mut U> {
        self.0.value_mut().and_then(|val| {
            if HeapType::from_raw_tag(val.tag()) == Some(<U as HeapInlineSealed<_>>::ty()) {
                U::try_mut(val)
            } else {
                None
            }
        })
    }

    /// Attempt to get a reference to the owned value of type `T`. This returns `Some` if the
    /// contained value is an owned `T`.
    #[must_use]
    pub fn try_ref_boxed(&self) -> Option<&T> {
        self.0.value().and_then(|val| {
            if HeapType::from_raw_tag(val.tag()) == Some(HeapType::Box) {
                let ptr = <*const T as RawStore>::from_val(val);
                // SAFETY: Type is Box, so inner value is owned by us and can be referenced matching us
                Some(unsafe { &*ptr })
            } else {
                None
            }
        })
    }

    /// Attempt to get a mutable reference to the owned value of type `T`. This returns `Some` if
    /// the contained value is an owned `T`.
    #[must_use]
    pub fn try_mut_boxed(&mut self) -> Option<&mut T> {
        self.0.value_mut().and_then(|val| {
            if HeapType::from_raw_tag(val.tag()) == Some(HeapType::Box) {
                let ptr = <*mut T as RawStore>::from_val(val);
                // SAFETY: Type is Box, so inner value is owned by us and can be referenced matching us
                Some(unsafe { &mut *ptr })
            } else {
                None
            }
        })
    }

    /// Attempt to convert this box into a contained float value. Returns `Ok` if the contained
    /// value is a flaot, otherwise `Err(self)`.
    pub fn try_into_float(self) -> Result<f64, Self> {
        self.0.float().copied().ok_or(self)
    }

    /// Attempt to convert this box into a contained inline value. Returns `Ok` if the contained
    /// value is the specified inline type, otherwise `Err(self)`.
    pub fn try_into_inline<U: HeapInline<T> + 'a>(self) -> Result<U, Self> {
        self.0
            .value()
            .and_then(|val| {
                if HeapType::from_raw_tag(val.tag()) == Some(U::ty()) {
                    // SAFETY: We just checked that the type matches, so this is sound
                    unsafe { U::try_read(val) }
                } else {
                    None
                }
            })
            .ok_or(self)
    }

    /// Attempt to convert this box into a contained owned `T`. Returns `Ok` if the contained
    /// value is an owned `T`, otherwise `Err(self)`.
    pub fn try_into_boxed(mut self) -> Result<T, Self> {
        let inner = mem::replace(&mut self.0, RawBox::from_float(f64::NAN));

        inner
            .into_value()
            .and_then(|val| {
                if HeapType::from_raw_tag(val.tag()) == Some(HeapType::Box) {
                    let ptr = val.load::<*mut T>();
                    // SAFETY: Since type matches, this value was leaked from a box
                    Ok(unsafe { *Box::from_raw(ptr) })
                } else {
                    Err(RawBox::from_value(val))
                }
            })
            .map_err(NanBox::from_raw)
    }

    /// Convert this type into the inner float, performing no checking. This is safe because
    /// non-float values are stored as `NaN` representation floats, meaning they are always valid
    /// to read as a floating-point value and cannot accidentally appear as a 'normal' value,
    /// instead poisoning future operations performed with them.
    #[inline]
    #[must_use]
    pub fn into_float_unchecked(mut self) -> f64 {
        let inner = mem::replace(&mut self.0, RawBox::from_float(f64::NAN));
        inner.into_float_unchecked()
    }
}

impl<T> From<f64> for NanBox<'_, T> {
    #[inline]
    fn from(value: f64) -> Self {
        NanBox::from_float(value)
    }
}

macro_rules! from_inline {
    ($ty:ty) => {
        impl<'a, T> From<$ty> for NanBox<'a, T> {
            #[inline]
            fn from(value: $ty) -> Self {
                NanBox::from_inline(value)
            }
        }
    };
}

from_inline!(u8);
from_inline!(u16);
from_inline!(u32);

from_inline!(i8);
from_inline!(i16);
from_inline!(i32);

from_inline!(bool);
from_inline!(char);

from_inline!(*const T);
from_inline!(*mut T);
from_inline!(&'a T);

impl<T> From<Box<T>> for NanBox<'_, T> {
    fn from(value: Box<T>) -> Self {
        NanBox::from_box(value)
    }
}

impl<'a, T> Clone for NanBox<'a, T>
where
    T: Clone,
{
    fn clone(&self) -> Self {
        let tag = self.0.tag().and_then(HeapType::from_raw_tag);

        match tag {
            None => NanBox::from_float(*self.0.float().unwrap()),
            Some(HeapType::Int) => {
                let data = self.0.value().unwrap().data();
                NanBox::from_raw(RawBox::from_value(Value::new(
                    HeapType::Int.raw_tag(),
                    *data,
                )))
            }
            Some(tag @ (HeapType::Ptr | HeapType::MutPtr | HeapType::Ref)) => {
                let ptr = self.0.value().map(<*const T>::from_val).unwrap();
                NanBox::from_raw(RawBox::from_value(Value::store(tag.raw_tag(), ptr)))
            }
            Some(HeapType::Box) => {
                let ptr = self.0.value().map(<*const T>::from_val).unwrap();
                // SAFETY: Since type is Box, we know inner value is uniquely owned by us
                let r = unsafe { &*ptr };
                NanBox::from_box(Box::new(T::clone(r)))
            }
        }
    }
}

impl<'a, T> PartialEq for NanBox<'a, T>
where
    T: PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        if self.0.tag() != other.0.tag() {
            return false;
        }

        match self.0.tag().and_then(HeapType::from_raw_tag) {
            None => self.0.float() == other.0.float(),
            Some(HeapType::Int | HeapType::Ptr | HeapType::MutPtr) => {
                self.0.value().map(Value::data) == other.0.value().map(Value::data)
            }
            Some(HeapType::Ref | HeapType::Box) => {
                let ptr1 = self.0.value().map(<*const T>::from_val).unwrap();
                let ptr2 = other.0.value().map(<*const T>::from_val).unwrap();

                // SAFETY: Type matches, and both Ref and Box guarantee our inner value is sound
                //         to turn into a reference
                (unsafe { &*ptr1 }) == (unsafe { &*ptr2 })
            }
        }
    }
}

impl<'a, T> fmt::Debug for NanBox<'a, T>
where
    T: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let tag = self.0.tag().and_then(HeapType::from_raw_tag);

        let variant = match tag {
            None => "NanBox::Float",
            Some(HeapType::Int) => {
                let ty = int_ty(self.0.value().unwrap().data());
                match ty {
                    IntType::Bool => "NanBox::Bool",
                    IntType::Char => "NanBox::Char",
                    IntType::U8 => "NanBox::U8",
                    IntType::U16 => "NanBox::U16",
                    IntType::U32 => "NanBox::U32",
                    IntType::I8 => "NanBox::I8",
                    IntType::I16 => "NanBox::I16",
                    IntType::I32 => "NanBox::I32",
                    IntType::F32 => "NanBox::F32",
                }
            }
            Some(HeapType::Ptr) => "NanBox::Ptr",
            Some(HeapType::MutPtr) => "NanBox::MutPtr",
            Some(HeapType::Ref) => "NanBox::Ref",
            Some(HeapType::Box) => "NanBox::Box",
        };

        let mut tuple = f.debug_tuple(variant);

        match tag {
            None => {
                let val = self.0.float().unwrap();
                tuple.field(val);
            }
            Some(HeapType::Int) => {
                let bytes = self.0.value().unwrap().data();
                let ty = int_ty(bytes);
                let data = int_data(bytes);
                match ty {
                    // SAFETY: Type matches to this is sound
                    IntType::Bool => tuple.field(unsafe { bool::ref_bytes(data) }),
                    // SAFETY: Type matches to this is sound
                    IntType::Char => tuple.field(unsafe { char::ref_bytes(data) }),
                    // SAFETY: Type matches to this is sound
                    IntType::U8 => tuple.field(unsafe { u8::ref_bytes(data) }),
                    // SAFETY: Type matches to this is sound
                    IntType::U16 => tuple.field(unsafe { u16::ref_bytes(data) }),
                    // SAFETY: Type matches to this is sound
                    IntType::U32 => tuple.field(unsafe { u32::ref_bytes(data) }),
                    // SAFETY: Type matches to this is sound
                    IntType::I8 => tuple.field(unsafe { i8::ref_bytes(data) }),
                    // SAFETY: Type matches to this is sound
                    IntType::I16 => tuple.field(unsafe { i16::ref_bytes(data) }),
                    // SAFETY: Type matches to this is sound
                    IntType::I32 => tuple.field(unsafe { i32::ref_bytes(data) }),
                    // SAFETY: Type matches to this is sound
                    IntType::F32 => tuple.field(unsafe { f32::ref_bytes(data) }),
                };
            }
            Some(HeapType::Ptr | HeapType::MutPtr) => {
                let ptr = self.0.value().map(<*const T>::from_val).unwrap();
                tuple.field(&ptr);
            }
            Some(HeapType::Ref | HeapType::Box) => {
                let ptr = self.0.value().map(<*const T>::from_val).unwrap();
                // SAFETY: If our type is `Ref` or `Box`, we contain a pointer valid to dereference for at least `'a`
                let r = unsafe { &*ptr };
                tuple.field(r);
            }
        }

        tuple.finish()
    }
}

impl<'a, T> Drop for NanBox<'a, T> {
    fn drop(&mut self) {
        if self.0.tag().and_then(HeapType::from_raw_tag) == Some(HeapType::Box) {
            let ptr = self.0.value().map(<*mut T>::from_val).unwrap();
            // SAFETY: If our type is `Box`, we contain an owned pointer and are allowed to free it on drop
            drop(unsafe { Box::from_raw(ptr) });
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_roundtrip_float() {
        let a = NanBox::<()>::from_float(1.0);
        assert_eq!(a.try_into_float(), Ok(1.0));

        let b = NanBox::<()>::from_float(f64::NAN);
        assert_eq!(b.try_into_float().unwrap().to_bits(), crate::nan::QUIET_NAN);
    }

    #[test]
    fn test_roundtrip_bool() {
        let a = NanBox::<()>::from_inline(true);
        assert_eq!(a.try_into_inline::<bool>(), Ok(true));

        let b = NanBox::<()>::from_inline(false);
        assert_eq!(b.try_into_inline::<bool>(), Ok(false));
    }

    #[test]
    fn test_roundtrip_char() {
        let a = NanBox::<()>::from_inline('a');
        assert_eq!(a.try_into_inline::<char>(), Ok('a'));

        let b = NanBox::<()>::from_inline('😀');
        assert_eq!(b.try_into_inline::<char>(), Ok('😀'));
    }

    #[test]
    fn test_roundtrip_ref() {
        let r = 1;

        let a = NanBox::<i32>::from_inline(&r);
        assert_eq!(a.try_into_inline::<&i32>(), Ok(&1));
    }

    #[test]
    fn test_roundtrip_boxed() {
        #[derive(Debug, PartialEq)]
        struct VeryLarge([u8; 128]);
        let r = Box::new(VeryLarge([0x55; 128]));

        let a = NanBox::<VeryLarge>::from_box(r);
        assert_eq!(a.try_into_boxed(), Ok(VeryLarge([0x55; 128])));
    }

    #[test]
    fn test_ref_u32() {
        let mut a = NanBox::<i32>::from_inline(-100i32);

        let r1 = a.try_ref_inline::<i32>().unwrap();
        assert_eq!(*r1, -100);

        let r2 = a.try_mut_inline::<i32>().unwrap();
        *r2 = 100;
        assert_eq!(*r2, 100);
    }

    #[test]
    fn test_eq() {
        let a = NanBox::<i32>::from_float(1.0);
        let b = NanBox::<i32>::from_float(-1.0);
        let c = NanBox::<i32>::from_inline(true);
        let d = NanBox::<i32>::from_inline(1);
        let e = NanBox::from_inline(&10);
        let f = NanBox::from_box(Box::new(-10));

        assert_eq!(a, a);
        assert_eq!(b, b);
        assert_eq!(c, c);
        assert_eq!(d, d);
        assert_eq!(e, e);
        assert_eq!(f, f);
    }
}
