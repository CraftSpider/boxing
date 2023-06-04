use crate::nan::raw::{RawStore, RawTag, Value};
use crate::nan::{RawBox, SingleNaNF64};
use crate::utils::ArrayExt;
use std::marker::PhantomData;
use std::{fmt, mem};
use std::num::NonZeroU8;
use std::ops::Deref;

fn int_ty(bytes: impl Deref<Target = [u8; 6]>) -> IntType {
    #[cfg(target_endian = "big")]
    let ty = u16::from_ne_bytes([bytes[0], bytes[1]]);
    #[cfg(target_endian = "little")]
    let ty = u16::from_ne_bytes([bytes[4], bytes[5]]);
    IntType::from_u16(ty)
}

fn int_data(bytes: &[u8; 6]) -> &[u8; 4] {
    #[cfg(target_endian = "big")]
    // SAFETY: We're offsetting by 2 and shrinking, which is legal
    let data = unsafe { &*(bytes as *const [u8; 6]).cast::<u8>().offset(2).cast::<[u8; 4]>() };
    #[cfg(target_endian = "little")]
    // SAFETY: We're just shrinking the array, which is legal
    let data = unsafe { &*(bytes as *const [u8; 6]).cast::<[u8; 4]>() };
    data
}

fn int_data_mut(bytes: &mut [u8; 6]) -> &mut [u8; 4] {
    #[cfg(target_endian = "big")]
    // SAFETY: We're offsetting by 2 and shrinking, which is legal
    let data = unsafe { &mut *(bytes as *mut [u8; 6]).cast::<u8>().offset(2).cast::<[u8; 4]>() };
    #[cfg(target_endian = "little")]
    // SAFETY: We're just shrinking the array, which is legal
    let data = unsafe { &mut *(bytes as *mut [u8; 6]).cast::<[u8; 4]>() };
    data
}

fn write_int<I: IntInline>(val: I) -> [u8; 6] {
    let ty = (I::ty() as u16).to_ne_bytes();
    let val = val.to_bytes();
    #[cfg(target_endian = "big")]
    return [ty[0], ty[1], val[0], val[1], val[2], val[3]];
    #[cfg(target_endian = "little")]
    return [val[0], val[1], val[2], val[3], ty[0], ty[1]];
}

fn read_int<I: IntInline>(bytes: [u8; 6]) -> Option<I> {
    let ty = int_ty(&bytes);
    let data = int_data(&bytes);
    
    if ty == I::ty() {
        // SAFETY: Data is guaranteed valid for I, since the type is that of I, and 4-byte aligned
        Some(unsafe { I::from_bytes(*data) })
    } else {
        None
    }
}

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

impl HeapType {
    fn raw_tag(self) -> RawTag {
        // SAFETY: `HeapType` discriminant is in the range 1..7
        RawTag::new(false, unsafe { NonZeroU8::new_unchecked(self as u8) })
    }

    fn from_raw_tag(tag: RawTag) -> Option<HeapType> {
        if tag.is_neg() {
            return None;
        }

        Some(match tag.val() {
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
}

impl IntType {
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
    
    unsafe fn ref_bytes(bytes: &[u8; 4]) -> &Self {
        &*bytes.as_ptr().cast()
    }
    
    unsafe fn mut_bytes(bytes: &mut [u8; 4]) -> &mut Self {
        &mut *bytes.as_mut_ptr().cast()
    }
}

pub trait HeapInline<T>: Sized {
    fn ty() -> HeapType;
    fn write(self, value: &mut Value);

    /// # Safety
    /// 
    /// The caller must have ensured that the value contains a valid instance of this type
    unsafe fn try_read(value: &Value) -> Option<Self>;
}

pub trait HeapInlineRef<T>: HeapInline<T> {
    fn try_ref(value: &Value) -> Option<&Self>;
    fn try_mut(value: &mut Value) -> Option<&mut Self>;
}

impl<T, I: HeapInline<T> + IntInline> HeapInlineRef<T> for I {
    fn try_ref(value: &Value) -> Option<&Self> {
        let ty = int_ty(value.ref_data());
        let data = int_data(value.ref_data());
        if ty == <Self as IntInline>::ty() {
            // SAFETY: Since types match, data is a valid instance of Self
            Some(unsafe { I::ref_bytes(data) })
        } else {
            None
        }
    }

    fn try_mut(value: &mut Value) -> Option<&mut Self> {
        let ty = int_ty(value.ref_data());
        let data = int_data_mut(value.mut_data());
        if ty == <Self as IntInline>::ty() {
            // SAFETY: Since types match, data is a valid instance of Self
            Some(unsafe { I::mut_bytes(data) })
        } else {
            None
        }
    }
}

macro_rules! impl_int {
    ($ty:ty, $variant:ident) => {
        impl<T> HeapInline<T> for $ty {
            fn ty() -> HeapType {
                HeapType::Int
            }

            fn write(self, value: &mut Value) {
                value.set_data(write_int(self))
            }

            unsafe fn try_read(value: &Value) -> Option<Self> {
                read_int(value.data())
            }
        }

        impl IntInline for $ty {
            fn ty() -> IntType {
                IntType::$variant
            }

            fn to_bytes(self) -> [u8; 4] {
                self.to_ne_bytes().truncate_to()
            }

            unsafe fn from_bytes(bytes: [u8; 4]) -> Self {
                <$ty>::from_ne_bytes(bytes.truncate_to())
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

impl IntInline for bool {
    fn ty() -> IntType {
        IntType::Bool
    }

    fn to_bytes(self) -> [u8; 4] {
        [u8::from(self), 0, 0, 0]
    }

    unsafe fn from_bytes(bytes: [u8; 4]) -> Self {
        bytes[0] == 1
    }
}

impl<T> HeapInline<T> for bool {
    fn ty() -> HeapType {
        HeapType::Int
    }

    fn write(self, value: &mut Value) {
        value.set_data(write_int(self));
    }

    unsafe fn try_read(value: &Value) -> Option<Self> {
        read_int(value.data())
    }
}

impl IntInline for char {
    fn ty() -> IntType {
        IntType::Char
    }

    fn to_bytes(self) -> [u8; 4] {
        u32::to_bytes(self as u32)
    }

    unsafe fn from_bytes(bytes: [u8; 4]) -> Self {
        // SAFETY: This requires provided bytes form a valid char
        char::from_u32_unchecked(u32::from_bytes(bytes))
    }
}

impl<T> HeapInline<T> for char {
    fn ty() -> HeapType {
        HeapType::Int
    }

    fn write(self, value: &mut Value) {
        value.set_data(write_int(self));
    }

    unsafe fn try_read(value: &Value) -> Option<Self> {
        read_int(value.data())
    }
}

impl<T> HeapInline<T> for *const T {
    fn ty() -> HeapType {
        HeapType::Ptr
    }

    fn write(self, value: &mut Value) {
        RawStore::to_val(self, value);
    }

    unsafe fn try_read(value: &Value) -> Option<Self> {
        Some(RawStore::from_val(value))
    }
}

impl<T> HeapInline<T> for *mut T {
    fn ty() -> HeapType {
        HeapType::MutPtr
    }

    fn write(self, value: &mut Value) {
        RawStore::to_val(self, value);
    }

    unsafe fn try_read(value: &Value) -> Option<Self> {
        Some(RawStore::from_val(value))
    }
}

impl<'a, T> HeapInline<T> for &'a T {
    fn ty() -> HeapType {
        HeapType::Ref
    }

    fn write(self, value: &mut Value) {
        RawStore::to_val(self as *const T, value);
    }

    unsafe fn try_read(value: &Value) -> Option<Self> {
        // SAFETY: Caller is required to ensure value contains a valid reference
        Some(unsafe { &*<*const T as RawStore>::from_val(value) })
    }
}

pub struct NanBox<'a, T>(RawBox, PhantomData<&'a mut T>);

impl<'a, T> NanBox<'a, T> {
    fn from_raw(b: RawBox) -> NanBox<'a, T> {
        NanBox(b, PhantomData)
    }

    #[must_use]
    pub fn from_f64(val: f64) -> NanBox<'a, T> {
        NanBox::from_raw(RawBox::from_f64(val))
    }

    #[must_use]
    pub fn from_inline<U: HeapInline<T> + 'a>(val: U) -> NanBox<'a, T> {
        let ty = U::ty();
        let mut value = Value::empty(ty.raw_tag());
        U::write(val, &mut value);
        let raw = RawBox::from_value(value);
        NanBox::from_raw(raw)
    }

    #[must_use]
    pub fn from_box(val: Box<T>) -> NanBox<'a, T> {
        let tag = HeapType::Box.raw_tag();
        let value = Value::store(tag, Box::into_raw(val));
        let raw = RawBox::from_value(value);
        NanBox::from_raw(raw)
    }

    #[must_use]
    pub fn try_ref_f64(&self) -> Option<&f64> {
        self.0.ref_f64()
    }

    #[must_use]
    pub fn try_mut_f64(&mut self) -> Option<&mut SingleNaNF64> {
        self.0.mut_f64()
    }
    
    #[must_use]
    pub fn try_ref_inline<U: HeapInlineRef<T> + 'a>(&self) -> Option<&U> {
        self.0.try_read(|val| {
            if HeapType::from_raw_tag(val.tag()) == Some(<U as HeapInline<_>>::ty()) {
                U::try_ref(val)
            } else {
                None
            }
        })
    }
    
    #[must_use]
    pub fn try_mut_inline<U: HeapInlineRef<T> + 'a>(&mut self) -> Option<&mut U> {
        self.0.try_read_mut(|val| {
            if HeapType::from_raw_tag(val.tag()) == Some(<U as HeapInline<_>>::ty()) {
                U::try_mut(val)
            } else {
                None
            }
        })
    }
    
    #[must_use]
    pub fn try_ref_boxed(&self) -> Option<&T> {
        self.0.try_read(|val| {
            if HeapType::from_raw_tag(val.tag()) == Some(HeapType::Box) {
                let ptr = <*const T as RawStore>::from_val(val);
                // SAFETY: Type is Box, so inner value is owned by us and can be referenced matching us
                Some(unsafe { &*ptr })
            } else {
                None
            }
        })
    }

    #[must_use]
    pub fn try_mut_boxed(&mut self) -> Option<&mut T> {
        self.0.try_read_mut(|val| {
            if HeapType::from_raw_tag(val.tag()) == Some(HeapType::Box) {
                let ptr = <*mut T as RawStore>::from_val(val);
                // SAFETY: Type is Box, so inner value is owned by us and can be referenced matching us
                Some(unsafe { &mut *ptr })
            } else {
                None
            }
        })
    }

    pub fn try_into_f64(mut self) -> Result<f64, Self> {
        let inner = mem::replace(&mut self.0, RawBox::from_f64(f64::NAN));
        inner.into_f64().map_err(NanBox::from_raw)
    }

    pub fn try_into_inline<U: HeapInline<T> + 'a>(self) -> Result<U, Self> {
        self.0.try_read(|val| {
            if HeapType::from_raw_tag(val.tag()) == Some(U::ty()) {
                // SAFETY: We just checked that the type matches, so this is sound
                unsafe { U::try_read(val) }
            } else {
                None
            }
        }).ok_or(self)
    }

    pub fn try_into_boxed(mut self) -> Result<T, Self> {
        let out = self.0.try_read(|val| {
            if HeapType::from_raw_tag(val.tag()) == Some(HeapType::Box) {
                let ptr = <*mut T as RawStore>::from_val(val);
                // SAFETY: Since type matches, this value was leaked from a box
                Some(unsafe { *Box::from_raw(ptr) })
            } else {
                None
            }
        });

        match out {
            Some(val) => {
                self.0 = RawBox::from_f64(f64::NAN);
                Ok(val)
            }
            None => Err(self),
        }
    }
}

impl<'a, T> Clone for NanBox<'a, T>
where
    T: Clone,
{
    fn clone(&self) -> Self {
        let tag = self.0.tag().and_then(HeapType::from_raw_tag);

        match tag {
            None => NanBox::from_f64(*self.0.ref_f64().unwrap()),
            Some(HeapType::Int) => {
                let data = self.0.ref_val().unwrap().ref_data();
                NanBox::from_raw(RawBox::from_value(Value::new(HeapType::Int.raw_tag(), *data)))
            }
            Some(tag @ (HeapType::Ptr | HeapType::MutPtr | HeapType::Ref)) => {
                let ptr = self.0.read(<*const T>::from_val).unwrap();
                NanBox::from_raw(RawBox::from_value(Value::store(tag.raw_tag(), ptr)))
            }
            Some(HeapType::Box) => {
                let ptr = self.0.read(<*const T>::from_val).unwrap();
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
            None => self.0.ref_f64() == other.0.ref_f64(),
            Some(HeapType::Int | HeapType::Ptr | HeapType::MutPtr) => {
                self.0.ref_val().map(Value::ref_data) == other.0.ref_val().map(Value::ref_data)
            },
            Some(HeapType::Ref | HeapType::Box) => {
                let ptr1 = self.0.read(<*const T>::from_val)
                    .unwrap();
                let ptr2 = other.0.read(<*const T>::from_val)
                    .unwrap();

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
                let ty = int_ty(self.0.ref_val().unwrap().ref_data());
                match ty {
                    IntType::Bool => "NanBox::Bool",
                    IntType::Char => "NanBox::Char",
                    IntType::U8 => "NanBox::U8",
                    IntType::U16 => "NanBox::U16",
                    IntType::U32 => "NanBox::U32",
                    IntType::I8 => "NanBox::I8",
                    IntType::I16 => "NanBox::I16",
                    IntType::I32 => "NanBox::I32",
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
                let val = self.0.ref_f64().unwrap();
                tuple.field(val);
            }
            Some(HeapType::Int) => {
                let bytes = self.0.ref_val().unwrap().ref_data();
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
                };
            }
            Some(HeapType::Ptr | HeapType::MutPtr) => {
                let ptr = self.0.read(<*const T>::from_val)
                    .unwrap();
                tuple.field(&ptr);
            }
            Some(HeapType::Ref | HeapType::Box) => {
                let ptr = self.0.read(<*const T>::from_val)
                    .unwrap();
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
            let ptr = self.0.read(<*mut T>::from_val).unwrap();
            drop(unsafe { Box::from_raw(ptr) });
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_roundtrip_f64() {
        let a = NanBox::<()>::from_f64(1.0);
        assert_eq!(a.try_into_f64(), Ok(1.0));

        let b = NanBox::<()>::from_f64(f64::NAN);
        assert_eq!(b.try_into_f64().unwrap().to_bits(), crate::nan::QUIET_NAN);
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
        let a = NanBox::<i32>::from_f64(1.0);
        let b = NanBox::<i32>::from_f64(-1.0);
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
