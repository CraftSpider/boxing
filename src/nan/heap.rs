use std::{fmt, mem, ptr};
use crate::nan::raw::{RawStore, RawTag, Value};
use crate::nan::{RawBox, SingleNaNF64};
use crate::utils::ArrayExt;
use std::marker::PhantomData;

fn write_int<I: IntInline>(val: I) -> [u8; 6] {
    let ty = (I::ty() as u16).to_ne_bytes();
    let val = val.to_bytes();
    [ty[0], ty[1], val[0], val[1], val[2], val[3]]
}

fn read_int<I: IntInline>(bytes: [u8; 6]) -> Option<I> {
    if IntType::from_u16(u16::from_ne_bytes([bytes[0], bytes[1]])) == I::ty() {
        I::from_bytes([bytes[2], bytes[3], bytes[4], bytes[5]])
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
    // Removed because it means we can't implement `Clone`
    // MutRef = 5,

    Box = 6,
}

impl HeapType {
    fn raw_tag(self) -> RawTag {
        RawTag::new(false, self as u8)
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
            // 5 => HeapType::MutRef,
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
    fn from_bytes(bytes: [u8; 4]) -> Option<Self>;
}

pub trait HeapInline<T>: Sized {
    fn ty() -> HeapType;
    fn write(self, value: &mut Value);
    fn try_read(value: &Value) -> Option<Self>;
}

macro_rules! impl_int {
    ($ty:ty, $variant:ident) => {
        impl<T> HeapInline<T> for $ty {
            fn ty() -> HeapType {
                HeapType::Int
            }

            fn write(self, value: &mut Value) {
                value.write(write_int(self))
            }

            fn try_read(value: &Value) -> Option<Self> {
                if HeapType::from_raw_tag(value.tag()) == Some(HeapType::Int) {
                    read_int(value.read())
                } else {
                    None
                }
            }
        }

        impl IntInline for $ty {
            fn ty() -> IntType {
                IntType::$variant
            }

            fn to_bytes(self) -> [u8; 4] {
                self.to_ne_bytes().truncate_to()
            }

            fn from_bytes(bytes: [u8; 4]) -> Option<Self> {
                Some(<$ty>::from_ne_bytes(bytes.truncate_to()))
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

    fn from_bytes(bytes: [u8; 4]) -> Option<Self> {
        Some(bytes[0] == 1)
    }
}

impl<T> HeapInline<T> for bool {
    fn ty() -> HeapType {
        HeapType::Int
    }

    fn write(self, value: &mut Value) {
        value.write(write_int(self));
    }

    fn try_read(value: &Value) -> Option<Self> {
        if HeapType::from_raw_tag(value.tag()) == Some(HeapType::Int) {
            read_int(value.read())
        } else {
            None
        }
    }
}

impl IntInline for char {
    fn ty() -> IntType {
        IntType::Char
    }

    fn to_bytes(self) -> [u8; 4] {
        u32::to_bytes(self as u32)
    }

    fn from_bytes(bytes: [u8; 4]) -> Option<Self> {
        u32::from_bytes(bytes).and_then(char::from_u32)
    }
}

impl<T> HeapInline<T> for char {
    fn ty() -> HeapType {
        HeapType::Int
    }

    fn write(self, value: &mut Value) {
        value.write(write_int(self));
    }

    fn try_read(value: &Value) -> Option<Self> {
        if HeapType::from_raw_tag(value.tag()) == Some(HeapType::Int) {
            read_int(value.read())
        } else {
            None
        }
    }
}

impl<T> HeapInline<T> for *const T {
    fn ty() -> HeapType {
        HeapType::Ptr
    }

    fn write(self, value: &mut Value) {
        RawStore::to_val(self, value);
    }

    fn try_read(value: &Value) -> Option<Self> {
        if HeapType::from_raw_tag(value.tag()) == Some(Self::ty()) {
            Some(RawStore::from_val(value))
        } else {
            None
        }
    }
}

impl<T> HeapInline<T> for *mut T {
    fn ty() -> HeapType {
        HeapType::MutPtr
    }

    fn write(self, value: &mut Value) {
        RawStore::to_val(self, value);
    }

    fn try_read(value: &Value) -> Option<Self> {
        if HeapType::from_raw_tag(value.tag()) == Some(Self::ty()) {
            Some(RawStore::from_val(value))
        } else {
            None
        }
    }
}

impl<'a, T> HeapInline<T> for &'a T {
    fn ty() -> HeapType {
        HeapType::Ref
    }

    fn write(self, value: &mut Value) {
        RawStore::to_val(self as *const T, value);
    }

    fn try_read(value: &Value) -> Option<Self> {
        if HeapType::from_raw_tag(value.tag()) == Some(Self::ty()) {
            Some(unsafe { &*<*const T as RawStore>::from_val(value) })
        } else {
            None
        }
    }
}

// impl<'a, T> HeapInline<T> for &'a mut T {
//     fn ty() -> HeapType {
//         HeapType::MutRef
//     }
// 
//     fn write(self, value: &mut Value) {
//         RawStore::to_val(self as *mut T, value);
//     }
// 
//     fn try_read(value: &Value) -> Option<Self> {
//         if HeapType::from_raw_tag(value.tag()) == Some(Self::ty()) {
//             Some(unsafe { &mut *<*mut T as RawStore>::from_val(value) })
//         } else {
//             None
//         }
//     }
// }

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
        let raw =
            RawBox::write(ty.raw_tag(), |b| U::write(val, b)).unwrap();
        NanBox::from_raw(raw)
    }

    #[must_use]
    pub fn from_box(val: Box<T>) -> NanBox<'a, T> {
        let raw = RawBox::write(
            HeapType::Box.raw_tag(),
            |v| <*mut T as HeapInline<_>>::write(Box::into_raw(val), v),
        )
        .unwrap();
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
    
    pub fn try_into_f64(mut self) -> Result<f64, Self> {
        let inner = mem::replace(&mut self.0, RawBox::from_f64(f64::NAN));
        inner.into_f64()
            .map_err(NanBox::from_raw)
    }
    
    pub fn try_into_inline<U: HeapInline<T> + 'a>(self) -> Result<U, Self> {
        self.0.try_read(|val| U::try_read(val))
            .ok_or(self)
    }
    
    pub fn try_into_boxed(mut self) -> Result<T, Self> {
        let out = self.0.try_read(|val| if HeapType::from_raw_tag(val.tag()) == Some(HeapType::Box) {
            let ptr = <*mut T as RawStore>::from_val(val);
            Some(unsafe { *Box::from_raw(ptr) })
        } else {
            None
        });
        
        match out {
            Some(val) => {
                self.0 = RawBox::from_val(HeapType::Box.raw_tag(), ptr::null::<T>()).unwrap();
                Ok(val)
            }
            None => Err(self)
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
            Some(HeapType::Int | HeapType::Ptr | HeapType::MutPtr) => self.0.ref_data() == other.0.ref_data(),
            Some(HeapType::Ref /*| HeapType::MutRef*/ | HeapType::Box) => {
                let ptr1 = self.0.read(<*const T>::from_val)
                    .unwrap();
                let ptr2 = other.0.read(<*const T>::from_val)
                    .unwrap();

                (unsafe { &*ptr1 }) == (unsafe { &*ptr2 })
            }
        }
    }
}

impl<'a, T> fmt::Debug for NanBox<'a, T>
where
    T: fmt::Debug
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let tag = self.0.tag().and_then(HeapType::from_raw_tag);
        
        let var = match tag {
            None => "NanBox::Float",
            Some(HeapType::Int) => {
                let data = self.0.ref_data().unwrap();
                match IntType::from_u16(u16::from_ne_bytes([data[0], data[1]])) {
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
            // Some(HeapType::MutRef) => "NanBox::Mut",
            Some(HeapType::Box) => "NanBox::Box",
        };
        
        let mut tuple = f.debug_tuple(var);
        
        match tag {
            None => {
                let val = self.0.ref_f64().unwrap();
                tuple.field(val);
            }
            Some(HeapType::Int) => {
                let data = self.0.ref_data().unwrap();
                let ty = IntType::from_u16(u16::from_ne_bytes([data[0], data[1]]));
                let bytes = [data[2], data[3], data[4], data[5]];
                match ty {
                    IntType::Bool => tuple.field(&bool::from_bytes(bytes).unwrap()),
                    IntType::Char => tuple.field(&char::from_bytes(bytes).unwrap()),
                    IntType::U8 => tuple.field(&u8::from_bytes(bytes).unwrap()),
                    IntType::U16 => tuple.field(&u16::from_bytes(bytes).unwrap()),
                    IntType::U32 => tuple.field(&u32::from_bytes(bytes).unwrap()),
                    IntType::I8 => tuple.field(&i8::from_bytes(bytes).unwrap()),
                    IntType::I16 => tuple.field(&i16::from_bytes(bytes).unwrap()),
                    IntType::I32 => tuple.field(&i32::from_bytes(bytes).unwrap()),
                };
            }
            Some(HeapType::Ptr | HeapType::MutPtr) => {
                let ptr = self.0.read(<*const T>::from_val)
                    .unwrap();
                tuple.field(&ptr);
            }
            Some(HeapType::Ref /*| HeapType::MutRef*/ | HeapType::Box) => {
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
            if !ptr.is_null() {
                drop(unsafe { Box::from_raw(ptr) });
            }
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
