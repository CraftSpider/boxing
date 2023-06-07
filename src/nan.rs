//! Implementations of NaN-boxes, with support for strict-typing and a clean primitive for building
//! your own.
//!
//! ## What is a NaN Box?
//!
//! A NaN Box is a form of data storage which takes advantage of the fact that IEEE floats have a
//! very large number of NaN representations - a full 6 bytes and 3 bits worth of them, in fact.
//! We can take advantage of that to store smaller data types, including integer or pointer values,
//! in those valid NaN representations.
//!
//! Now you might be saying 'wait, aren't pointers on 64 bit systems also 64 bit?' It's true that
//! the size of a pointer on 64 bit systems is <u class="mousetext" title="64 bits">8 bytes</u>, but
//! there's a secret - most systems only actually use the first <u class="mousetext" title="48 bits">6 bytes</u>
//! of address space. This means that we can store any pointer on most systems - they'll fit in the
//! <u class="mousetext" title="48 bits">6 bytes</u> storage
//!
//! ## Why use a NaN Box?
//!
//! NaN-boxing data is a technique most frequently used in interpreters, to save memory - they're
//! effectively a niche-optimized enum, where the niche is the NaN values of the stored float. This
//! can save up to 8 bytes of memory for every object, for minimal runtime cast, which adds up
//! quite fast.
//!
//! ## Limitations
//!
//! - Since all data must fit in the 6 bytes of space a float provides us, we cannot store
//!   wide-pointers, so all data stored must be `Sized`. This can be worked around by using
//!   double-indirection, storing a `Box<T: ?Sized>` or similar.
//!
//! ## Examples
//!
//! A general example of using [`NanBox`] with some large data type:
//!
//! ```
//! # use boxing::nan::{NanBox, NanBoxRef};
//! # #[cfg(not(miri))] {
//!
//! // The thing we're storing in our box - a data type in our program
//! #[derive(Debug)]
//! pub struct InterpValue<'a> {
//!     class: u64,
//!     fields: Vec<(String, NanBox<'a, InterpValue<'a>>)>,
//! }
//!
//! // We can make a list of boxes, which takes up the same amount of memory as a `Vec<f64>`
//! let mut values = vec![
//!     NanBox::from_float(1.0),
//!     NanBox::from_inline(4),
//!     NanBox::from_box(Box::new(
//!         InterpValue { class: 1, fields: vec![(String::from("foo"), NanBox::from_float(-1.0))] }
//!     )),
//! ];
//!
//! // We want to evaluate, say, +1 if the value is a float:
//! for v in &mut values {
//!     if let Some(f) = v.try_mut_float() {
//!         // If you look at `try_mut_float`, it actually returns a `&mut SingleNaNF64` - this type
//!         // protects from writing NaN values that might change the type of the box into not-a-float,
//!         // but it can be used drop-in like a float in most places.
//!         *f += 1.0;
//!     }
//! }
//!
//! // Alternatively, we want to read an object and get its fields:
//! for v in &values {
//!     if let Some(obj) = v.try_ref_boxed() {
//!         println!("{}", obj.fields[0].0);
//!     }
//! }
//! 
//! // For accessing multiple types at once, there are convenience functions for extracting them
//! // as an enum
//! for v in &values {
//!     match v.enum_ref() {
//!         NanBoxRef::Float(f) => println!("{}", f),
//!         NanBoxRef::Box(b) => println!("{:?}", b.fields),
//!         NanBoxRef::I32(i) => println!("{}", i),
//!         _ => panic!(),
//!     }
//! }
//!
//! // Final note: since every type is represented as a float, it's always safe and sound to turn
//! // one into a float with no branches. This can leak memory though, so be careful.
//! for v in values {
//!     // Prints 2.0, nan, and nan. Leaks `InterpValue`.
//!     println!("{}", v.into_float_unchecked());
//! }
//!
//! # }
//! ```
//!

pub mod heap;
pub mod raw;
mod singlenan;

pub use heap::{NanBox, NanBoxOwn, NanBoxRef, NanBoxMut};
pub use raw::{RawBox, RawOwn, RawRef, RawMut};
pub use singlenan::SingleNaNF64;

const SIGN_MASK: u64 = 0x7FFF_FFFF_FFFF_FFFF;
const QUIET_NAN: u64 = 0x7FF8_0000_0000_0000;
const NEG_QUIET_NAN: u64 = 0xFFF8_0000_0000_0000;
