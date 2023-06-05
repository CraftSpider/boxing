//! Implementations of NaN-boxes, with support for strict-typing and a clean primitive for building
//! your own.
//!
//! # What is a NaN Box?
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

pub mod heap;
pub mod raw;
mod singlenan;

pub use heap::NanBox;
pub use raw::RawBox;
pub use singlenan::SingleNaNF64;

const SIGN_MASK: u64 = 0x7FFF_FFFF_FFFF_FFFF;
const QUIET_NAN: u64 = 0x7FF8_0000_0000_0000;
const NEG_QUIET_NAN: u64 = 0xFFF8_0000_0000_0000;
