pub mod heap;
pub mod raw;
mod singlenan;

pub use raw::RawBox;
pub use singlenan::SingleNaNF64;

const SIGN_MASK: u64 = 0x7FFF_FFFF_FFFF_FFFF;
const QUIET_NAN: u64 = 0x7FF8_0000_0000_0000;
const NEG_QUIET_NAN: u64 = 0xFFF8_0000_0000_0000;
