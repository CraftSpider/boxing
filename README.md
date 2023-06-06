
# Boxing

[![crates.io](https://img.shields.io/crates/v/boxing.svg)](https://crates.io/crates/boxing)
[![Documentation](https://docs.rs/boxing/badge.svg)](https://docs.rs/boxing)
[![MIT/Apache-2 licensed](https://img.shields.io/crates/l/boxing.svg)](./LICENSE-APACHE)

An easy-to-use, cross-platform library for pointer and NaN boxing data - storing other data
values in the unused portions of a float or pointer.

## Examples

For more detailed examples, see the `nan` module documentation.

```rust
use boxing::nan::NanBox;

assert_eq!(core::mem::size_of::<NanBox<()>>(), core::mem::size_of::<f64>());

let a = NanBox::<()>::from_float(2.0);
let b = NanBox::<()>::from_inline(-1i32);

assert_eq!(a.clone().try_into_float(), Ok(2.0));
assert_eq!(b.clone().try_into_inline::<i32>(), Ok(-1i32));
assert!((a.into_float_unchecked() + b.into_float_unchecked()).is_nan());
```
