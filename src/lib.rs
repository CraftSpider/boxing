//! A library for pointer and NaN boxing data - storing other data values in the unused portions
//! of a float or pointer.
//!
//! ## Examples
//!
//! For more detailed examples, see the [`nan`] module documentation.
//!
//! ```
//! use boxing::nan::NanBox;
//!
//! assert_eq!(core::mem::size_of::<NanBox<()>>(), core::mem::size_of::<f64>());
//!
//! let a = NanBox::<()>::from_float(2.0);
//! let b = NanBox::<()>::from_inline(-1i32);
//!
//! assert_eq!(a.clone().try_into_float(), Ok(2.0));
//! assert_eq!(b.clone().try_into_inline::<i32>(), Ok(-1i32));
//! assert!((a.into_float_unchecked() + b.into_float_unchecked()).is_nan());
//!
//! ```
//!

#![warn(
    missing_docs,
    elided_lifetimes_in_paths,
    explicit_outlives_requirements,
    missing_abi,
    noop_method_call,
    pointer_structural_match,
    semicolon_in_expressions_from_macros,
    unused_import_braces,
    unused_lifetimes,
    unsafe_op_in_unsafe_fn,
    clippy::cargo,
    clippy::missing_panics_doc,
    clippy::doc_markdown,
    clippy::ptr_as_ptr,
    clippy::cloned_instead_of_copied,
    clippy::unreadable_literal,
    clippy::undocumented_unsafe_blocks,
    clippy::cast_sign_loss,
    clippy::cast_precision_loss,
    clippy::cast_possible_truncation,
    clippy::cast_possible_wrap
)]

pub mod nan;
mod utils;
