//! Handling of data in Basic Encoding Rules.
//!
//! This crate allows decoding and encoding of data encoded in ASN.1’s _Basic
//! Encoding Rules_ as defined in ITU recommendation X.690 as well as their
//! stricter companions _Cannonical Encoding Rules_ and _Distringuished
//! Encoding Rules._
//!
//! You will find a short introduction to ASN.1 and encoding rules as well
//! as a discussion of how decoding and encoding with the crate work in
//! the [guide] module. The documentation with all the other
//! modules serves as a reference documentation.
//!
//! The most important modules of the crate are [decode] and [encode] that
//! provide the machinery for implementing decoding and encoding of data.
//! 
//! Additionally, the crate provides a number of types that help dealing
//! with the more complex universal types in ASN.1. Specifically, the
//! module [int] provides variable length integers, the module
//! [string] contains types for the various kinds of strings defined in
//! ASN.1, and [oid] deals with object identifiers. Finally, [captured]
//! provides a way to keep encoded data around for later processing.
//! The most important types from these modules are also re-exported at
//! library level.
//!
//! [guide]: guide/index.html
//! [decode]: decode/index.html
//! [encode]: encode/index.thml
//! [about_asn1]: about_asn1/index.html
//! [int]: int/index.html
//! [string]: string/index.html
//! [oid]: oid/index.html
//! [captured]: captured/index.html
#![allow(renamed_and_removed_lints, unknown_lints)]

// We have seemingly redundant closures (i.e., closures where just providing
// a function would also work) that cannot be removed due to lifetime issues.
#![allow(redundant_closure)]

//--- Re-exports

pub use self::captured::Captured;
pub use self::int::{Integer, Unsigned};
pub use self::mode::Mode;
pub use self::oid::{ConstOid, Oid};
pub use self::string::{
    BitString, OctetString,
    Ia5String, NumericString, PrintableString, Utf8String,
};
pub use self::tag::Tag;


//--- Public modules

#[macro_use] pub mod debug;

pub mod decode;
pub mod encode;

pub mod captured;
pub mod int;
pub mod oid;
pub mod string;


//--- Private modules

mod length;
mod mode;
mod tag;

//--- Elaborate documentation
//
pub mod guide;

