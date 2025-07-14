//! BER encoding for various strings types.
//!
//! This module provides type that match the various string encodings provided
//! by ASN.1 and BER.
//!
//! There are two types of strings for binary data. [`OctetString`]s contain
//! a unrestricted sequence of octets while [`BitString`]s contain a sequence
//! of bits that does not need to be of a length divisible by eight.
//!
//! In addition, there are a number of so-called restricted character strings
//! that each conain a sequence of characters according to a pre-defined
//! character set. ASN.1 defines quite a few of those of which the crate
//! currently only implements a subset that is commonly in use. Specifically:
//!
//! * [`Ia5String`] contains ASCII characters only (IA5 is an alternative
//!   name for ASCII),
//! * [`NumericString`] contains only decimals digits and spaces,
//! * [`PrintableString`] contains a subset of ASCII characters including
//!   letters, digits, and a few symbols,
//! * [`Utf8String`] contains a sequence of Unicode code points encoded as
//!   octets through UTF-8.
//!
//! All of these are implemented atop a generic [`RestrictedString`] by
//! providing an implementation for the [`CharSet`] trait.

//--- Re-exports

pub use self::bit::{BitString, BitStringError, BitStringTarget};
pub use self::restricted::{
    CharSetError, Ia5String, NumericString, PrintableString,
    RestrictedString, Utf8String,
};
pub use self::octet::{OctetString, OctetStringArray};


//--- Private modules

mod bit;
mod restricted;
mod octet;


