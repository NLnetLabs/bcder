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
//!
//! [`OctetString`]: struct.OctetString.html
//! [`BitString`]: struct.BitString.html
//! [`Ia5String`]: struct.Ia5String.html
//! [`NumericString`]: struct.NumericString.html
//! [`PrintableString`]: struct.PrintableString.html
//! [`Utf8String`]: struct.Utf8String.html
//! [`RestrictedString`]: struct.RestrictedString.html
//! [`CharSet`]: trait.CharSet.html

//--- Re-exports

pub use self::bit::{BitString, BitStringIter};
pub use self::bytes::BytesString;
pub use self::restricted::{
    CharSet, CharSetError,
    RestrictedString, RestrictedStringChars,
    Ia5String, NumericString, PrintableString, Utf8String
};
pub use self::octet::{
    OctetString, OctetStringEncoder, OctetStringIter, OctetStringOctets,
    OctetStringSource, WrappingOctetStringEncoder
};

//--- Private modules

mod bit;
mod bytes;
mod restricted;
mod octet;

