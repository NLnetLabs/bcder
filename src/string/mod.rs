//! BER encoding for various strings types.
//!
//! This module provides type that match the various string encodings provided
//! by ASN.1 and BER.
//!
//! The most basic string type is [`OctetString`] which is simply a sequence
//! of octets.

//--- Re-exports

pub use self::bstring::{BitString, BitStringIter};
pub use self::cstring::{CharSet, CharString, PrintableString, CharSetError};
pub use self::ostring::{
    OctetString, OctetStringEncoder, OctetStringIter, OctetStringOctets,
    OctetStringSource, WrappingOctetStringEncoder
};

//--- Private modules

mod bstring;
mod cstring;
mod ostring;

