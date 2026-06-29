//! The encoding mode.
//!
//! The Basic Encoding Rules are relatively flexible when it comes to how
//! values are encoded. While this can be useful to adapt to a given use case,
//! it also means that there is no one encoding for a given value. For cases
//! where this is necessary, the standard defines two restricted modes, known
//! as the Canonical Encoding Rules (CER) and the Distinguished Encoding Rules
//! (DER) which remove such choices and guarantee that any given value is
//! encoded with exactly one bit pattern. They achieve this in two different
//! ways which means that CER is best used in streaming situations when size
//! and content of value isn’t known up front while DER requires the value to
//! be fully available before encoding.
//!
//! In _bcder_ the encoding mode is represented by the three marker types
//! defined in this module. All the types and functions used for decoding
//! and encoding are generic over the mode. This makes it possible to
//! require a certain mode when implementing decoding and encoding for
//! certain types. For instance, X.509 certificates are always encoded using
//! DER, so only decoding and encoding for DER makes sense.

/// Basic Encoding Rules.
///
/// These are the most flexible rules, allowing alternative encodings for
/// some types as well as both definite and indefinite length values.
//
//  XXX We derive all the things for now so we can derive them on types that
//      are generic over the mode but will replace the derives later.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Ber;

/// Canonical Encoding Rules.
///
/// These rules always employ indefinite length encoding for constructed
/// values and the shortest possible form for primitive values.  There
/// are additional restrictions for certain types.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Cer;

/// Distinguished Encoding Rules.
///
/// These rules always employ definite length values and require the
/// shortest possible encoding. Additional rules apply to some types.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Der;

/// One of the modes.
///
/// The trait defines a number of constants that allow implementations that
/// are generic over the particular mode to branch on them which in turn
/// allows the compiler to remove the unused branches during monomorphization
/// when a concrete mode is used.
pub trait Mode: 'static {
    /// Is this mode CER?
    const IS_CER: bool;

    /// Is this mode DER?
    const IS_DER: bool;

    /// Is this mode CER or DER?
    const IS_RESTRICTED: bool;

    /// Does this mode allow definite-length constructed values?
    ///
    /// This is `true` for [`BER`] and [`DER`].
    const ALLOW_DEFINITE_CONSTRUCTED: bool;

    /// Does this mode allow indefinite length constructed values?
    ///
    /// This is `true` for [`BER`] and [`CER`].
    const ALLOW_INDEFINITE_CONSTRUCTED: bool;
}

impl Mode for Ber {
    const IS_CER: bool = false;
    const IS_DER: bool = false;
    const IS_RESTRICTED: bool = false;
    const ALLOW_DEFINITE_CONSTRUCTED: bool = true;
    const ALLOW_INDEFINITE_CONSTRUCTED: bool = true;
}

impl Mode for Cer {
    const IS_CER: bool = true;
    const IS_DER: bool = false;
    const IS_RESTRICTED: bool = true;
    const ALLOW_DEFINITE_CONSTRUCTED: bool = false;
    const ALLOW_INDEFINITE_CONSTRUCTED: bool = true;
}

impl Mode for Der {
    const IS_CER: bool = false;
    const IS_DER: bool = true;
    const IS_RESTRICTED: bool = true;
    const ALLOW_DEFINITE_CONSTRUCTED: bool = true;
    const ALLOW_INDEFINITE_CONSTRUCTED: bool = false;
}

/// Either BER or CER mode.
///
/// Those are the modes that allow indefinite length form constructed
/// values.
///
/// (This trait only exists because we currently can’t require
/// `Mode::ALLOW_INDEFINITE_CONSTRUCTED` to be `true` in a trait bound.)
pub trait BerCer { }

impl BerCer for Ber { }
impl BerCer for Cer { }

