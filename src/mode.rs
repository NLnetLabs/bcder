//! The BER mode.


/// Basic Encoding Rules.
///
/// These are the most flexible rules, allowing alternative encodings for
/// some types as well as indefinite length values.
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
    const ALLOW_DEFINITE_CONSTRUCTED: bool;

    /// Does this mode allow indefinite length constructed values?
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
pub trait BerCer { }

impl BerCer for Ber { }
impl BerCer for Cer { }
