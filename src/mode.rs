//! The BER mode.
//!
//! 


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

/// One of the restricted rules CER or DER.
///
/// Some restrictions to the basic rules are shared between CER and DER.
/// This trait allows implementations to do both.
pub trait Restricted { }

impl Restricted for Cer { }
impl Restricted for Der { }

/// One of the modes.
pub trait Mode {
    /// Is this mode CER or DER?
    const IS_RESTRICTED: bool;

    /// Does this mode allow definite-length constructed values?
    const ALLOW_DEFINITE_CONSTRUCTED: bool;

    /// Does this mode allow indefinite length constructed values?
    const ALLOW_INDEFINITE_CONSTRUCTED: bool;
}

impl Mode for Ber {
    const IS_RESTRICTED: bool = false;
    const ALLOW_DEFINITE_CONSTRUCTED: bool = true;
    const ALLOW_INDEFINITE_CONSTRUCTED: bool = true;
}

impl Mode for Cer {
    const IS_RESTRICTED: bool = true;
    const ALLOW_DEFINITE_CONSTRUCTED: bool = false;
    const ALLOW_INDEFINITE_CONSTRUCTED: bool = true;
}

impl Mode for Der {
    const IS_RESTRICTED: bool = true;
    const ALLOW_DEFINITE_CONSTRUCTED: bool = true;
    const ALLOW_INDEFINITE_CONSTRUCTED: bool = false;
}

