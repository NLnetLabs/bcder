//! The BER mode.
//!
//! This is a private module. It’s public items are re-exported by the parent.

use crate::decode;


//------------ Mode ----------------------------------------------------------

/// The BER Mode.
///
/// X.680 defines not one but three sets of related encoding rules. All three
/// follow the same basic ideas but implement them in slightly different
/// ways.
///
/// This type represents these rules. The [`decode`] method provides a way to
/// decode a source using the specific decoding mode. You can also change
/// the decoding mode later on through the `set_mode` methods of [`Primitive`]
/// and [`Constructed`].
///
/// [`decode´]: #method.decode
/// [`Primitive`]: decode/struct.Primitive.html
/// [`Constructed`]: decode/struct.Constructed.html
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Mode {
    /// Basic Encoding Rules.
    ///
    /// These are the most flexible rules, allowing alternative encodings for
    /// some types as well as indefinite length values.
    Ber,

    /// Canonical Encoding Rules.
    ///
    /// These rules always employ indefinite length encoding for constructed
    /// values and the shortest possible form for primitive values.  There
    /// are additional restrictions for certain types.
    Cer,

    /// Distinguished Encoding Rules.
    ///
    /// These rules always employ definite length values and require the
    /// shortest possible encoding. Additional rules apply to some types.
    Der,
}

impl Mode {
    /// Decode a source using a specific mode.
    ///
    /// The method will attempt to decode `source` using the rules represented
    /// by this value. The closure `op` will be given the content of the
    /// source as a sequence of values. The closure does not need to process
    /// all values in the source.
    pub fn decode<S, F, T>(self, source: S, op: F) -> Result<T, S::Err>
    where
        S: decode::Source,
        F: FnOnce(&mut decode::Constructed<S>) -> Result<T, S::Err>
    {
        decode::Constructed::decode(source, self, op)
    }

    /// Returns whether the mode is `Mode::Ber`.
    pub fn is_ber(self) -> bool {
        matches!(self, Mode::Ber)
    }

    /// Returns whether the mode is `Mode::Cer`.
    pub fn is_cer(self) -> bool {
        matches!(self, Mode::Cer)
    }

    /// Returns whether the mode is `Mode::Der`.
    pub fn is_der(self) -> bool {
        matches!(self, Mode::Der)
    }
}

impl Default for Mode {
    fn default() -> Self {
        Mode::Ber
    }
}

