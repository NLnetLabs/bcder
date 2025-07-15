
use std::{error, fmt};
use std::borrow::Cow;
use crate::ident::Tag;


//------------ CharSet -------------------------------------------------------

/// The character set of a restricted character string type.
///
/// The trait is primarily used to define the character set of the
/// [`RestrictedString`] type.
pub trait CharSet {
    /// The natural tag of the related restricted character string type.
    const TAG: Tag;

    /// The type for decoding byte sequences into UTF-8 strings.
    ///
    /// This type is also used for checking a sequence.
    type Decoder: CharSetDecoder;

    /// The type for encoding UTF-8 strings into byte sequences.
    type Encoder: CharSetEncoder;
}

/// A type that can decode data in a character set.
pub trait CharSetDecoder: Default {
    /// The error type of the decoder.
    type Error: error::Error + Send + Sync + 'static;

    //--- Required methods

    /// Checks the next slice of a sequence.
    ///
    /// The slice may be empty.
    fn check_next(&mut self, slice: &[u8]) -> Result<(), Self::Error>;

    /// Checks the end of a sequence.
    fn check_final(&mut self) -> Result<(), Self::Error>;

    /*
    /// Decodes the next slice of a sequence.
    ///
    /// The slice may be empty.
    ///
    /// Appends whatever it decoded to `target`.
    fn decode_next(
        &mut self, slice: &[u8], target: &mut String
    ) -> Result<(), Self::Error>;

    /// Decodes the end of a sequence.
    ///
    /// Appends whatever is left to `target`.
    fn decode_final(
        &mut self, target: &mut String
    ) -> Result<(), Self::Error>;
    */

    fn decode_slice_lossy(slice: &[u8]) -> Cow<'_, str>;

    /// Checks a slice.
    fn check_slice(slice: &[u8]) -> Result<(), Self::Error> {
        let mut this = Self::default();
        this.check_next(slice)?;
        this.check_final()
    }
}

pub trait CharSetDirectDecoder: CharSetDecoder {
    unsafe fn decode_slice_direct(slice: &[u8]) -> &str;
}

/// A type that can encode a string into a certain character set.
pub trait CharSetEncoder: Default {
    /// The error type of the decoder.
    type Error: error::Error + Send + Sync + 'static;

    /*
    fn encode_next(
        &mut self, slice: &str, target: &mut Vec<u8>
    ) -> Result<(), Self::Error>;

    fn encode_final(
        &mut self, target: &mut Vec<u8>
    ) -> Result<(), Self::Error>;
    */

    fn encode_str(slice: &str) -> Result<Cow<'_, [u8]>, Self::Error>;
}

/// A character set encoder that doesn’t need to change the string.
///
/// If an encoder implements this trait, the character set encodes a subset
/// of UTF-8 and an encoded str is thus not going to change.
pub trait CharSetDirectEncoder: CharSetEncoder {
    fn encode_str_direct(slice: &str) -> Result<&[u8], Self::Error>;
}


//------------ CharSetError --------------------------------------------------

#[derive(Debug, Default)]
pub struct CharSetError(());

impl fmt::Display for CharSetError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str("invalid characters")
    }
}

impl error::Error for CharSetError { }

