
use std::str;
use std::borrow::Cow;
use crate::ident::Tag;
use super::charset::{
    CharSet, CharSetDecoder, CharSetDirectDecoder, CharSetDirectEncoder,
    CharSetEncoder, CharSetError,
};
use super::string::RestrictedString;


//------------ PrintableString -----------------------------------------------

/// A restricted character string allowing a subset of ASCII characters.
///
/// This character string allows the following characters from the ASCII
/// character set and encodes them with their ASCII value:
///
/// * the letters `A` to `Z` and `a` to `z`,
/// * the digits `0` to `9`,
/// * the space character ` `,
/// * the symbols `'`, `(`, `)`, `+`, `,`, `-`, `.`, `/`, `:`, `=`, and `?`.
///
/// See [`RestrictedString`] for more details on restricted character strings
/// in general.
pub type PrintableString = RestrictedString<PrintableCharSet>;


//------------ PrintableCharSet ----------------------------------------------

/// The character set for the PrintableString ASN.1 type.
#[derive(Clone, Debug, Default)]
pub struct PrintableCharSet;

impl PrintableCharSet {
    fn check_slice(slice: &[u8]) -> Result<(), CharSetError> {
        if slice.iter().copied().all(|x| {
            x.is_ascii_alphanumeric() || // A-Z a-z 0-9
            x == b' ' || x == b'\'' || x == b'(' || x == b')' ||
            x == b'+' || x == b',' || x == b'-' || x == b'.' ||
            x == b'/' || x == b':' || x == b'=' || x == b'?'
        }) {
            Ok(())
        }
        else {
            Err(CharSetError::default())
        }
    }
}

impl CharSet for PrintableCharSet {
    const TAG: Tag = Tag::PRINTABLE_STRING;

    type Decoder = Self;
    type Encoder = Self;
}

impl CharSetDecoder for PrintableCharSet {
    type Error = CharSetError;

    fn check_next(&mut self, slice: &[u8]) -> Result<(), Self::Error> {
        Self::check_slice(slice)
    }

    fn check_final(&mut self) -> Result<(), Self::Error> {
        Ok(())
    }

    fn decode_slice_lossy(slice: &[u8]) -> Cow<str> {
        String::from_utf8_lossy(slice)
    }
}

impl CharSetDirectDecoder for PrintableCharSet {
    unsafe fn decode_slice_direct(slice: &[u8]) -> &str {
        str::from_utf8_unchecked(slice)
    }
}

impl CharSetEncoder for PrintableCharSet {
    type Error = CharSetError;

    fn encode_str(slice: &str) -> Result<Cow<[u8]>, Self::Error> {
        Self::check_slice(slice.as_bytes())?;
        Ok(Cow::Borrowed(slice.as_bytes()))
    }
}

impl CharSetDirectEncoder for PrintableCharSet {
    fn encode_str_direct(slice: &str) -> Result<&[u8], Self::Error> {
        Self::check_slice(slice.as_bytes())?;
        Ok(slice.as_bytes())
    }
}

