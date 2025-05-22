
use std::str;
use std::borrow::Cow;
use crate::ident::Tag;
use super::charset::{
    CharSet, CharSetDecoder, CharSetDirectDecoder, CharSetDirectEncoder,
    CharSetEncoder, CharSetError,
};
use super::string::RestrictedString;


//------------ NumericString -------------------------------------------------

/// A restricted character string containing only digits and spaces.
///
/// This character string allows only decimal digits `0` to `9` and the
/// space character ` `. It encodes them with their ASCII value.
///
/// See [`RestrictedString`] for more details on restricted character strings
/// in general.
pub type NumericString = RestrictedString<NumericCharSet>;


//------------ NumericCharSet ------------------------------------------------

/// The character set for the NumericString ASN.1 type.
#[derive(Clone, Copy, Debug, Default)]
pub struct NumericCharSet;

impl NumericCharSet {
    fn check_slice(slice: &[u8]) -> Result<(), CharSetError> {
        if slice.iter().copied().all(|ch| {
            ch == b' ' || ch.is_ascii_digit()
        }) {
            Ok(())
        }
        else {
            Err(CharSetError::default())
        }
    }
}

impl CharSet for NumericCharSet {
    const TAG: Tag = Tag::NUMERIC_STRING;

    type Decoder = Self;
    type Encoder = Self;
}

impl CharSetDecoder for NumericCharSet {
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

impl CharSetDirectDecoder for NumericCharSet {
    unsafe fn decode_slice_direct(slice: &[u8]) -> &str {
        str::from_utf8_unchecked(slice)
    }
}

impl CharSetEncoder for NumericCharSet {
    type Error = CharSetError;

    fn encode_str(slice: &str) -> Result<Cow<[u8]>, Self::Error> {
        Self::check_slice(slice.as_bytes())?;
        Ok(Cow::Borrowed(slice.as_bytes()))
    }
}

impl CharSetDirectEncoder for NumericCharSet {
    fn encode_str_direct(slice: &str) -> Result<&[u8], Self::Error> {
        Self::check_slice(slice.as_bytes())?;
        Ok(slice.as_bytes())
    }
}
