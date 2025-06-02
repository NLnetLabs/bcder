
use std::str;
use std::borrow::Cow;
use crate::ident::Tag;
use super::charset::{
    CharSet, CharSetDecoder, CharSetDirectDecoder, CharSetDirectEncoder,
    CharSetEncoder, CharSetError,
};
use super::string::RestrictedString;


//------------ Ia5String -----------------------------------------------------

/// A restricted character string containing ASCII characters.
///
/// This character string allows all ASCII characters (i.e., octets with
/// values `0x00` to `0x7F`) and encodes them with their ASCII value.
///
/// The type’s name is derived from the name used in ASN.1. It is derived
/// from the name IA5 or International Alphabet No. 5 which is the ITU name
/// for ASCII and is specified in ITU.T recommendation T.50.
///
/// See [`RestrictedString`] for more details on restricted character strings
/// in general.
pub type Ia5String = RestrictedString<Ia5CharSet>;


//------------ Ia5CharSet ----------------------------------------------------

/// The character set for the IA5String ASN.1 type.
#[derive(Clone, Copy, Debug, Default)]
pub struct Ia5CharSet;

impl Ia5CharSet {
    fn check_slice(slice: &[u8]) -> Result<(), CharSetError> {
        if slice.iter().copied().all(|ch| ch.is_ascii()) {
            Ok(())
        }
        else {
            Err(CharSetError::default())
        }
    }
}

impl CharSet for Ia5CharSet {
    const TAG: Tag = Tag::IA5_STRING;

    type Decoder = Self;
    type Encoder = Self;
}

impl CharSetDecoder for Ia5CharSet {
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

impl CharSetDirectDecoder for Ia5CharSet {
    unsafe fn decode_slice_direct(slice: &[u8]) -> &str {
        unsafe { str::from_utf8_unchecked(slice) }
    }
}

impl CharSetEncoder for Ia5CharSet {
    type Error = CharSetError;

    fn encode_str(slice: &str) -> Result<Cow<[u8]>, Self::Error> {
        Self::check_slice(slice.as_bytes())?;
        Ok(Cow::Borrowed(slice.as_bytes()))
    }
}

impl CharSetDirectEncoder for Ia5CharSet {
    fn encode_str_direct(slice: &str) -> Result<&[u8], Self::Error> {
        Self::check_slice(slice.as_bytes())?;
        Ok(slice.as_bytes())
    }
}

