//! UTF8 strings.
//!
//! XXX This should probably be its own type rather than using
//! `RestrictedString` since valid content can be converted infallibly into
//! a `str`.

use std::{error, fmt, str};
use std::borrow::Cow;
use std::convert::Infallible;
use crate::ident::Tag;
use super::charset::{
    CharSet, CharSetDecoder, CharSetDirectDecoder, CharSetDirectEncoder,
    CharSetEncoder,
};
use super::string::RestrictedString;


//------------ Utf8String ----------------------------------------------------

/// A restricted character string containing UTF-8 encoded characters.
///
/// This character string allows all Unicode code points. It represents them
/// as a sequence of octets according to the UTF-8 encoding defined in
/// [RFC 3629].
///
/// See [`RestrictedString`] for more details on restricged character strings
/// in general.
///
/// [`RestrictedString`]: struct.RestrictedString.html
/// [RFC 3629]: https://tools.ietf.org/html/rfc3629
pub type Utf8String = RestrictedString<Utf8CharSet>;


//------------ Utf8CharSet ---------------------------------------------------

pub struct Utf8CharSet;

impl CharSet for Utf8CharSet {
    const TAG: Tag = Tag::UTF8_STRING;

    type Decoder = Utf8Decoder;
    type Encoder = Utf8Encoder;
}


//------------ Utf8Decoder ---------------------------------------------------

#[derive(Default)]
pub struct Utf8Decoder {
    pending: Pending
}

impl CharSetDecoder for Utf8Decoder {
    type Error = Utf8Error;

    fn check_next(&mut self, slice: &[u8]) -> Result<(), Self::Error> {
        let slice = self.pending.split_head(slice)?;
        match str::from_utf8(slice) {
            Ok(_) => {
                // The slice contained a complete UTF-8 sequence. Nothing
                // to pending over.
                Ok(())
            }
            Err(err) if err.error_len().is_some() => {
                // An invalid byte was encountered. This is an error.
                self.pending = Pending::Err;
                Err(Utf8Error(()))
            }
            Err(err) => {
                // Early end of input reached. Take what we need to carry
                // over and return success.
                match slice.get(err.valid_up_to()..) {
                    Some(slice) => {
                        self.pending.update(slice)?;
                        Ok(())
                    }
                    None => {
                        // The error was broken. Let’s return an error here.
                        self.pending = Pending::Err;
                        Err(Utf8Error(()))
                    }
                }
            }
        }
    }

    fn check_final(&mut self) -> Result<(), Self::Error> {
        if !matches!(self.pending, Pending::None) {
            Err(Utf8Error(()))
        }
        else {
            Ok(())
        }
    }

    fn decode_slice_lossy(slice: &[u8]) -> Cow<str> {
        String::from_utf8_lossy(slice)
    }
}

impl CharSetDirectDecoder for Utf8Decoder {
    unsafe fn decode_slice_direct(slice: &[u8]) -> &str {
        str::from_utf8_unchecked(slice)
    }
}


//------------ Utf8Encoder ---------------------------------------------------

#[derive(Default)]
pub struct Utf8Encoder;

impl CharSetEncoder for Utf8Encoder {
    type Error = Infallible;


    fn encode_str(slice: &str) -> Result<Cow<[u8]>, Self::Error> {
        Ok(Cow::Borrowed(slice.as_bytes()))
    }
}

impl CharSetDirectEncoder for Utf8Encoder {
    fn encode_str_direct(slice: &str) -> Result<&[u8], Self::Error> {
        Ok(slice.as_bytes())
    }
}


//------------ Pending -------------------------------------------------------

#[derive(Clone, Copy, Default)]
enum Pending {
    #[default]
    None,
    One,
    Two,
    Three,
    Err,
}

impl Pending {
    fn split_head<'a>(
        &mut self, slice: &'a [u8]
    ) -> Result<&'a [u8], Utf8Error> {
        match *self {
            Self::None => Ok(slice),
            Self::Err => Err(Utf8Error(())),
            Self::One => {
                match Self::take_first(slice) {
                    Ok(None) => Ok(slice),
                    Ok(Some(tail)) => {
                        *self = Self::None;
                        Ok(tail)
                    }
                    Err(err) => {
                        *self = Self::Err;
                        Err(err)
                    }
                }
            }
            Self::Two => {
                match Self::take_first(slice) {
                    Ok(None) => Ok(slice),
                    Ok(Some(tail)) => {
                        *self = Self::One;
                        self.split_head(tail)
                    }
                    Err(err) => {
                        *self = Self::Err;
                        Err(err)
                    }
                }
            }
            Self::Three => {
                match Self::take_first(slice) {
                    Ok(None) => Ok(slice),
                    Ok(Some(tail)) => {
                        *self = Self::Two;
                        self.split_head(tail)
                    }
                    Err(err) => {
                        *self = Self::Err;
                        Err(err)
                    }
                }
            }
        }
    }

    fn take_first(slice: &[u8]) -> Result<Option<&[u8]>, Utf8Error> {
        let Some((&head, tail)) = slice.split_first() else {
            return Ok(None)
        };
        if head & 0b1100_0000 == 0b1000_0000 {
            return Err(Utf8Error(()))
        }
        Ok(Some(tail))
    }

    fn update(&mut self, slice: &[u8]) -> Result<(), Utf8Error> {
        // slice is the beginning of a UTF-8 character. Determine how many
        // bytes we should have, check that the ones we do have are valid,
        // then set *self to how many we are missing.
        //
        // If slice doesn’t make sense vis-a-vis what we are expecting, we
        // end processing with prejudice.
        let Some((&first, tail)) = slice.split_first() else {
            *self = Self::Err;
            return Err(Utf8Error(()))
        };
        if first & 0b1110_0000 == 0b1100_0000 {
            // One extra byte. tail should be empty now.
            if tail.is_empty() {
                *self = Self::One;
                Ok(())
            }
            else {
                *self = Self::Err;
                Err(Utf8Error(()))
            }
        }
        else if first & 0b1111_0000 == 0b1110_0000 {
            // Two extra bytes. tail can have at most one byte.
            if tail.get(1).is_some() {
                *self = Self::Err;
                Err(Utf8Error(()))
            }
            else if let Some(first) = tail.first().copied() {
                if first & 0b1100_0000 != 0b1000_0000 {
                    *self = Self::Err;
                    Err(Utf8Error(()))
                }
                else {
                    *self = Self::One;
                    Ok(())
                }
            }
            else {
                *self = Self::Two;
                Ok(())
            }
        }
        else if first & 0b1111_1000 == 0b1111_0000 {
            // Three extra bytes. tail can have at most two bytes.
            if tail.get(2).is_some() {
                *self = Self::Err;
                Err(Utf8Error(()))
            }
            else if let Some(value) = tail.get(1).copied() {
                if value & 0b1100_0000 != 0b1000_0000 {
                    *self = Self::Err;
                    Err(Utf8Error(()))
                }
                else {
                    *self = Self::One;
                    Ok(())
                }
            }
            else if let Some(first) = tail.first().copied() {
                if first & 0b1100_0000 != 0b1000_0000 {
                    *self = Self::Err;
                    Err(Utf8Error(()))
                }
                else {
                    *self = Self::Two;
                    Ok(())
                }
            }
            else {
                *self = Self::Three;
                Ok(())
            }
        }
        else {
            // Either the first octet is a single character sequence or it is
            // illegal.
            *self = Self::Err;
            Err(Utf8Error(()))
        }
    }
}


//------------ Utf8Error -----------------------------------------------------

#[derive(Debug)]
pub struct Utf8Error(());

impl fmt::Display for Utf8Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str("invalid UTF-8")
    }
}

impl error::Error for Utf8Error { }

