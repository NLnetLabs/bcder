//! BER-encoded Restricted Character String types.
//!
//! This is an internal module. It’s public items are re-exported by the
//! parent.

use std::{char, cmp, fmt, hash, ops, str};
use std::borrow::Cow;
use std::marker::PhantomData;
use bytes::Bytes;
use crate::{decode, encode};
use crate::decode::DecodeError;
use crate::tag::Tag;
use super::octet::{OctetString, OctetStringIter, OctetStringOctets};


//------------ CharSet -------------------------------------------------------

/// The character set of a restricted character string type.
///
/// The trait only includes associated functions and can thus be implemented
/// for marker types. It main purpose is to take an iterator over `u8`s and
/// produce `char`s or errors. This happens in [`next_char`].
///
/// The trait is primarily used to define the character set of the
/// [`RestrictedString`] type.
///
/// [`next_char`]: #tymethod.next_char
/// [`RestrictedString`]: struct.RestrictedString.html
pub trait CharSet {
    /// The natural tag of the related restricted character string type.
    const TAG: Tag;

    /// Returns the next character from a octet sequence.
    fn next_char<I: Iterator<Item=u8>>(
        iter: &mut I
    ) -> Result<Option<char>, CharSetError>;

    /// Converts a `str` into a octet sequence.
    ///
    /// The method takes a `str` and converts it into one of three things.
    /// If the string can be encoded in this character set and its own octet
    /// sequence is identical to the encoded sequence, it returns its octet
    /// sequence as a `Ok(Cow::Borrowed(_))`. If the octet sequence differs,
    /// it creates that and returns it as a `Ok(Cow::Owned(_))`. Finally, if
    /// the string cannot be encoded in this character set, it returns an
    /// error.
    fn from_str(s: &str) -> Result<Cow<[u8]>, CharSetError>;

    /// Checks whether a sequence of octets is a valid string.
    ///
    /// The method returns an error if the sequence of the octets represented
    /// by `iter` is not in fact a valid string for this character set.
    fn check<I: Iterator<Item=u8>>(iter: &mut I) -> Result<(), CharSetError> {
        while Self::next_char(iter)?.is_some() { }
        Ok(())
    }
}


//------------ RestrictedString ----------------------------------------------

/// A generic restricted character string.
///
/// Restricted character strings essentially are a sequence of characters from
/// a specific character set mapped into a sequence of octets. In BER, these
/// are in fact encoded just like an [`OctetString`] with a different tag.
/// Consequently, this type is a wrapper around [`OctetString`] that makes
/// sure that the sequence of octets is correctly encoded for the given
/// character set.
///
/// As usual, you can parse a restricted character string from encoded data
/// by way of the [`take_from`] and [`from_content`] methods.
/// Alternatively, you can create a new value from a `String` or `str` via
/// the [`from_string`] and [`from_str`] associated functions.
///
/// Conversely, a restricted character string can be converted into a string
/// by way of the [`to_string`] and [`to_str`] methods.
///
/// In addition, the restricted character string mirrors the standard
/// library’s string types by dereffing to [`OctetString`] and using the
/// octet string’s iterators. In addition, the [`chars`] method provides an
/// iterator over the characters encoded in the string.
///
/// [`CharSet`]: trait.CharSet.html
/// [`OctetString`]: struct.OctetString.html
/// [`take_from`]: #method.take_from
/// [`from_content`]: #method.take_content
/// [`from_string`]: #method.from_string
/// [`from_str`]: #method.from_str
/// [`to_string`]: #method.to_string
/// [`to_str`]: #method.to_str
/// [`chars`]: #method.chars
#[derive(Clone, Debug)]
pub struct RestrictedString<L: CharSet> {
    /// The underlying octet string.
    octets: OctetString,

    /// Marker for our character set.
    marker: PhantomData<L>
}

impl<L: CharSet> RestrictedString<L> {
    /// Creates a new character string without any checks.
    unsafe fn new_unchecked(octets: OctetString) -> Self {
        RestrictedString {
            octets,
            marker: PhantomData
        }
    }

    /// Creates a new character string from an octet string.
    ///
    /// If the octet string contains octet sequences that are not valid for
    /// the character set, an appropriate error will be returned.
    pub fn new(os: OctetString) -> Result<Self, CharSetError> {
        L::check(&mut os.octets())?;
        Ok(unsafe { Self::new_unchecked(os) })
    }

    /// Creates a new character string from a `String`.
    ///
    /// If the string’s internal representation is identical to the encoding
    /// of restricted character string, the string will be reused and no
    /// allocation occurs. Otherwise, a new bytes value is created.
    ///
    /// If the string cannot be encoded in the character set, an error is
    /// returned.
    pub fn from_string(s: String) -> Result<Self, CharSetError> {
        let octets = match L::from_str(s.as_ref())? {
            Cow::Borrowed(_) => s.into_bytes().into(),
            Cow::Owned(owned) => owned.into(),
        };
        Ok(unsafe { Self::new_unchecked(OctetString::new(octets)) })
    }

    /// Returns an iterator over the character in the character string.
    pub fn chars(&self) -> RestrictedStringChars<L> {
        RestrictedStringChars::new(self.octets.octets())
    }

    /// Converts the string into its underlying bytes.
    ///
    /// Note that the bytes value will contain the raw octets of the string
    /// which are not necessarily a valid Rust string.
    pub fn into_bytes(self) -> Bytes {
        self.octets.into_bytes()
    }
}


/// # Decoding and Encoding
///
impl<L: CharSet> RestrictedString<L> {
    /// Takes a single character set value from constructed value content.
    ///
    /// If there is no next value, if the next value does not have the natural
    /// tag appropriate for this character set implementation, or if it does
    /// not contain a correctly encoded character string, a malformed error is
    /// returned.
    pub fn take_from<S: decode::Source>(
        cons: &mut decode::Constructed<S>
    ) -> Result<Self, DecodeError<S::Error>> {
        cons.take_value_if(L::TAG, Self::from_content)
    }

    /// Takes a character set from content.
    pub fn from_content<S: decode::Source>(
        content: &mut decode::Content<S>
    ) -> Result<Self, DecodeError<S::Error>> {
        let os = OctetString::from_content(content)?;
        Self::new(os).map_err(|_| content.content_err("invalid character"))
    }

    /// Returns a value encoder for the character string with the natural tag.
    pub fn encode(self) -> impl encode::Values {
        self.encode_as(L::TAG)
    }

    /// Returns a value encoder for the character string with the given tag.
    pub fn encode_as(self, tag: Tag) -> impl encode::Values {
        self.octets.encode_as(tag)
    }

    /// Returns a value encoder for the character string with the natural tag.
    pub fn encode_ref(&self) -> impl encode::Values + '_ {
        self.encode_ref_as(L::TAG)
    }

    /// Returns a value encoder for the character string with the given tag.
    pub fn encode_ref_as(&self, tag: Tag) -> impl encode::Values + '_ {
        self.octets.encode_ref_as(tag)
    }
}

//--- FromStr

impl<L: CharSet> str::FromStr for RestrictedString<L> {
    type Err = CharSetError;

    fn from_str(s: &str) -> Result<Self, CharSetError> {
        Ok(unsafe { Self::new_unchecked(OctetString::new(
            L::from_str(s)?.into_owned().into()
        ))})
    }
}


//--- Deref and AsRef

impl<L: CharSet> ops::Deref for RestrictedString<L> {
    type Target = OctetString;

    fn deref(&self) -> &OctetString {
        self.as_ref()
    }
}

impl<L: CharSet> AsRef<OctetString> for RestrictedString<L> {
    fn as_ref(&self) -> &OctetString {
        &self.octets
    }
}


//--- PartialEq and Eq, PartialOrd and Ord
//
// We only supply PartialEq<Self> because two identical octet sequences in
// different character sets can mean different things.
//
// XXX Once specialization lands we can bring back the generic comparision
//     and implement it over `Self::chars`.

impl<L: CharSet> PartialEq for RestrictedString<L> {
    fn eq(&self, other: &Self) -> bool {
        self.octets.eq(&other.octets)
    }
}

impl<L: CharSet> Eq for RestrictedString<L> { }

impl<L: CharSet> PartialOrd for RestrictedString<L> {
    fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl<L: CharSet> Ord for RestrictedString<L> {
    fn cmp(&self, other: &Self) -> cmp::Ordering {
        self.octets.cmp(&other.octets)
    }
}


//--- Hash

impl<L: CharSet> hash::Hash for RestrictedString<L> {
    fn hash<H: hash::Hasher>(&self, state: &mut H) {
        self.octets.hash(state)
    }
}


//--- IntoIterator

impl<'a, L: CharSet> IntoIterator for &'a RestrictedString<L> {
    type Item = &'a [u8];
    type IntoIter = OctetStringIter<'a>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}


//--- Display

impl<L: CharSet> fmt::Display for RestrictedString<L> {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        self.chars().try_for_each(|ch| fmt::Display::fmt(&ch, fmt))
    }
}


//------------ RestrictedStringChars ------------------------------------------

/// An iterator over the characters in a restricted character string.
///
/// You can obtain a value of this type via a restricted string’s [`chars`]
/// method.
///
/// [`chars`]: struct.RestrictedStringChars.html#method.chars
#[derive(Clone, Debug)]
pub struct RestrictedStringChars<'a, L: CharSet> {
    /// The underlying octet iterator.
    octets: OctetStringOctets<'a>,

    /// Our character set.
    marker: PhantomData<L>,
}

impl<'a, L: CharSet> RestrictedStringChars<'a, L> {
    /// Creates a new character iterator from an octet iterator.
    fn new(octets: OctetStringOctets<'a>) -> Self {
        RestrictedStringChars {
            octets,
            marker: PhantomData
        }
    }
}

impl<'a, L: CharSet> Iterator for RestrictedStringChars<'a, L> {
    type Item = char;

    fn next(&mut self) -> Option<char> {
        L::next_char(&mut self.octets).unwrap()
    }
}


//============ Concrete Restricted String Types ==============================

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

/// The character set for the UTF8String ASN.1 type.
#[derive(Clone, Copy, Debug)]
pub struct Utf8CharSet;

impl CharSet for Utf8CharSet {
    const TAG: Tag = Tag::UTF8_STRING;

    fn next_char<I: Iterator<Item=u8>>(
        iter: &mut I
    ) -> Result<Option<char>, CharSetError> {
        let first = match iter.next() {
            Some(ch) => ch,
            None => return Ok(None)
        };
        if first < 0x80 {
            return Ok(Some(char::from(first)))
        }
        let second = match iter.next() {
            Some(ch) => ch,
            None => return Err(CharSetError),
        };
        if first < 0xC0 || second < 0x80 {
            return Err(CharSetError)
        }
        if first < 0xE0 {
            return Ok(Some(unsafe {
                char::from_u32_unchecked(
                    (u32::from(first & 0x1F)) << 6 |
                    u32::from(second & 0x3F)
                )
            }))
        }
        let third = match iter.next() {
            Some(ch) => ch,
            None => return Err(CharSetError)
        };
        if third < 0x80 {
            return Err(CharSetError)
        }
        if first < 0xF0 {
            return Ok(Some(unsafe {
                char::from_u32_unchecked(
                    (u32::from(first & 0x0F)) << 12 |
                    (u32::from(second & 0x3F)) << 6 |
                    u32::from(third & 0x3F)
                )
            }))
        }
        let fourth = match iter.next() {
            Some(ch) => ch,
            None => return Err(CharSetError)
        };
        if first > 0xF7 || fourth < 0x80 {
            return Err(CharSetError)
        }
        Ok(Some(unsafe {
            char::from_u32_unchecked(
                (u32::from(first & 0x07)) << 18 |
                (u32::from(second & 0x3F)) << 12 |
                (u32::from(third & 0x3F)) << 6 |
                u32::from(fourth & 0x3F)
            )
        }))
    }

    fn from_str(s: &str) -> Result<Cow<[u8]>, CharSetError> {
        Ok(Cow::Borrowed(s.as_bytes()))
    }
}


//------------ NumericString -------------------------------------------------

/// A restricted character string containing only digits and spaces.
///
/// This character string allows only decimal digits `0` to `9` and the
/// space character ` `. It encodes them with their ASCII value.
///
/// See [`RestrictedString`] for more details on restricged character strings
/// in general.
///
/// [`RestrictedString`]: struct.RestrictedString.html
pub type NumericString = RestrictedString<NumericCharSet>;

/// The character set for the NumericString ASN.1 type.
#[derive(Clone, Copy, Debug)]
pub struct NumericCharSet;

impl CharSet for NumericCharSet {
    const TAG: Tag = Tag::NUMERIC_STRING;

    fn next_char<I: Iterator<Item=u8>>(
        iter: &mut I
    ) -> Result<Option<char>, CharSetError> {
        match iter.next() {
            Some(ch) if ch == b' ' || ch.is_ascii_digit() => {
                Ok(Some(char::from(ch)))
            }
            Some(_) => Err(CharSetError),
            None => Ok(None)
        }
    }

    fn from_str(s: &str) -> Result<Cow<[u8]>, CharSetError> {
        Ok(Cow::Borrowed(s.as_bytes()))
    }
}


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
/// See [`RestrictedString`] for more details on restricged character strings
/// in general.
///
/// [`RestrictedString`]: struct.RestrictedString.html
pub type PrintableString = RestrictedString<PrintableCharSet>;

/// The character set for the PrintableString ASN.1 type.
#[derive(Clone, Debug)]
pub struct PrintableCharSet;

impl CharSet for PrintableCharSet {
    const TAG: Tag = Tag::PRINTABLE_STRING;

    fn next_char<I: Iterator<Item=u8>>(
        iter: &mut I
    ) -> Result<Option<char>, CharSetError> {
        match iter.next() {
            Some(x) if x.is_ascii_alphanumeric() || // A-Z a-z 0-9
                       x == b' ' || x == b'\'' || x == b'(' || x == b')' ||
                       x == b'+' || x == b',' || x == b'-' || x == b'.' ||
                       x == b'/' || x == b':' || x == b'=' || x == b'?' => {
                Ok(Some(char::from(x)))
            }
            Some(_) => Err(CharSetError),
            None => Ok(None)
        }
    }

    fn from_str(s: &str) -> Result<Cow<[u8]>, CharSetError> {
        Ok(Cow::Borrowed(s.as_bytes()))
    }
}


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
/// See [`RestrictedString`] for more details on restricged character strings
/// in general.
///
/// [`RestrictedString`]: struct.RestrictedString.html
pub type Ia5String = RestrictedString<Ia5CharSet>;

/// The character set for the IA5String ASN.1 type.
#[derive(Clone, Copy, Debug)]
pub struct Ia5CharSet;

impl CharSet for Ia5CharSet {
    const TAG: Tag = Tag::IA5_STRING;

    fn next_char<I: Iterator<Item=u8>>(
        iter: &mut I
    ) -> Result<Option<char>, CharSetError> {
        match iter.next() {
            Some(ch) if ch.is_ascii() => Ok(Some(char::from(ch))),
            Some(_) => Err(CharSetError),
            None => Ok(None)
        }
    }

    fn from_str(s: &str) -> Result<Cow<[u8]>, CharSetError> {
        Ok(Cow::Borrowed(s.as_bytes()))
    }
}


//------------ CharSetError --------------------------------------------------

/// An illegal value was encountered during character set conversion.
#[derive(Debug)]
pub struct CharSetError;


//------------ Testing -------------------------------------------------------

#[cfg(test)]
mod test {

    use super::*;
    use bytes::Bytes;
    use crate::decode::IntoSource;
    use crate::mode::Mode;
    use crate::encode::Values;

    #[test]
    fn should_encode_decode_printable_string() {
        let os = OctetString::new(Bytes::from_static(b"This is okay"));
        let ps = PrintableString::new(os).unwrap();

        let mut v = Vec::new();
        ps.encode_ref().write_encoded(Mode::Der, &mut v).unwrap();

        let decoded = Mode::Der.decode(
            v.as_slice().into_source(),
            PrintableString::take_from
        ).unwrap();

        assert_eq!(ps, decoded);
    }

    #[test]
    fn should_restrict_printable_string() {
        let os = OctetString::new(Bytes::from_static(b"This is wrong!"));
        assert!(PrintableString::new(os).is_err());
    }
}
