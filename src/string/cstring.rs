//! BER-encoded Restricted Character String types.
//!
//! This is an internal module. It’s public types are re-exported by the
//! parent.

use std::marker::PhantomData;
use ::{decode, encode};
use ::OctetString;
use ::tag::Tag;


//------------ CharSet -------------------------------------------------------

/// Trait for the various Restricted Character String types defined in X.680
pub trait CharSet {
    /// Implementations must specify their own natural tag
    const TAG: Tag;

    /// Implementations must verify the contents
    fn is_allowed<I: Iterator<Item=u8>>(i: &mut I) -> bool;
}


//------------ PrintableString -----------------------------------------------

/// A PrintableString.
///
/// The printable string is an implementation of the restricted character
/// string type defined in X.680 that only allows the following characters:
/// a-z A-Z 0-9 (space) ' ( ) + , _ . / : = ?
pub type PrintableString = CharString<PrintableStringSet>;

#[derive(Clone, Debug)]
pub struct PrintableStringSet;

impl CharSet for PrintableStringSet {
    const TAG: Tag = Tag::PRINTABLE_STRING;

    fn is_allowed<I: Iterator<Item=u8>>(i: &mut I) -> bool {
        i.all(|x| {
            x.is_ascii_alphanumeric() || // A-Z a-z 0-9
            x == b' ' || x == b'\'' || x == b'(' || x == b')' ||
            x == b'+' || x == b',' || x == b'-' || x == b'.' ||
            x == b'/' || x == b':' || x == b'=' || x == b'?'
        })
    }
}


//------------ CharString ----------------------------------------------------

/// A generic Restricted Character String.
///
/// Contains an octet string with the actual content.
///
/// Specific implementations have to ensure that they verify the content
/// according to the appropriate limitations, and use the correct Tag.
#[derive(Clone, Debug)]
pub struct CharString<L: CharSet> {
    octets: OctetString,
    marker: PhantomData<L>
}

impl<L: CharSet> CharString<L> {
    unsafe fn new_unchecked(octets: OctetString) -> Self {
        CharString {
            octets,
            marker: PhantomData
        }
    }

    /// Creates a new restricted character set instance.
    ///
    /// Creates a new restricted character set instance from an octet string,
    /// and verifies that all the bytes in the octet string are allowed by
    /// the specific restricted character set implementation, e.g. printable
    /// string.
    pub fn new(os: OctetString) -> Result<Self, CharSetError> {
        if L::is_allowed(&mut os.octets()) {
            Ok(unsafe { Self::new_unchecked(os) })
        } else {
            Err(CharSetError)
        }
    }

    /// Takes a single character set value from constructed value content.
    ///
    /// If there is no next value, if the next value does not have the natural
    /// tag appropriate for this character set implementation, or if it does
    /// not contain a correctly encoded character string, a malformed error is
    /// returned.
    pub fn take_from<S: decode::Source>(
        cons: &mut decode::Constructed<S>
    ) -> Result<Self, S::Err> {
        cons.take_value_if(L::TAG, Self::take_content_from)
    }

    /// Takes a character set from content.
    pub fn take_content_from<S: decode::Source>(
        content: &mut decode::Content<S>
    ) -> Result<Self, S::Err> {
        let os = OctetString::take_content_from(content)?;
        Self::new(os).map_err(|_| decode::Error::Malformed.into())
    }

    pub fn encode<'a>(&'a self) -> impl encode::Values + 'a {
        self.encode_as(L::TAG)
    }

    pub fn encode_as<'a>(&'a self, tag: Tag) -> impl encode::Values + 'a {
        self.octets.encode_as(tag)
    }
}


//--- PartialEq and Eq

impl<L: CharSet, T: AsRef<OctetString>> PartialEq<T> for CharString<L> {
    fn eq(&self, other: &T) -> bool {
        self.octets.eq(other.as_ref())
    }
}

impl<L: CharSet> Eq for CharString<L> { }


//--- AsRef

impl<L: CharSet> AsRef<OctetString> for CharString<L> {
    fn as_ref(&self) -> &OctetString {
        &self.octets
    }
}


//------------ CharSetError --------------------------------------------------

#[derive(Debug)]
pub struct CharSetError;


//------------ Testing -------------------------------------------------------

#[cfg(test)]
mod test {

    use super::*;
    use bytes::Bytes;
    use mode::Mode;
    use encode::Values;

    #[test]
    fn should_encode_decode_printable_string() {
        let os = OctetString::new(Bytes::from_static(b"This is okay"));
        let ps = PrintableString::new(os).unwrap();

        let mut v = Vec::new();
        ps.encode().write_encoded(Mode::Der, &mut v).unwrap();

        let decoded = Mode::Der.decode(
            v.as_slice(),
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
