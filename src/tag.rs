//! The identifer octets of a BER encoded value.
//!
//! This is a private module. Its public items are re-exported by the parent.

use std::{fmt, io};
use crate::decode;


//------------ Tag -----------------------------------------------------------

/// The tag of a BER encoded value.
///
/// Each BER encoded value starts with a sequence of one or more octets called
/// the _identifier octets._ They encode both the tag of the value as well as
/// whether the value uses primitive or constructed encoding. The `Tag` type
/// represents the tag only. The distinction between primitive and constructed
/// encoding is captured by the decoder types [`Primitive`] and
/// [`Constructed`] instead.
///
/// The tag in turn consists of two parts: the class and the number – the
/// `Tag` type includes both of them.
///
/// At the moment, you can only compare two tags. All necessary values are
/// defined as associated constants; there is no other way to create new tag
/// values.
///
/// # Limitations
///
/// At this time, we can only decode single-octet identifier octets. That is,
/// we only support tag numbers between 0 and 30.
///
/// [`Primitive`]: decode/struct.Primitive.html
/// [`Constructed`]: decode/struct.Constructed.html
//
//  For the moment, the tag is stored as a single `u8` with the constructed
//  bit always cleared.
#[derive(Clone, Copy, Eq, PartialEq)]
pub struct Tag(u8);

/// # Constants for Often Used Tag Values
///
impl Tag {
    /// The mask for checking the class.
    const CLASS_MASK: u8 = 0xc0;

    /// The tag value representing for the ‘universal’ class.
    const UNIVERSAL: u8 = 0x00;

    /// The tag value representing the ‘application’ class.
    const APPLICATION: u8 = 0x40;

    /// The tag value representing the ‘context-specific’ class.
    const CONTEXT_SPECIFIC: u8 = 0x80;

    /// The tag value representing the `private` class.
    const PRIVATE: u8 = 0xc0;

    /// The tag marking the end-of-value in an indefinite length value.
    ///
    /// This is UNIVERSAL 0.
    pub const END_OF_VALUE: Self = Tag(0);

    //--- Universal Tags
    //
    // See clause 8.4 of X.690.

    /// The tag for the BOOLEAN type, UNIVERSAL 1.
    pub const BOOLEAN: Self = Tag(1);

    /// The tag for the INTEGER type, UNIVERSAL 2.
    pub const INTEGER: Self = Tag(2);

    /// The tag for the BIT STRING type, UNIVERSAL 3.
    pub const BIT_STRING: Self = Tag(3);

    /// The tag for the OCTET STRING type, UNIVERSAL 4.
    pub const OCTET_STRING: Self = Tag(4);

    /// The tag for the NULL type, UNIVERSAL 5.
    pub const NULL: Self = Tag(5);

    /// The tag for the OBJECT IDENTIFIER type, UNIVERSAL 6.
    pub const OID: Self = Tag(6);

    /// The tag for the ObjectDescriptor type, UNIVERSAL 7.
    pub const OBJECT_DESCRIPTOR: Self = Tag(7);

    /// The tag for the EXTERNAL and Instance-of types, UNIVERSAL 8.
    pub const EXTERNAL: Self = Tag(8);

    /// The tag for the REAL type, UNIVERSAL 9.
    pub const REAL: Self = Tag(9);

    /// The tag for the ENUMERATED type, UNIVERAL 10.
    pub const ENUMERATED: Self = Tag(10);

    /// The tag for the EMBEDDED PDV type, UNIVERAL 11.
    pub const EMBEDDED_PDV: Self = Tag(11);

    /// The tag for the UTF8String type, UNIVERSAL 12
    pub const UTF8_STRING: Self = Tag(12);

    /// The tag for the RELATIVE-OID type, UNIVERAL 13.
    pub const RELATIVE_OID: Self = Tag(13);

    /// The tag for the SEQUENCE and SEQUENCE OF types, UNIVERSAL 16.
    pub const SEQUENCE: Self = Tag(16);

    /// The tag for the SET and SET OF types, UNIVERSAL 17.
    pub const SET: Self = Tag(17);

    /// The tag for the NumericString type, UNIVERSAL 18.
    pub const NUMERIC_STRING: Self = Tag(18);

    /// The tag for the PrintableString type, UNIVERSAL 19.
    pub const PRINTABLE_STRING: Self = Tag(19);

    /// The tag for the TeletexString type, UNIVERSAL 20.
    pub const TELETEX_STRING: Self = Tag(20);

    /// The tag for the VideotexString type, UNIVERSAL 21.
    pub const VIDEOTEX_STRING: Self = Tag(21);

    /// The tag for the IA5String type, UNIVERSAL 22.
    pub const IA5_STRING: Self = Tag(22);

    /// The tag for the UTCTime type, UNIVERSAL 23.
    pub const UTC_TIME: Self = Tag(23);

    /// The tag for the GeneralizedType type, UNIVERAL 24.
    pub const GENERALIZED_TIME: Self = Tag(24);

    /// The tag for the GraphicString type, UNIVERSAL 25.
    pub const GRAPHIC_STRING: Self = Tag(25);

    /// The tag for the VisibleString type, UNIVERSAL 26.
    pub const VISIBLE_STRING: Self = Tag(26);

    /// The tag for the GeneralString type, UNIVERSAL 27.
    pub const GENERAL_STRING: Self = Tag(27);

    /// The tag for the UniversalString type, UNIVERSAL 28.
    pub const UNIVERSAL_STRING: Self = Tag(28);

    /// The tag for the BMPString type, UNIVERSAL 29.
    pub const BMP_STRING: Self = Tag(29);

    /// The tag context specific tag [0].
    pub const CTX_0: Self = Tag(Tag::CONTEXT_SPECIFIC);

    /// The tag context specific tag [1].
    pub const CTX_1: Self = Tag(Tag::CONTEXT_SPECIFIC | 1);

    /// The tag context specific tag [2].
    pub const CTX_2: Self = Tag(Tag::CONTEXT_SPECIFIC | 2);

    /// The tag context specific tag [3].
    pub const CTX_3: Self = Tag(Tag::CONTEXT_SPECIFIC | 3);

    /// The tag context specific tag [4].
    pub const CTX_4: Self = Tag(Tag::CONTEXT_SPECIFIC | 4);

    /// The tag context specific tag [5].
    pub const CTX_5: Self = Tag(Tag::CONTEXT_SPECIFIC | 5);

    /// The tag context specific tag [6].
    pub const CTX_6: Self = Tag(Tag::CONTEXT_SPECIFIC | 6);
}

impl Tag {
    /// Creates a new tag in the universal class with the given tag number.
    ///
    /// # Panics
    ///
    /// Currently, this function panics if the tag number is greater than
    /// 30.
    pub fn universal(number: u8) -> Self {
        assert!(number < 31);
        Tag(number)
    }

    /// Creates a new tag in the application class with the given tag number.
    ///
    /// # Panics
    ///
    /// Currently, this function panics if the tag number is greater than
    /// 30.
    pub fn application(number: u8) -> Self {
        assert!(number < 31);
        Tag(Tag::APPLICATION | number)
    }

    /// Creates a new tag in the context specific class.
    ///
    /// # Panics
    ///
    /// Currently, this function panics if the provided tag number is greater
    /// than 30.
    pub fn context_specific(number: u8) -> Self {
        assert!(number < 31);
        Tag(Tag::CONTEXT_SPECIFIC| number)
    }

    /// Creates a new tag in the private class with the given tag number.
    ///
    /// # Panics
    ///
    /// Currently, this function panics if the provided tag number is greater
    /// than 30.
    pub fn private(number: u8) -> Self {
        assert!(number < 31);
        Tag(Tag::PRIVATE | number)
    }

    /// Returns whether the tag is of the universal class.
    pub fn is_universal(self) -> bool {
        self.0 & Self::CLASS_MASK == Self::UNIVERSAL
    }

    /// Returns whether the tag is of the application class.
    pub fn is_application(self) -> bool {
        self.0 & Self::CLASS_MASK == Self::APPLICATION
    }

    /// Returns whether the tag is of the context specific class.
    pub fn is_context_specific(self) -> bool {
        self.0 & Self::CLASS_MASK == Self::CONTEXT_SPECIFIC
    }

    /// Returns whether the tag is of the private class.
    pub fn is_private(self) -> bool {
        self.0 & Self::CLASS_MASK == Self::PRIVATE
    }

    /// Returns the number of the tag.
    pub fn number(self) -> u8 {
        self.0 & !Self::CLASS_MASK
    }

    /// Takes a tag from the beginning of a source.
    ///
    /// Upon success, returns both the tag and whether the value is
    /// constructed. If there are no more octets available in the source,
    /// an error is returned.
    pub fn take_from<S: decode::Source>(
        source: &mut S,
    ) -> Result<(Self, bool), S::Err> {
        let byte = source.take_u8()?;
        if (byte & 0x1F) == 0x1F {
            // If all five lower bits are 1, the tag is encoded in multiple
            // bytes. We don’t support that.
            xerr!(return Err(decode::Error::Unimplemented.into()))
        }
        Ok((Tag(byte & 0xdf), byte & 0x20 != 0))
    }

    /// Takes a tag from the beginning of a resource if it matches this tag.
    ///
    /// If there is no more data available in the source or if the tag is
    /// something else, returns `Ok(None)`. If the tag matches `self`, returns
    /// whether the value is constructed.
    pub fn take_from_if<S: decode::Source>(
        self,
        source: &mut S,
    ) -> Result<Option<bool>, S::Err> {
        if source.request(1)? == 0 {
            return Ok(None)
        }
        let byte = source.slice()[0];
        let (tag, compressed) = (Tag(byte & 0xdf), byte & 0x20 != 0);
        if tag == self {
            source.advance(1)?;
            Ok(Some(compressed))
        }
        else {
            Ok(None)
        }
    }

    /// Returns the number of octets of the encoded form of the tag.
    #[allow(trivially_copy_pass_by_ref)] // for possible multi-byte tags
    pub fn encoded_len(&self) -> usize {
        1
    }

    /// Encodes the tag into a target.
    ///
    /// If `constructed` is `true`, the encoded tag will signal a value in
    /// constructed encoding and primitive encoding otherwise.
    #[allow(trivially_copy_pass_by_ref)] // for possible multi-byte tags
    pub fn write_encoded<W: io::Write>(
        &self,
        constructed: bool,
        target: &mut W
    ) -> Result<(), io::Error> {
        let mut buf = [self.0];
        if constructed {
            buf[0] |= 0x20
        }
        target.write_all(&buf)
    }
}

impl fmt::Display for Tag {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Tag::BOOLEAN => write!(f, "BOOLEAN"),
            Tag::INTEGER => write!(f, "INTEGER"),
            Tag::BIT_STRING => write!(f, "BIT STRING"),
            Tag::OCTET_STRING => write!(f, "OCTET STRING"),
            Tag::NULL => write!(f, "NULL"),
            Tag::OID => write!(f, "OBJECT IDENTIFIER"),
            Tag::OBJECT_DESCRIPTOR => write!(f, "ObjectDescriptor"),
            Tag::EXTERNAL => write!(f, "EXTERNAL"),
            Tag::REAL => write!(f, "REAL"),
            Tag::ENUMERATED => write!(f, "ENUMERATED"),
            Tag::EMBEDDED_PDV => write!(f, "EMBEDDED PDV"),
            Tag::UTF8_STRING => write!(f, "UTF8String"),
            Tag::RELATIVE_OID => write!(f, "RELATIVE-OID"),
            Tag::SEQUENCE => write!(f, "SEQUENCE"),
            Tag::SET => write!(f, "SET"),
            Tag::NUMERIC_STRING => write!(f, "NumericString"),
            Tag::PRINTABLE_STRING => write!(f, "PrintableString"),
            Tag::TELETEX_STRING => write!(f, "TeletexString"),
            Tag::VIDEOTEX_STRING => write!(f, "VideotexString"),
            Tag::IA5_STRING => write!(f, "IA5String"),
            Tag::UTC_TIME => write!(f, "UTCTime"),
            Tag::GENERALIZED_TIME => write!(f, "GeneralizedTime"),
            Tag::GRAPHIC_STRING => write!(f, "GraphicString"),
            Tag::VISIBLE_STRING => write!(f, "VisibleString"),
            Tag::GENERAL_STRING => write!(f, "GeneralString"),
            Tag::UNIVERSAL_STRING => write!(f, "UniversalString"),
            Tag::BMP_STRING => write!(f, "BMPString"),
            tag => {
                match tag.0 & Tag::CLASS_MASK {
                    Tag::UNIVERSAL => write!(f, "[UNIVERSAL ")?,
                    Tag::APPLICATION => write!(f, "[APPLICATION ")?,
                    Tag::CONTEXT_SPECIFIC => write!(f, "[")?,
                    Tag::PRIVATE => write!(f, "[PRIVATE ")?,
                    _ => unreachable!()
                }
                write!(f, "{}]", tag.0 & !Tag::CLASS_MASK)
            }
        }
    }
}

impl fmt::Debug for Tag {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Tag({})", self)
    }
}

