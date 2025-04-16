//! The identifier octets of a BER encoded value.
//!
//! This is a private module. Its public items are re-exported by the parent.

use std::{fmt, io};
use crate::decode::{DecodeError, Fragment, Pos, Source};


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
/// # Limitations
///
/// We can only decode up to six identifier octets. This is enough to encode
/// hold tag numbers represented by a `u32`.
///
/// [`Primitive`]: decode/struct.Primitive.html
/// [`Constructed`]: decode/struct.Constructed.html
//
//  For the moment, the tag is stored with the constructed bit always cleared.
#[derive(Clone, Copy, Eq, PartialEq)]
pub struct Tag(T);

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum T {
    L1([u8; 1]),
    L2([u8; 2]),
    L3([u8; 3]),
    L4([u8; 4]),
    L5([u8; 5]),
    L6([u8; 6]),
}

/// # Constants for Often Used Tag Values
///
impl Tag {
    /// The tag marking the end-of-value in an indefinite length value.
    ///
    /// This is UNIVERSAL 0.
    pub const END_OF_VALUE: Self = Tag::universal(0);

    //--- Universal Tags
    //
    // See clause 8.4 of X.690.

    /// The tag for the BOOLEAN type, UNIVERSAL 1.
    pub const BOOLEAN: Self = Tag::universal(1);

    /// The tag for the INTEGER type, UNIVERSAL 2.
    pub const INTEGER: Self = Tag::universal(2);

    /// The tag for the BIT STRING type, UNIVERSAL 3.
    pub const BIT_STRING: Self = Tag::universal(3);

    /// The tag for the OCTET STRING type, UNIVERSAL 4.
    pub const OCTET_STRING: Self = Tag::universal(4);

    /// The tag for the NULL type, UNIVERSAL 5.
    pub const NULL: Self = Tag::universal(5);

    /// The tag for the OBJECT IDENTIFIER type, UNIVERSAL 6.
    pub const OID: Self = Tag::universal(6);

    /// The tag for the ObjectDescriptor type, UNIVERSAL 7.
    pub const OBJECT_DESCRIPTOR: Self = Tag::universal(7);

    /// The tag for the EXTERNAL and Instance-of types, UNIVERSAL 8.
    pub const EXTERNAL: Self = Tag::universal(8);

    /// The tag for the REAL type, UNIVERSAL 9.
    pub const REAL: Self = Tag::universal(9);

    /// The tag for the ENUMERATED type, UNIVERSAL 10.
    pub const ENUMERATED: Self = Tag::universal(10);

    /// The tag for the EMBEDDED PDV type, UNIVERSAL 11.
    pub const EMBEDDED_PDV: Self = Tag::universal(11);

    /// The tag for the UTF8String type, UNIVERSAL 12
    pub const UTF8_STRING: Self = Tag::universal(12);

    /// The tag for the RELATIVE-OID type, UNIVERSAL 13.
    pub const RELATIVE_OID: Self = Tag::universal(13);

    /// The tag for the TIME type, UNIVERSAL 14.
    pub const TIME: Self = Tag::universal(14);

    /// The tag for the SEQUENCE and SEQUENCE OF types, UNIVERSAL 16.
    pub const SEQUENCE: Self = Tag::universal(16);

    /// The tag for the SET and SET OF types, UNIVERSAL 17.
    pub const SET: Self = Tag::universal(17);

    /// The tag for the NumericString type, UNIVERSAL 18.
    pub const NUMERIC_STRING: Self = Tag::universal(18);

    /// The tag for the PrintableString type, UNIVERSAL 19.
    pub const PRINTABLE_STRING: Self = Tag::universal(19);

    /// The tag for the TeletexString type, UNIVERSAL 20.
    pub const TELETEX_STRING: Self = Tag::universal(20);

    /// The tag for the VideotexString type, UNIVERSAL 21.
    pub const VIDEOTEX_STRING: Self = Tag::universal(21);

    /// The tag for the IA5String type, UNIVERSAL 22.
    pub const IA5_STRING: Self = Tag::universal(22);

    /// The tag for the UTCTime type, UNIVERSAL 23.
    pub const UTC_TIME: Self = Tag::universal(23);

    /// The tag for the GeneralizedType type, UNIVERSAL 24.
    pub const GENERALIZED_TIME: Self = Tag::universal(24);

    /// The tag for the GraphicString type, UNIVERSAL 25.
    pub const GRAPHIC_STRING: Self = Tag::universal(25);

    /// The tag for the VisibleString type, UNIVERSAL 26.
    pub const VISIBLE_STRING: Self = Tag::universal(26);

    /// The tag for the GeneralString type, UNIVERSAL 27.
    pub const GENERAL_STRING: Self = Self::universal(27);

    /// The tag for the UniversalString type, UNIVERSAL 28.
    pub const UNIVERSAL_STRING: Self = Self::universal(28);

    /// The tag for the CHARACTER STRING type, UNIVERSAL 29.
    pub const CHARACTER_STRING: Self = Self::universal(29);

    /// The tag for the BMPString type, UNIVERSAL 30.
    pub const BMP_STRING: Self = Self::universal(30);

    /// The tag for the DATE type, UNIVERSAL 31.
    pub const DATE: Self = Self::universal(31);

    /// The tag for the TIME-OF-DAY type, UNIVERSAL 32.
    pub const TIME_OF_DAY: Self = Self::universal(32);

    /// The tag for the DATE-TIME type, UNIVERSAL 33.
    pub const DATE_TIME: Self = Self::universal(33);

    /// The tag for the DURATION type, UNIVERSAL 34.
    pub const DURATION: Self = Self::universal(34);

    /// The tag for the OID-IRI type, UNIVERSAL 35.
    pub const OID_IRI: Self = Self::universal(35);

    /// The tag for the RELATIVE-OID-IRI type, UNIVERSAL 36.
    pub const RELATIVE_OID_IRI: Self = Self::universal(36);


    //--- Internal constants.

    /// The mask for checking the class.
    const CLASS_MASK: u8 = 0xc0;

    /// The mask for checking whether the value is a primitive
    ///
    /// A value of 0 indicates primitive.
    const CONSTRUCTED_MASK: u8 = 0x20;

    /// The mask for the fourth octet data (bits 24-32).
    ///
    /// (5 bits – 0b0001_1111).
    const SINGLEBYTE_DATA_MASK: u8 = 0x1f;

    /// The mask for octet data.
    ///
    /// (7 bits – 0b0111_1111).
    const MULTIBYTE_DATA_MASK: u8 = 0x7f;

    /// The mask for the last octet with identifier data
    ///
    /// (1 bit – 0b1000_0000, it is cleared in the last octet).
    const LAST_OCTET_MASK: u8 = 0x80;

    /// The tag value representing for the ‘universal’ class.
    const UNIVERSAL: u8 = 0x00;

    /// The tag value representing the ‘application’ class.
    const APPLICATION: u8 = 0x40;

    /// The tag value representing the ‘context-specific’ class.
    const CONTEXT_SPECIFIC: u8 = 0x80;

    /// The tag value representing the `private` class.
    const PRIVATE: u8 = 0xc0;
}

impl Tag {
    /// Encodes a number into the identifier representation.
    ///
    /// There are two forms:
    /// * low tag number (for tag numbers between 0 and 30):
    ///     One octet. Bits 8 and 7 specify the class, bit 6 indicates whether
    ///     the encoding is primitive (0), and bits 5-1 give the tag number.
    /// * high tag number (for tag numbers 31 and greater):
    ///     Two or more octets. First octet is as in low-tag-number form,
    ///     except that bits 5-1 all have value 1. Second and following octets
    ///     give the tag number, base 128, most significant digit first, with
    ///     as few digits as possible, and with the bit 8 of each octet except
    ///     the last set to 1.
    ///
    /// This function assumes that `class_mask` has the lower six bits all
    /// zero.
    const fn new(class_mask: u8, number: u32) -> Self {
        if number <= 0x1e {
            // five bits but not all of them one (so not 0x1f)
            return Tag(T::L1([class_mask | number as u8]))
        }

        // Now the first octet is always the class plus bits 1 to 5 all 1.
        let first = class_mask | 0x1f;

        // The lowest seven bits are the last octet. Shift the number by
        // seven to see what’s left. If that’s zero, we have a two octet
        // tag.
        let n0 = (number & 0x7F) as u8;
        let number = number >> 7;
        if number == 0 {
            return Tag(T::L2([first, n0]))
        }

        // Now rince an repeat.
        let n1 = (number | 0x80) as u8;
        let number = number >> 7;
        if number == 0 {
            return Tag(T::L3([first, n1, n0]))
        }

        let n2 = (number | 0x80) as u8;
        let number = number >> 7;
        if number == 0 {
            return Tag(T::L4([first, n2, n1, n0]))
        }

        let n3 = (number | 0x80) as u8;
        let number = number >> 7;
        if number == 0 {
            return Tag(T::L5([first, n3, n2, n1, n0]))
        }

        let n4 = (number | 0x80) as u8;
        let number = number >> 7;
        debug_assert!(number == 0);
        Tag(T::L6([first, n4, n3, n2, n1, n0]))
    }

    /// Creates a new tag in the universal class with the given tag number.
    pub const fn universal(number: u32) -> Self {
        Tag::new(Tag::UNIVERSAL, number)
    }

    /// Creates a new tag in the application class with the given tag number.
    pub const fn application(number: u32) -> Self {
        Tag::new(Tag::APPLICATION, number)
    }

    /// Creates a new tag in the context specific class.
    pub const fn ctx(number: u32) -> Self {
        Tag::new(Tag::CONTEXT_SPECIFIC, number)
    }

    /// Creates a new tag in the private class with the given tag number.
    pub const fn private(number: u32) -> Self {
        Tag::new(Tag::PRIVATE, number)
    }

    /// Returns a slice of the encoded octets.
    const fn as_slice(&self) -> &[u8] {
        match &self.0 {
            T::L1(arr) => arr.as_slice(),
            T::L2(arr) => arr.as_slice(),
            T::L3(arr) => arr.as_slice(),
            T::L4(arr) => arr.as_slice(),
            T::L5(arr) => arr.as_slice(),
            T::L6(arr) => arr.as_slice(),
        }
    }

    /// Returns the first octet.
    const fn first(self) -> u8 {
        match self.0 {
            T::L1([x]) => x,
            T::L2([x, ..]) => x,
            T::L3([x, ..]) => x,
            T::L4([x, ..]) => x,
            T::L5([x, ..]) => x,
            T::L6([x, ..]) => x,
        }
    }

    /// Returns a tag with the constructed bit set.
    ///
    /// This is private to avoid accidentally handing out tags with this
    /// bit set.
    fn into_constructed(self) -> Self {
        match self.0 {
            T::L1([x]) => Self(T::L1([x | Self::CONSTRUCTED_MASK])),
            T::L2([x, y0]) => Self(T::L2([x | Self::CONSTRUCTED_MASK, y0])),
            T::L3([x, y0, y1]) => {
                Self(T::L3([x | Self::CONSTRUCTED_MASK, y0, y1]))
            }
            T::L4([x, y0, y1, y2]) => {
                Self(T::L4([x | Self::CONSTRUCTED_MASK, y0, y1, y2]))
            }
            T::L5([x, y0, y1, y2, y3]) => {
                Self(T::L5([x | Self::CONSTRUCTED_MASK, y0, y1, y2, y3]))
            }
            T::L6([x, y0, y1, y2, y3, y4]) => {
                Self(T::L6([x | Self::CONSTRUCTED_MASK, y0, y1, y2, y3, y4]))
            }
        }
    }
    

    /// Returs the class bits.
    const fn class(self) -> u8 {
        self.first() & Self::CLASS_MASK
    }

    /// Returns whether the tag is of the universal class.
    pub const fn is_universal(self) -> bool {
        self.class() == Self::UNIVERSAL
    }

    /// Returns whether the tag is of the application class.
    pub const fn is_application(self) -> bool {
        self.class() == Self::APPLICATION
    }

    /// Returns whether the tag is of the context specific class.
    pub const fn is_context_specific(self) -> bool {
        self.class() == Self::CONTEXT_SPECIFIC
    }

    /// Returns whether the tag is of the private class.
    pub const fn is_private(self) -> bool {
        self.class() == Self::PRIVATE
    }

    /// Returns the number of the tag.
    pub const fn number(self) -> u32 {
        match self.0 {
            T::L1([x]) => (x & Self::SINGLEBYTE_DATA_MASK) as u32,
            T::L2([_, x0]) => x0 as u32,
            T::L3([_, x1, x2]) => {
                  ((x1 & Self::MULTIBYTE_DATA_MASK) as u32) << 7
                | (x2 as u32)
            }
            T::L4([_, x1, x2, x3]) => {
                  ((x1 & Self::MULTIBYTE_DATA_MASK) as u32) << 14 
                | ((x2 & Self::MULTIBYTE_DATA_MASK) as u32) << 7
                | (x3 as u32)
            }
            T::L5([_, x1, x2, x3, x4]) => {
                  ((x1 & Self::MULTIBYTE_DATA_MASK) as u32) << 21
                | ((x2 & Self::MULTIBYTE_DATA_MASK) as u32) << 14 
                | ((x3 & Self::MULTIBYTE_DATA_MASK) as u32) << 7
                | (x4 as u32)
            }
            T::L6([_, x1, x2, x3, x4, x5]) => {
                  ((x1 & Self::MULTIBYTE_DATA_MASK) as u32) << 28
                | ((x2 & Self::MULTIBYTE_DATA_MASK) as u32) << 21
                | ((x3 & Self::MULTIBYTE_DATA_MASK) as u32) << 14 
                | ((x4 & Self::MULTIBYTE_DATA_MASK) as u32) << 7
                | (x5 as u32)
            }
        }
    }


    fn peek_opt<S: Source>(
        source: &mut S,
    ) -> Result<Option<(Self, bool)>, PeekError<S::Error>> {
        let pos = source.pos();
        let Some(first) = source.peek_opt_nth(0)? else {
            return Ok(None)
        };

        // Clear constructed bit but remember if for later.
        let constructed = first & Tag::CONSTRUCTED_MASK != 0;
        let first = first & !Tag::CONSTRUCTED_MASK;

        // If we have a single octet tag, we can already return.
        if (first & Tag::SINGLEBYTE_DATA_MASK) < Tag::SINGLEBYTE_DATA_MASK {
            return Ok(Some((Self(T::L1([first])), constructed)))
        }

        // Work your way through the multi-octet tags.
        let x0 = source.peek_nth(1)?;
        if (x0 & Self::LAST_OCTET_MASK) == 0 {
            return Ok(Some((Self(T::L2([first, x0])), constructed)))
        }

        let x1 = source.peek_nth(2)?;
        if (x1 & Self::LAST_OCTET_MASK) == 0 {
            return Ok(Some((Self(T::L3([first, x0, x1])), constructed)))
        }

        let x2 = source.peek_nth(3)?;
        if (x2 & Self::LAST_OCTET_MASK) == 0 {
            return Ok(Some((Self(T::L4([first, x0, x1, x2])), constructed)))
        }

        let x3 = source.peek_nth(4)?;
        if (x3 & Self::LAST_OCTET_MASK) == 0 {
            return Ok(Some((Self(T::L5([first, x0, x1, x2, x3])), constructed)))
        }

        let x4 = source.peek_nth(5)?;
        if (x4 & Self::LAST_OCTET_MASK) == 0 {
            // In order to fit into a u32, the upper four bits of x0 must
            // be zero.
            if x0 & 0xF0 != 0 {
                return Err(PeekError::LongTag(pos))
            }

            return Ok(Some((
                Self(T::L6([first, x0, x1, x2, x3, x4])),
                constructed
            )))
        }

        Err(PeekError::LongTag(pos))
    }

    fn consume<S: Source>(
        self, source: &mut S
    ) -> Result<(), DecodeError<S::Error>> {
        source.request_exact(self.encoded_len())?.consume();
        Ok(())
    }


    /// Takes an optional tag from the beginning of a source.
    ///
    /// Upon success, returns both the tag and whether the value is
    /// constructed.
    pub fn take_opt_from<S: Source>(
        source: &mut S,
    ) -> Result<Option<(Self, bool)>, DecodeError<S::Error>> {
        let res = Self::peek_opt(source)?;
        if let Some((tag, _)) = res {
            tag.consume(source)?;
        }
        Ok(res)
    }

    /// Takes a tag from the beginning of a source.
    ///
    /// Upon success, returns both the tag and whether the value is
    /// constructed. If there are no more octets available in the source,
    /// an error is returned.
    pub fn take_from<S: Source>(
        source: &mut S,
    ) -> Result<(Self, bool), DecodeError<S::Error>> {
        let Some((tag, constructed)) = Self::peek_opt(source)? else {
            return Err(source.content_err("additional values expected"))
        };
        tag.consume(source)?;
        Ok((tag, constructed))
    }

    /// Takes a tag from the beginning of a resource if it matches this tag.
    ///
    /// If there is no more data available in the source or if the tag is
    /// something else, returns `Ok(None)`. If the tag matches `self`, returns
    /// whether the value is constructed.
    pub fn take_from_if<S: Source>(
        self,
        source: &mut S,
    ) -> Result<Option<bool>, DecodeError<S::Error>> {
        match Self::peek_opt(source) {
            Ok(Some((tag, constructed))) if tag == self => {
                Ok(Some(constructed))
            }
            Err(PeekError::Decode(err)) => Err(err),
            _ => Ok(None)
        }
    }

    /// Returns the number of octets of the encoded form of the tag.
    pub fn encoded_len(self) -> usize {
        match self.0 {
            T::L1(_) => 1,
            T::L2(_) => 2,
            T::L3(_) => 3,
            T::L4(_) => 4,
            T::L5(_) => 5,
            T::L6(_) => 6,
        }
    }

    /// Writes the encoded tag to a target.
    ///
    /// If `constructed` is `true`, the encoded tag will signal a value in
    /// constructed encoding and primitive encoding otherwise.
    pub fn write_encoded<W: io::Write>(
        self,
        constructed: bool,
        target: &mut W
    ) -> Result<(), io::Error> {
        let tag = if constructed {
            self.into_constructed()
        }
        else {
            self
        };
        target.write_all(tag.as_slice())
    }

    /// Appends the encoded tag to a vec.
    ///
    /// If `constructed` is `true`, the encoded tag will signal a value in
    /// constructed encoding and primitive encoding otherwise.
    pub fn append_encoded(
        self, constructed: bool, target: &mut  Vec<u8>
    ) {
        let tag = if constructed {
            self.into_constructed()
        }
        else {
            self
        };
        target.extend_from_slice(tag.as_slice())
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
            Tag::TIME => write!(f, "TIME"),
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
            Tag::CHARACTER_STRING => write!(f, "CHARACTER STRING"),
            Tag::BMP_STRING => write!(f, "BMPString"),
            Tag::DATE => write!(f, "DATE"),
            Tag::TIME_OF_DAY => write!(f, "TIME-OF-DAY"),
            Tag::DATE_TIME => write!(f, "DATE-TIME"),
            Tag::DURATION => write!(f, "DURATION"),
            Tag::OID_IRI => write!(f, "OID-IRI"),
            Tag::RELATIVE_OID_IRI => write!(f, "RELATIVE-OID-IRI"),
            tag => {
                match tag.first() & Tag::CLASS_MASK {
                    Tag::UNIVERSAL => write!(f, "[UNIVERSAL ")?,
                    Tag::APPLICATION => write!(f, "[APPLICATION ")?,
                    Tag::CONTEXT_SPECIFIC => write!(f, "[")?,
                    Tag::PRIVATE => write!(f, "[PRIVATE ")?,
                    _ => unreachable!()
                }
                write!(f, "{}]", tag.number())
            }
        }
    }
}

impl fmt::Debug for Tag {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Tag({} - {:?})", self, self.0)
    }
}


//------------ PeekError -----------------------------------------------------

enum PeekError<S> {
    Decode(DecodeError<S>),
    LongTag(Pos),
}

impl<S> From<DecodeError<S>> for PeekError<S> {
    fn from(src: DecodeError<S>) -> Self {
        PeekError::Decode(src)
    }
}

impl<S> From<PeekError<S>> for DecodeError<S> {
    fn from(src: PeekError<S>) -> Self {
        match src {
            PeekError::Decode(err) => err,
            PeekError::LongTag(pos) => {
                DecodeError::content(
                    "tag numbers above 4 bytes not supported",
                    pos
                )
            }
        }
    }
}


//============ Tests =========================================================

#[cfg(test)]
mod test {
    use crate::decode::source::SliceSource;
    use super::*;

    const TYPES: &[u8] = &[
        Tag::UNIVERSAL, Tag::APPLICATION, Tag::CONTEXT_SPECIFIC, Tag::PRIVATE
    ];

    #[test]
    fn test_tags() {
        let mut tags = Vec::new();

        for &typ in TYPES {
            for i in 0..=0x1e {
                tags.push(( 
                    Tag::new(typ, i),
                    Tag(T::L1([typ | i as u8]))
                ));
            }
        }
        for &typ in TYPES {
            for i in 0x1f..=0x7f {
                tags.push((
                    Tag::new(typ, i),
                    Tag(T::L2([
                        typ | 0x1f,
                        i as u8
                    ]))
                ));
            }
        }
        for &typ in TYPES {
            for i in 0x80..=0x3fff {
                tags.push((
                    Tag::new(typ, i),
                    Tag(T::L3([
                        typ | 0x1f,
                        ((i >> 7) & 0x7f) as u8 | 0x80,
                        (i & 0x7f) as u8,
                    ]))
                ));
            }
        }

        for (tag, expected) in tags {
            assert_eq!(tag, expected);

            let mut encoded = Vec::new();
            tag.append_encoded(true, &mut encoded);
            println!("{:?}", tag);
            let mut source = SliceSource::new(encoded.as_ref());

            let (decoded, constructed) = Tag::take_from(&mut source).unwrap();
            assert!(Tag::take_opt_from(&mut source).unwrap().is_none());

            assert!(constructed);
            assert_eq!(tag, decoded);

            let mut encoded = Vec::new();
            tag.append_encoded(false, &mut encoded);
            let mut source = SliceSource::new(encoded.as_ref());

            let (decoded, constructed) = Tag::take_from(&mut source).unwrap();
            assert!(Tag::take_opt_from(&mut source).unwrap().is_none());

            assert!(!constructed);
            assert_eq!(tag, decoded);
        }
    }
}

