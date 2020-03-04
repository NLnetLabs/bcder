//! The identifier octets of a BER encoded value.
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
/// # Limitations
///
/// We can only decode up to four identifier octets. That is, we only support tag
/// numbers between 0 and 1fffff.
///
/// [`Primitive`]: decode/struct.Primitive.html
/// [`Constructed`]: decode/struct.Constructed.html
//
//  For the moment, the tag is stored with the constructed bit always cleared.
#[derive(Clone, Copy, Eq, PartialEq)]
pub struct Tag([u8; 4]);

/// # Constants for Often Used Tag Values
///
impl Tag {
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
    
    /// The largest tag number possible with three octets.
    const MAX_VAL_SPAN_3_OCTETS: u32 = 0x001f_ffff;

    /// The largest tag number possible with two octets.
    const MAX_VAL_SPAN_2_OCTETS: u32 = 0x3fff;

    /// The largest tag number possible with one octet.
    const MAX_VAL_SPAN_1_OCTET: u32 = 0x7f;

    /// The largest tag number possible with the fourth octet.
    const MAX_VAL_FOURTH_OCTET: u32 = 0x1e;

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
    pub const END_OF_VALUE: Self = Tag([0, 0, 0, 0]);

    //--- Universal Tags
    //
    // See clause 8.4 of X.690.

    /// The tag for the BOOLEAN type, UNIVERSAL 1.
    pub const BOOLEAN: Self = Tag([1, 0, 0, 0]);

    /// The tag for the INTEGER type, UNIVERSAL 2.
    pub const INTEGER: Self = Tag([2, 0, 0, 0]);

    /// The tag for the BIT STRING type, UNIVERSAL 3.
    pub const BIT_STRING: Self = Tag([3, 0, 0, 0]);

    /// The tag for the OCTET STRING type, UNIVERSAL 4.
    pub const OCTET_STRING: Self = Tag([4, 0, 0, 0]);

    /// The tag for the NULL type, UNIVERSAL 5.
    pub const NULL: Self = Tag([5, 0, 0, 0]);

    /// The tag for the OBJECT IDENTIFIER type, UNIVERSAL 6.
    pub const OID: Self = Tag([6, 0, 0, 0]);

    /// The tag for the ObjectDescriptor type, UNIVERSAL 7.
    pub const OBJECT_DESCRIPTOR: Self = Tag([7, 0, 0, 0]);

    /// The tag for the EXTERNAL and Instance-of types, UNIVERSAL 8.
    pub const EXTERNAL: Self = Tag([8, 0, 0, 0]);

    /// The tag for the REAL type, UNIVERSAL 9.
    pub const REAL: Self = Tag([9, 0, 0, 0]);

    /// The tag for the ENUMERATED type, UNIVERAL 10.
    pub const ENUMERATED: Self = Tag([10, 0, 0, 0]);

    /// The tag for the EMBEDDED PDV type, UNIVERAL 11.
    pub const EMBEDDED_PDV: Self = Tag([11, 0, 0, 0]);

    /// The tag for the UTF8String type, UNIVERSAL 12
    pub const UTF8_STRING: Self = Tag([12, 0, 0, 0]);

    /// The tag for the RELATIVE-OID type, UNIVERAL 13.
    pub const RELATIVE_OID: Self = Tag([13, 0, 0, 0]);

    /// The tag for the SEQUENCE and SEQUENCE OF types, UNIVERSAL 16.
    pub const SEQUENCE: Self = Tag([16, 0, 0, 0]);

    /// The tag for the SET and SET OF types, UNIVERSAL 17.
    pub const SET: Self = Tag([17, 0, 0, 0]);

    /// The tag for the NumericString type, UNIVERSAL 18.
    pub const NUMERIC_STRING: Self = Tag([18, 0, 0, 0]);

    /// The tag for the PrintableString type, UNIVERSAL 19.
    pub const PRINTABLE_STRING: Self = Tag([19, 0, 0, 0]);

    /// The tag for the TeletexString type, UNIVERSAL 20.
    pub const TELETEX_STRING: Self = Tag([20, 0, 0, 0]);

    /// The tag for the VideotexString type, UNIVERSAL 21.
    pub const VIDEOTEX_STRING: Self = Tag([21, 0, 0, 0]);

    /// The tag for the IA5String type, UNIVERSAL 22.
    pub const IA5_STRING: Self = Tag([22, 0, 0, 0]);

    /// The tag for the UTCTime type, UNIVERSAL 23.
    pub const UTC_TIME: Self = Tag([23, 0, 0, 0]);

    /// The tag for the GeneralizedType type, UNIVERAL 24.
    pub const GENERALIZED_TIME: Self = Tag([24, 0, 0, 0]);

    /// The tag for the GraphicString type, UNIVERSAL 25.
    pub const GRAPHIC_STRING: Self = Tag([25, 0, 0, 0]);

    /// The tag for the VisibleString type, UNIVERSAL 26.
    pub const VISIBLE_STRING: Self = Tag([26, 0, 0, 0]);

    /// The tag for the GeneralString type, UNIVERSAL 27.
    pub const GENERAL_STRING: Self = Tag([27, 0, 0, 0]);

    /// The tag for the UniversalString type, UNIVERSAL 28.
    pub const UNIVERSAL_STRING: Self = Tag([28, 0, 0, 0]);

    /// The tag for the BMPString type, UNIVERSAL 29.
    pub const BMP_STRING: Self = Tag([29, 0, 0, 0]);

    //--- The first few context-specific tags.
    //
    //    These will be removed once we can have `ctx` be a const fn.

    /// The tag context specific tag [0].
    pub const CTX_0: Self = Tag([Tag::CONTEXT_SPECIFIC, 0, 0, 0]);

    /// The tag context specific tag [1].
    pub const CTX_1: Self = Tag([Tag::CONTEXT_SPECIFIC | 1, 0, 0, 0]);

    /// The tag context specific tag [2].
    pub const CTX_2: Self = Tag([Tag::CONTEXT_SPECIFIC | 2, 0, 0, 0]);

    /// The tag context specific tag [3].
    pub const CTX_3: Self = Tag([Tag::CONTEXT_SPECIFIC | 3, 0, 0, 0]);

    /// The tag context specific tag [4].
    pub const CTX_4: Self = Tag([Tag::CONTEXT_SPECIFIC | 4, 0, 0, 0]);

    /// The tag context specific tag [5].
    pub const CTX_5: Self = Tag([Tag::CONTEXT_SPECIFIC | 5, 0, 0, 0]);

    /// The tag context specific tag [6].
    pub const CTX_6: Self = Tag([Tag::CONTEXT_SPECIFIC | 6, 0, 0, 0]);
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
    //
    /// # Panics
    ///
    /// This function panics if the tag number is greater than
    /// `Self::MAX_VAL_SPAN_3_OCTETS`.
    #[inline]
    fn new(class_mask: u8, number: u32) -> Self {
        assert!(number <= Tag::MAX_VAL_SPAN_3_OCTETS);
        if number <= Tag::MAX_VAL_FOURTH_OCTET {
            Tag([class_mask | number as u8, 0, 0, 0])
        } else if number <= Tag::MAX_VAL_SPAN_1_OCTET {
            // Fit the number in the third octets
            let number = number as u8;
            Tag([class_mask | Tag::SINGLEBYTE_DATA_MASK, number, 0, 0])
        } else if number <= Tag::MAX_VAL_SPAN_2_OCTETS {
            // Fit the number in the second and the third octets
            let first_part = {
                Tag::MULTIBYTE_DATA_MASK & ((number >> 7) as u8)
                | Tag::LAST_OCTET_MASK
            };
            let second_part = Tag::MULTIBYTE_DATA_MASK & (number as u8);
            Tag([
                class_mask | Tag::SINGLEBYTE_DATA_MASK, first_part,
                second_part, 0
            ])
        } else {
            // Fit the number in the first, second and the third octets
            let first_part = {
                Tag::MULTIBYTE_DATA_MASK & ((number >> 14) as u8)
                | Tag::LAST_OCTET_MASK
            };
            let second_part = {
                Tag::MULTIBYTE_DATA_MASK & ((number >> 7) as u8)
                | Tag::LAST_OCTET_MASK
            };
            let third_part = Tag::MULTIBYTE_DATA_MASK & (number as u8);
            Tag([
                class_mask | Tag::SINGLEBYTE_DATA_MASK, first_part,
                second_part, third_part
            ])
        }
    }

    /// Creates a new tag in the universal class with the given tag number.
    ///
    /// # Panics
    ///
    /// Currently, this function panics if the tag number is greater than
    /// `MAX_VAL_SPAN_3_OCTETS`.
    pub fn universal(number: u32) -> Self {
        Tag::new(Tag::UNIVERSAL, number)
    }

    /// Creates a new tag in the application class with the given tag number.
    ///
    /// # Panics
    ///
    /// Currently, this function panics if the tag number is greater than
    /// `MAX_VAL_SPAN_3_OCTETS`.
    pub fn application(number: u32) -> Self {
        Tag::new(Tag::APPLICATION, number)
    }

    /// Creates a new tag in the context specific class.
    ///
    /// # Panics
    ///
    /// Currently, this function panics if the provided tag number is greater
    /// than `MAX_VAL_SPAN_3_OCTETS`.
    pub fn ctx(number: u32) -> Self {
        Tag::new(Tag::CONTEXT_SPECIFIC, number)
    }

    /// Creates a new tag in the private class with the given tag number.
    ///
    /// # Panics
    ///
    /// Currently, this function panics if the provided tag number is greater
    /// than `MAX_VAL_SPAN_3_OCTETS`.
    pub fn private(number: u32) -> Self {
        Tag::new(Tag::PRIVATE, number)
    }

    /// Returns whether the tag is of the universal class.
    pub fn is_universal(self) -> bool {
        self.0[0] & Self::CLASS_MASK == Self::UNIVERSAL
    }

    /// Returns whether the tag is of the application class.
    pub fn is_application(self) -> bool {
        self.0[0] & Self::CLASS_MASK == Self::APPLICATION
    }

    /// Returns whether the tag is of the context specific class.
    pub fn is_context_specific(self) -> bool {
        self.0[0] & Self::CLASS_MASK == Self::CONTEXT_SPECIFIC
    }

    /// Returns whether the tag is of the private class.
    pub fn is_private(self) -> bool {
        self.0[0] & Self::CLASS_MASK == Self::PRIVATE
    }

    /// Returns the number of the tag.
    pub fn number(self) -> u32 {
        if (Tag::SINGLEBYTE_DATA_MASK & self.0[0]) != Tag::SINGLEBYTE_DATA_MASK {
            // It's a single byte identifier
            u32::from(Tag::SINGLEBYTE_DATA_MASK & self.0[0])
        } else if Tag::LAST_OCTET_MASK & self.0[1] == 0 {
            // It's a multibyte that starts and ends in the third octet
            u32::from(Tag::MULTIBYTE_DATA_MASK & self.0[1])
        } else if Tag::LAST_OCTET_MASK & self.0[2] == 0 {
            // It's a multibyte that starts in the second octet and ends in
            // the third octet
            u32::from(Tag::MULTIBYTE_DATA_MASK & self.0[1]) << 7
            | u32::from(Tag::MULTIBYTE_DATA_MASK & self.0[2])
        } else {
            // It's a multibyte that spans the first three octets
            u32::from(Tag::MULTIBYTE_DATA_MASK & self.0[1]) << 14
            | u32::from(Tag::MULTIBYTE_DATA_MASK & self.0[2]) << 7
            | u32::from(Tag::MULTIBYTE_DATA_MASK & self.0[3])
        }
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
        // clear constructed bit
        let mut data = [byte & !Tag::CONSTRUCTED_MASK, 0, 0, 0];
        let constructed = byte & Tag::CONSTRUCTED_MASK != 0;
        if (data[0] & Tag::SINGLEBYTE_DATA_MASK) == Tag::SINGLEBYTE_DATA_MASK {
            for i in 1..=3 {
                data[i] = source.take_u8()?;
                if data[i] & Tag::LAST_OCTET_MASK == 0 {
                    return Ok((Tag(data), constructed));
                }
            }
        } else {
            return Ok((Tag(data), constructed));
        }
        xerr!(Err(decode::Error::Unimplemented.into()))
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
        // clear constructed bit
        let mut data = [byte & !Tag::CONSTRUCTED_MASK, 0, 0, 0];
        if (data[0] & Tag::SINGLEBYTE_DATA_MASK) == Tag::SINGLEBYTE_DATA_MASK {
            let mut i = 1;
            loop {
                if source.request(i + 1)? == 0 {
                    // Not enough data for a complete tag.
                    xerr!(return Err(decode::Error::Malformed.into()))
                }
                data[i] = source.slice()[i];
                if data[i] & Tag::LAST_OCTET_MASK == 0 {
                    break
                }
                // We don’t support tags larger than 4 bytes.
                if i == 3 {
                    xerr!(return Err(decode::Error::Unimplemented.into()))
                }
                i += 1;
            }
        }
        let (tag, compressed) = (Tag(data), byte & Tag::CONSTRUCTED_MASK != 0);
        if tag == self {
            source.advance(tag.encoded_len())?;
            Ok(Some(compressed))
        }
        else {
            Ok(None)
        }
    }

    /// Returns the number of octets of the encoded form of the tag.
    #[allow(clippy::trivially_copy_pass_by_ref)] // for possible multi-byte tags
    pub fn encoded_len(&self) -> usize {
        if (Tag::SINGLEBYTE_DATA_MASK & self.0[0]) != Tag::SINGLEBYTE_DATA_MASK {
            1
        } else if Tag::LAST_OCTET_MASK & self.0[1] == 0 {
            2
        } else if Tag::LAST_OCTET_MASK & self.0[2] == 0 {
            3
        } else {
            4
        }
    }

    /// Encodes the tag into a target.
    ///
    /// If `constructed` is `true`, the encoded tag will signal a value in
    /// constructed encoding and primitive encoding otherwise.
    #[allow(clippy::trivially_copy_pass_by_ref)] // for possible multi-byte tags
    pub fn write_encoded<W: io::Write>(
        &self,
        constructed: bool,
        target: &mut W
    ) -> Result<(), io::Error> {
        let mut buf = self.0;
        if constructed {
            buf[0] |= Tag::CONSTRUCTED_MASK
        }
        target.write_all(&buf[..self.encoded_len()])
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
                match tag.0[0] & Tag::CLASS_MASK {
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
        write!(f, "Tag({})", self)
    }
}

//============ Tests =========================================================

#[cfg(test)]
mod test {
    use super::*;

    const TYPES: &[u8] = &[Tag::UNIVERSAL, Tag::APPLICATION, Tag::CONTEXT_SPECIFIC, Tag::PRIVATE];

    #[test]
    fn test_single_octet_tags() {
        // Test edge cases.
        let range: Vec<u32> = (0..5).chain(
            Tag::MAX_VAL_FOURTH_OCTET-5..Tag::MAX_VAL_FOURTH_OCTET
        ).collect();
        for &typ in TYPES {
            for i in range.clone() {
                let tag = Tag::new(typ, i);
                let expected = Tag([typ | i as u8, 0, 0, 0]);
                let decoded = Tag::take_from(&mut &tag.0[..]).unwrap();
                assert_eq!(tag.take_from_if(&mut &tag.0[..]), Ok(Some(false)));
                // The value is not constructed.
                assert_eq!(decoded.1, false);
                // The tag is the same
                assert_eq!(decoded.0, expected);
                // We get the same number back.
                assert_eq!(tag.number(), i);
                // The representation is correct.
                assert_eq!(tag, expected);

            }
        }
    }

    #[test]
    fn test_double_octets_tags() {
        // Test edge cases.
        let range: Vec<u32> = (
            Tag::MAX_VAL_FOURTH_OCTET+1..Tag::MAX_VAL_FOURTH_OCTET+5
        ).chain(
            Tag::MAX_VAL_SPAN_1_OCTET-5..Tag::MAX_VAL_SPAN_1_OCTET
        ).collect();
        for &typ in TYPES {
            for i in range.clone() {
                let tag = Tag::new(typ, i);
                let expected = Tag([
                        Tag::SINGLEBYTE_DATA_MASK | typ, i as u8, 0, 0
                ]);
                let decoded = Tag::take_from(&mut &tag.0[..]).unwrap();
                assert_eq!(tag.take_from_if(&mut &tag.0[..]), Ok(Some(false)));
                // The value is not constructed.
                assert_eq!(decoded.1, false);
                // The tag is the same
                assert_eq!(decoded.0, expected);
                assert_eq!(tag.number(), i);
                assert_eq!(tag, expected);
            }
        }
    }

    #[test]
    fn test_three_octets_tags() {
        // Test edge cases.
        let range: Vec<u32> = (
            Tag::MAX_VAL_SPAN_1_OCTET+1..Tag::MAX_VAL_SPAN_1_OCTET + 5
        ).chain(
            Tag::MAX_VAL_SPAN_2_OCTETS-5..Tag::MAX_VAL_SPAN_2_OCTETS
        ).collect();
        for &typ in TYPES {
            for i in range.clone() {
                let tag = Tag::new(typ, i);
                let expected = Tag([
                    Tag::SINGLEBYTE_DATA_MASK | typ,
                    (i >> 7) as u8 | Tag::LAST_OCTET_MASK,
                    i as u8 & !Tag::LAST_OCTET_MASK,
                    0
                ]);
                let decoded = Tag::take_from(&mut &tag.0[..]).unwrap();
                assert_eq!(tag.take_from_if(&mut &tag.0[..]), Ok(Some(false)));
                // The value is not constructed.
                assert_eq!(decoded.1, false);
                // The tag is the same
                assert_eq!(decoded.0, expected);
                assert_eq!(tag.number(), i);
                assert_eq!(tag, expected);
            }
        }
    }

    #[test]
    fn test_four_octets_tags() {
        // Test edge cases.
        let range: Vec<u32> = (
            Tag::MAX_VAL_SPAN_2_OCTETS+1..Tag::MAX_VAL_SPAN_2_OCTETS + 5
        ).chain(
            Tag::MAX_VAL_SPAN_3_OCTETS-5..Tag::MAX_VAL_SPAN_3_OCTETS
        ).collect();
        for &typ in TYPES {
            for i in range.clone() {
                let tag = Tag::new(typ, i);
                let expected = Tag([
                    Tag::SINGLEBYTE_DATA_MASK | typ,
                    (i >> 14) as u8 | Tag::LAST_OCTET_MASK,
                    (i >> 7) as u8 | Tag::LAST_OCTET_MASK,
                    i as u8 & !Tag::LAST_OCTET_MASK
                ]);
                let decoded = Tag::take_from(&mut &tag.0[..]).unwrap();
                assert_eq!(tag.take_from_if(&mut &tag.0[..]), Ok(Some(false)));
                // The value is not constructed.
                assert_eq!(decoded.1, false);
                // The tag is the same
                assert_eq!(decoded.0, expected);
                assert_eq!(tag.number(), i);
                assert_eq!(tag, expected);
            }
        }
    }

    #[test]
    fn test_tags_failures() {
        let large_tag = [
            0b1111_1111, 0b1000_0000, 0b1000_0000, 0b1000_0000, 0b1000_0000
        ];
        assert_eq!(
            Tag::take_from(&mut &large_tag[..]),
            Err(decode::Error::Unimplemented)
        );
        let short_tag = [0b1111_1111, 0b1000_0000];
        assert_eq!(
            Tag::take_from(&mut &short_tag[..]),
            Err(decode::Error::Malformed)
        );
    }
}
