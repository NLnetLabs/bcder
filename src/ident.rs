//! The identifier octets of a BER encoded value.
//!
//! This is a private module. The relevant items are re-exported by the
//! parent.

use std::{fmt, io};
use crate::decode::read_u8;
use crate::encode::Target;
use crate::length::Length;


//------------ Tag -----------------------------------------------------------

/// The tag of a value.
///
/// In ASN.1, tags are used to identify the type of a value. Tags consist of
/// one of four classes, represented by the [`Class`] enum, and a number
/// within this class. The number is an unsigned integer.
///
/// In BER encoding, the tag becomes part of the identifier octets by
/// combining it with a bit indicating whether a value is primitive or
/// constructed.
///
/// # Limitations
///
/// We only support tag numbers that fit into a `u32`. This should be more
/// than enough in practice.
//
//  Internally, we store the tag as the identifier octets of a primitive value
//  with the same tag.
#[derive(Clone, Copy, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
pub struct Tag(Ident);

impl Tag {
    /// Creates a tag from a class and number.
    pub const fn new(class: Class, number: u32) -> Self {
        Self(Ident::new(class, false, number))
    }

    /// Creates a new tag in class “context dependent” with the given number.
    pub const fn ctx(number: u32) -> Self {
        Self::new(Class::Context, number)
    }

    /// Returns the class of the identifier octets.
    pub const fn class(self) -> Class {
        self.0.class()
    }

    /// Returns the number of the tag.
    pub const fn number(self) -> u32 {
        self.0.number()
    }
}

/// # Constants for universal tags.
///
/// See clause 8.4 of ITU Recommendation X.690.
///
impl Tag {
    /// The tag for the BOOLEAN type, UNIVERSAL 1.
    pub const BOOLEAN: Self = Self::new(Class::Universal, 1);

    /// The tag for the INTEGER type, UNIVERSAL 2.
    pub const INTEGER: Self = Self::new(Class::Universal, 2);

    /// The tag for the BIT STRING type, UNIVERSAL 3.
    pub const BIT_STRING: Self = Self::new(Class::Universal, 3);

    /// The tag for the OCTET STRING type, UNIVERSAL 4.
    pub const OCTET_STRING: Self = Self::new(Class::Universal, 4);

    /// The tag for the NULL type, UNIVERSAL 5.
    pub const NULL: Self = Self::new(Class::Universal, 5);

    /// The tag for the OBJECT IDENTIFIER type, UNIVERSAL 6.
    pub const OID: Self = Self::new(Class::Universal, 6);

    /// The tag for the ObjectDescriptor type, UNIVERSAL 7.
    pub const OBJECT_DESCRIPTOR: Self = Self::new(Class::Universal, 7);

    /// The tag for the EXTERNAL and Instance-of types, UNIVERSAL 8.
    pub const EXTERNAL: Self = Self::new(Class::Universal, 8);

    /// The tag for the REAL type, UNIVERSAL 9.
    pub const REAL: Self = Self::new(Class::Universal, 9);

    /// The tag for the ENUMERATED type, UNIVERSAL 10.
    pub const ENUMERATED: Self = Self::new(Class::Universal, 10);

    /// The tag for the EMBEDDED PDV type, UNIVERSAL 11.
    pub const EMBEDDED_PDV: Self = Self::new(Class::Universal, 11);

    /// The tag for the UTF8String type, UNIVERSAL 12
    pub const UTF8_STRING: Self = Self::new(Class::Universal, 12);

    /// The tag for the RELATIVE-OID type, UNIVERSAL 13.
    pub const RELATIVE_OID: Self = Self::new(Class::Universal, 13);

    /// The tag for the TIME type, UNIVERSAL 14.
    pub const TIME: Self = Self::new(Class::Universal, 14);

    /// The tag for the SEQUENCE and SEQUENCE OF types, UNIVERSAL 16.
    pub const SEQUENCE: Self = Self::new(Class::Universal, 16);

    /// The tag for the SET and SET OF types, UNIVERSAL 17.
    pub const SET: Self = Self::new(Class::Universal, 17);

    /// The tag for the NumericString type, UNIVERSAL 18.
    pub const NUMERIC_STRING: Self = Self::new(Class::Universal, 18);

    /// The tag for the PrintableString type, UNIVERSAL 19.
    pub const PRINTABLE_STRING: Self = Self::new(Class::Universal, 19);

    /// The tag for the TeletexString type, UNIVERSAL 20.
    pub const TELETEX_STRING: Self = Self::new(Class::Universal, 20);

    /// The tag for the VideotexString type, UNIVERSAL 21.
    pub const VIDEOTEX_STRING: Self = Self::new(Class::Universal, 21);

    /// The tag for the IA5String type, UNIVERSAL 22.
    pub const IA5_STRING: Self = Self::new(Class::Universal, 22);

    /// The tag for the UTCTime type, UNIVERSAL 23.
    pub const UTC_TIME: Self = Self::new(Class::Universal, 23);

    /// The tag for the GeneralizedType type, UNIVERSAL 24.
    pub const GENERALIZED_TIME: Self = Self::new(Class::Universal, 24);

    /// The tag for the GraphicString type, UNIVERSAL 25.
    pub const GRAPHIC_STRING: Self = Self::new(Class::Universal, 25);

    /// The tag for the VisibleString type, UNIVERSAL 26.
    pub const VISIBLE_STRING: Self = Self::new(Class::Universal, 26);

    /// The tag for the GeneralString type, UNIVERSAL 27.
    pub const GENERAL_STRING: Self = Self::new(Class::Universal, 27);

    /// The tag for the UniversalString type, UNIVERSAL 28.
    pub const UNIVERSAL_STRING: Self = Self::new(Class::Universal, 28);

    /// The tag for the CHARACTER STRING type, UNIVERSAL 29.
    pub const CHARACTER_STRING: Self = Self::new(Class::Universal, 29);

    /// The tag for the BMPString type, UNIVERSAL 30.
    pub const BMP_STRING: Self = Self::new(Class::Universal, 30);

    /// The tag for the DATE type, UNIVERSAL 31.
    pub const DATE: Self = Self::new(Class::Universal, 31);

    /// The tag for the TIME-OF-DAY type, UNIVERSAL 32.
    pub const TIME_OF_DAY: Self = Self::new(Class::Universal, 32);

    /// The tag for the DATE-TIME type, UNIVERSAL 33.
    pub const DATE_TIME: Self = Self::new(Class::Universal, 33);

    /// The tag for the DURATION type, UNIVERSAL 34.
    pub const DURATION: Self = Self::new(Class::Universal, 34);

    /// The tag for the OID-IRI type, UNIVERSAL 35.
    pub const OID_IRI: Self = Self::new(Class::Universal, 35);

    /// The tag for the RELATIVE-OID-IRI type, UNIVERSAL 36.
    pub const RELATIVE_OID_IRI: Self = Self::new(Class::Universal, 36);
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
                match tag.class() {
                    Class::Universal => write!(f, "[UNIVERSAL ")?,
                    Class::Application => write!(f, "[APPLICATION ")?,
                    Class::Context => write!(f, "[")?,
                    Class::Private => write!(f, "[PRIVATE ")?,
                }
                write!(f, "{}]", tag.number())
            }
        }
    }
}

impl fmt::Debug for Tag {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Tag({} - {:?})", self, self.0.as_slice())
    }
}


//------------ Ident ---------------------------------------------------------

#[derive(Clone, Copy, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Ident(I);

#[derive(Clone, Copy, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum I {
    L1([u8; 1]),
    L2([u8; 2]),
    L3([u8; 3]),
    L4([u8; 4]),
    L5([u8; 5]),
    L6([u8; 6]),
}

impl Ident {
    /// The tag marking the end-of-contents in an indefinite length value.
    pub const END_OF_CONTENTS: Self = Self::new(Class::Universal, false, 0);

    /// Encodes a number into the identifier representation.
    const fn new(class: Class, constructed: bool, number: u32) -> Self {
        let first = if constructed {
            class.into_u8() | 0x20
        }
        else {
            class.into_u8()
        };

        if number <= 0x1e {
            // five bits but not all of them one (so not 0x1f)
            return Self(I::L1([first | number as u8]))
        }

        // Now the first octet is always the class plus bits 1 to 5 all 1.
        let first = first | 0x1f;

        // The lowest seven bits are the last octet. Shift the number by
        // seven to see what’s left. If that’s zero, we have a two octet
        // tag.
        let n0 = (number & 0x7F) as u8;
        let number = number >> 7;
        if number == 0 {
            return Self(I::L2([first, n0]))
        }

        // Now rince an repeat.
        let n1 = (number | 0x80) as u8;
        let number = number >> 7;
        if number == 0 {
            return Self(I::L3([first, n1, n0]))
        }

        let n2 = (number | 0x80) as u8;
        let number = number >> 7;
        if number == 0 {
            return Self(I::L4([first, n2, n1, n0]))
        }

        let n3 = (number | 0x80) as u8;
        let number = number >> 7;
        if number == 0 {
            return Self(I::L5([first, n3, n2, n1, n0]))
        }

        let n4 = (number | 0x80) as u8;
        let number = number >> 7;
        debug_assert!(number == 0);
        Self(I::L6([first, n4, n3, n2, n1, n0]))
    }

    /// Creates identifier octets from a tag.
    pub const fn from_tag(tag: Tag, constructed: bool) -> Self {
        if constructed {
            match tag.0.0 {
                I::L1([x]) => Self(I::L1([x | 0x20])),
                I::L2([x, y0]) => Self(I::L2([x | 0x20, y0])),
                I::L3([x, y0, y1]) => {
                    Self(I::L3([x | 0x20, y0, y1]))
                }
                I::L4([x, y0, y1, y2]) => {
                    Self(I::L4([x | 0x20, y0, y1, y2]))
                }
                I::L5([x, y0, y1, y2, y3]) => {
                    Self(I::L5([x | 0x20, y0, y1, y2, y3]))
                }
                I::L6([x, y0, y1, y2, y3, y4]) => {
                    Self(I::L6([x | 0x20, y0, y1, y2, y3, y4]))
                }
            }
        }
        else {
            tag.0
        }
    }

    /// Returns the tag for the identifier octets.
    pub const fn tag(self) -> Tag {
        match self.0 {
            I::L1([x]) => Tag(Self(I::L1([x & 0xDF]))),
            I::L2([x, y0]) => Tag(Self(I::L2([x & 0xDF, y0]))),
            I::L3([x, y0, y1]) => {
                Tag(Self(I::L3([x & 0xDF, y0, y1])))
            }
            I::L4([x, y0, y1, y2]) => {
                Tag(Self(I::L4([x & 0xDF, y0, y1, y2])))
            }
            I::L5([x, y0, y1, y2, y3]) => {
                Tag(Self(I::L5([x & 0xDF, y0, y1, y2, y3])))
            }
            I::L6([x, y0, y1, y2, y3, y4]) => {
                Tag(Self(I::L6([x & 0xDF, y0, y1, y2, y3, y4])))
            }
        }
    }

    /// Returns the class of the identifier octets.
    pub const fn class(self) -> Class {
        Class::from_u8(self.first())
    }

    /// Returns whether the value is to be a constructed value.
    pub const fn is_constructed(self) -> bool {
        self.first() & 0x20 != 0
    }

    /// Returns the number of the tag.
    pub const fn number(self) -> u32 {
        match self.0 {
            I::L1([x]) => (x & 0x1f) as u32,
            I::L2([_, x0]) => x0 as u32,
            I::L3([_, x1, x2]) => {
                  ((x1 & 0x7f) as u32) << 7
                | (x2 as u32)
            }
            I::L4([_, x1, x2, x3]) => {
                  ((x1 & 0x7f) as u32) << 14 
                | ((x2 & 0x7f) as u32) << 7
                | (x3 as u32)
            }
            I::L5([_, x1, x2, x3, x4]) => {
                  ((x1 & 0x7f) as u32) << 21
                | ((x2 & 0x7f) as u32) << 14 
                | ((x3 & 0x7f) as u32) << 7
                | (x4 as u32)
            }
            I::L6([_, x1, x2, x3, x4, x5]) => {
                  ((x1 & 0x7f) as u32) << 28
                | ((x2 & 0x7f) as u32) << 21
                | ((x3 & 0x7f) as u32) << 14 
                | ((x4 & 0x7f) as u32) << 7
                | (x5 as u32)
            }
        }
    }

    /// Returns a slice of the encoded octets.
    const fn as_slice(&self) -> &[u8] {
        match &self.0 {
            I::L1(arr) => arr.as_slice(),
            I::L2(arr) => arr.as_slice(),
            I::L3(arr) => arr.as_slice(),
            I::L4(arr) => arr.as_slice(),
            I::L5(arr) => arr.as_slice(),
            I::L6(arr) => arr.as_slice(),
        }
    }

    /// Returns the first octet.
    const fn first(self) -> u8 {
        match self.0 {
            I::L1([x]) => x,
            I::L2([x, ..]) => x,
            I::L3([x, ..]) => x,
            I::L4([x, ..]) => x,
            I::L5([x, ..]) => x,
            I::L6([x, ..]) => x,
        }
    }

    /// Reads the identifier octets from a reader.
    pub fn read_opt(
        reader: &mut impl io::Read
    ) -> Result<Option<Self>, io::Error> {
        let first = match read_u8(reader) {
            Ok(res) => res,
            Err(err) if err.kind() == io::ErrorKind::UnexpectedEof => {
                return Ok(None)
            }
            Err(err) => return Err(err)
        };

        // If we have a single octet tag, we can already return.
        if (first & 0x1f) < 0x1f {
            return Ok(Some(Self(I::L1([first]))))
        }

        // Work your way through the multi-octet tags.
        let x0 = read_u8(reader)?;
        if (x0 & 0x80) == 0 {
            return Ok(Some(Self(I::L2([first, x0]))))
        }

        let x1 = read_u8(reader)?;
        if (x1 & 0x80) == 0 {
            return Ok(Some(Self(I::L3([first, x0, x1]))))
        }

        let x2 = read_u8(reader)?;
        if (x2 & 0x80) == 0 {
            return Ok(Some(Self(I::L4([first, x0, x1, x2]))))
        }

        let x3 = read_u8(reader)?;
        if (x3 & 0x80) == 0 {
            return Ok(Some(Self(I::L5([first, x0, x1, x2, x3]))))
        }

        let x4 = read_u8(reader)?;
        if (x4 & 0x80) == 0 {
            // In order to fit into a u32, the upper four bits of x0 must
            // be zero.
            if x0 & 0xF0 != 0 {
                return Err(io::Error::new(
                    io::ErrorKind::Unsupported,
                    "tag numbers above 4 bytes not supported"
                ))
            }

            return Ok(Some(Self(I::L6([first, x0, x1, x2, x3, x4]))))
        }

        Err(io::Error::new(
            io::ErrorKind::Unsupported,
            "tag numbers above 4 bytes not supported"
        ))
    }

    pub fn read(
        reader: &mut impl io::Read
    ) -> Result<Self, io::Error> {
        match Self::read_opt(reader)? {
            Some(res) => Ok(res),
            None => {
                Err(io::Error::new(
                    io::ErrorKind::InvalidData, "unexpected end of value"
                ))
            }
        }
    }

    /// Returns the number of octets of the encoded form of the tag.
    pub fn encoded_len(self) -> Length {
        Length::from_u64(
            match self.0 {
                I::L1(_) => 1,
                I::L2(_) => 2,
                I::L3(_) => 3,
                I::L4(_) => 4,
                I::L5(_) => 5,
                I::L6(_) => 6,
            }
        )
    }

    /// Writes the identifier octets to a target.
    pub fn write_encoded<T: Target>(
        self, target: &mut T
    ) -> Result<(), T::Error> {
        target.write_all(self.as_slice())
    }
}

impl fmt::Debug for Ident {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self.as_slice())
    }
}


//------------ Class ---------------------------------------------------------

#[derive(Clone, Copy, Debug)]
pub enum Class {
    Universal,
    Application,
    Context,
    Private,
}

impl Class {
    const fn from_u8(octet: u8) -> Self {
        match octet {
            0x00..=0x3F => Self::Universal,
            0x40..=0x7F => Self::Application,
            0x80..=0xBF => Self::Context,
            0xC0..=0xFF => Self::Private
        }
    }

    const fn into_u8(self) -> u8 {
        match self {
            Self::Universal => 0x00,
            Self::Application => 0x40,
            Self::Context => 0x80,
            Self::Private => 0xC0,
        }
    }
}


