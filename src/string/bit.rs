//! BER-encoded bit strings.
//!
//! This is a private module. Its public items are re-exported by the parent.

use std::io;
use bytes::Bytes;
use crate::{decode, encode};
use crate::decode::{DecodeError, Source};
use crate::length::Length;
use crate::mode::Mode;
use crate::tag::Tag;


//------------ BitString -----------------------------------------------------

/// A bit string value.
///
/// Bit strings are a sequence of bits. Unlike
/// [`OctetString`][crate::string::OctetString]s, they do not need to contain
/// a multiple of eight bits.
/// 
/// You can parse a bit string value out of a constructed value using the
/// [`take_from`][Self::take_from] function. The
/// [`from_content`][Self::from_content] function parses the
/// content octets of a bit string value and can be used of the bit string is
/// implcitely tagged. Alternatively, you can create a new simple bit string
/// via the [`new`][Self::new] method.
///
/// There are two types of methods for accessing the data in a bit string.
/// Methods starting with `bit` operate on the individual bits while those
/// prefixed with `octet` access entire octets and ignore the fact that there
/// may be unused bits in the final octet.
///
/// # BER Encoding
///
/// When encoded in BER, bit strings can either be a primitive or
/// constructed value.
///
/// If encoded as a primitive value, the first octet of the
/// content contains the number of unused bits in the last octet and the
/// following octets contain the bits with the first bit in the most
/// significant bit of the octet.
///
/// In the constructed encoding, the bit string is represented as a sequence
/// of bit strings which in turn may either be constructed or primitive
/// encodings. The only limitation in this nesting is that only the last
/// primitively encoded bit string may have a non-zero number of unused bits.
///
/// With BER, the sender can choose either form of encoding. With CER, the
/// primitive encoding should be chosen if its length would be no more than
/// 1000 octets long. Otherwise, the constructed encoding is to be chosen
/// which must contain a sequence of primitively encoded bit strings. Each of
/// these except for the last one must have content of exactly 1000 octets.
/// The last one must be a least one and at most 1000 octets of content.
/// With DER, only the primitive form is allowed.
///
/// # Limitation
///
/// At this time, the `BitString` type does not implement the constructed
/// encoding of a bit string.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct BitString {
    /// The number of unused bits in the last byte.
    unused: u8,

    /// The bytes of the bit string.
    bits: Bytes,
}

impl BitString {
    /// Creates a new bit string.
    pub fn new(unused: u8, bits: Bytes) -> Self {
        Self { unused, bits}
    }

    /// Returns the value of the given bit.
    pub fn bit(&self, bit: usize) -> bool {
        let idx = bit >> 3;
        if self.bits.len() <= idx {
            return false
        }
        let bit = 7 - (bit as u8 & 7);
        if self.bits.len() + 1 == idx && self.unused > bit {
            return false
        }
        self.bits[idx] & (1 << bit) != 0
    }

    /// Returns the number of bits in the bit string.
    pub fn bit_len(&self) -> usize {
        (self.bits.len() << 3) - (self.unused as usize)
    }

    /// Returns the number of unused bits in the last octet.
    pub fn unused(&self) -> u8 {
        self.unused
    }

    /// Returns the number of octets in the bit string.
    pub fn octet_len(&self) -> usize {
        self.bits.len()
    }

    /// Returns an iterator over the octets in the bit string.
    pub fn octets(&self) -> BitStringIter {
        BitStringIter(self.bits.iter())
    }

    /// Returns a slice of the octets in the bit string if available.
    ///
    /// The method will return `None` if the bit string is constructed from
    /// several parts.
    pub fn octet_slice(&self) -> Option<&[u8]> {
        Some(self.bits.as_ref())
    }

    /// Returns a bytes value of the octets of the bit string.
    ///
    /// This will be cheap for primitively encoded bit strings but requires
    /// allocations for complex ones.
    pub fn octet_bytes(&self) -> Bytes {
        self.bits.clone()
    }
}

/// # Decoding and Encoding
///
impl BitString {
    /// Takes a single bit string value from constructed content.
    pub fn take_from<S: decode::Source>(
        constructed: &mut decode::Constructed<S>
    ) -> Result<Self, DecodeError<S::Error>> {
        constructed.take_value_if(Tag::BIT_STRING, Self::from_content)
    }

    /// Skip over a single bit string value inside constructed content.
    pub fn skip_in<S: decode::Source>(
        cons: &mut decode::Constructed<S>
    ) -> Result<(), DecodeError<S::Error>> {
        cons.take_value_if(Tag::BIT_STRING, Self::skip_content)
    }
 
    /// Parses the content octets of a bit string value.
    pub fn from_content<S: decode::Source>(
        content: &mut decode::Content<S>
    ) -> Result<Self, DecodeError<S::Error>> {
        match *content {
            decode::Content::Primitive(ref mut inner) => {
                if inner.mode() == Mode::Cer && inner.remaining() > 1000 {
                    return Err(content.content_err(
                        "long bit string component in CER mode"
                    ))
                }
                Ok(BitString {
                    unused: inner.take_u8()?,
                    bits: inner.take_all()?,
                })
            }
            decode::Content::Constructed(ref inner) => {
                if inner.mode() == Mode::Der {
                    Err(content.content_err(
                       "constructed bit string in DER mode"
                    ))
                }
                else {
                    Err(content.content_err(
                        "constructed bit string not implemented"
                    ))
                }
            }
        }
    }

    /// Skips over the content octets of a bit string value.
    pub fn skip_content<S: decode::Source>(
        content: &mut decode::Content<S>
    ) -> Result<(), DecodeError<S::Error>> {
        match *content {
            decode::Content::Primitive(ref mut inner) => {
                if inner.mode() == Mode::Cer && inner.remaining() > 1000 {
                    return Err(content.content_err(
                        "long bit string component in CER mode"
                    ))
                }
                inner.skip_all()
            }
            decode::Content::Constructed(ref inner) => {
                if inner.mode() == Mode::Der {
                    Err(content.content_err(
                       "constructed bit string in DER mode"
                    ))
                }
                else {
                    Err(content.content_err(
                        "constructed bit string not implemented"
                    ))
                }
            }
        }
    }

    /// Returns a value encoder that encodes a bytes slice as an octet string.
    pub fn encode_slice<T>(value: T, unused: u8) -> BitSliceEncoder<T> {
        Self::encode_slice_as(value, unused, Tag::BIT_STRING)
    }

    /// Returns a value encoder that encodes a bytes slice as an octet string.
    pub fn encode_slice_as<T>(
        value: T,
        unused: u8,
        tag: Tag
    ) -> BitSliceEncoder<T> {
        BitSliceEncoder::new(value, unused, tag)
    }
}


//--- PrimitiveContent

impl encode::PrimitiveContent for BitString {
    const TAG: Tag = Tag::BIT_STRING;

    fn encoded_len(&self, _: Mode) -> usize {
        self.bits.len() + 1
    }

    fn write_encoded<W: io::Write>(
        &self,
        _: Mode,
        target: &mut W
    ) -> Result<(), io::Error> {
        target.write_all(&[self.unused])?;
        target.write_all(self.bits.as_ref())
    }
}


//------------ BitStringIter -------------------------------------------------

/// An iterator over the octets in the bit string.
#[derive(Clone, Debug)]
pub struct BitStringIter<'a>(::std::slice::Iter<'a, u8>);

impl<'a> Iterator for BitStringIter<'a> {
    type Item = u8;

    fn next(&mut self) -> Option<u8> {
        self.0.next().cloned()
    }
}


//------------ BitSliceEncoder -----------------------------------------------

/// A value encoder for a bytes slice as a bit string.
#[derive(Clone, Debug)]
pub struct BitSliceEncoder<T> {
    /// The slice to encode.
    slice: T,

    /// The unused bits in the last byte.
    unused: u8,

    /// The tag to be used for encoded value.
    tag: Tag,
}

impl<T> BitSliceEncoder<T> {
    /// Creates a new bit slice encoder.
    fn new(slice: T, unused: u8, tag: Tag) -> Self {
        BitSliceEncoder { slice, unused, tag }
    }
}


//--- encode::Values

impl<T: AsRef<[u8]>> encode::Values for BitSliceEncoder<T> {
    fn encoded_len(&self, mode: Mode) -> usize {
        if mode == Mode::Cer {
            unimplemented!()
        }
        let len = self.slice.as_ref().len() + 1;
        self.tag.encoded_len() + Length::Definite(len).encoded_len() + len
    }

    fn write_encoded<W: io::Write>(
        &self,
        mode: Mode,
        target: &mut W
    ) -> Result<(), io::Error> {
        if mode == Mode::Cer {
            unimplemented!()
        }
        self.tag.write_encoded(false, target)?;
        Length::Definite(self.slice.as_ref().len() + 1).write_encoded(target)?;
        target.write_all(&[self.unused])?;
        target.write_all(self.slice.as_ref())
    }
}

