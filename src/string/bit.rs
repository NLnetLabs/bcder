//! Handling BITSTRING.

use std::{cmp, error, fmt, io, mem};
use std::convert::Infallible;
use std::marker::PhantomData;
use crate::{decode, encode};
use crate::decode::NestedItem;
use crate::ident::Tag;
use crate::length::Length;
use crate::mode::{Der, Mode};


//------------ BitString -----------------------------------------------------

/// A bit string value.
///
/// Bit strings are a sequence of bits. Unlike
/// [`OctetString`][crate::string::OctetString]s, they do not need to contain
/// a multiple of eight bits.
///
/// This type represents the contents of such a bit string as a thin wrapper
/// around an unsized byte slice. In order to carry all necessary information
/// in a single byte slice, it uses the first byte of that slice to contain
/// the number of bits of the last byte that are unused. In addition, those
/// unused bits in the last octet must be zero. The first byte must always be
/// present. An empty bit string must be represented by the slice `b"\0"`.
///
/// # BER Encoding
///
/// When encoded in BER, bit strings can either be a primitive or
/// constructed value.
///
/// If encoded as a primitive value, the first octet of the content contains
/// the number of unused bits in the last octet and the following octets
/// contain the bits with the first bit in the most significant bit of the
/// octet.
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
/// The last one must be at least one and at most 1000 octets of content.
/// With DER, only the primitive form is allowed.
///
/// In both CER and DER, the unused bits of the last octet must be zero.
#[derive(Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
pub struct BitString([u8]);

impl BitString {
    /// Creates a bit string from a byte slice.
    ///
    /// Returns an error if the byte slice does not contain a correctly
    /// encoded bit string.
    pub fn from_slice(slice: &[u8]) -> Result<&Self, BitStringError> {
        Self::check_slice(slice)?;
        Ok(unsafe { Self::from_slice_unchecked(slice) })
    }

    /// Creates an bit string from a byte slice without checking.
    ///
    /// # Safety
    ///
    /// The caller needs to make sure that the byte slice contains a valid
    /// bit string. Specifically, the first byte must contain the number of
    /// unused bits and thus must be between 0 and 7. The unused bits in the
    /// last byte must be set to zero.
    pub unsafe fn from_slice_unchecked(slice: &[u8]) -> &Self {
        unsafe { mem::transmute(slice) }
    }

    /// Creates a bit string from a boxed byte slice.
    ///
    /// Returns an error if the byte slice does not contain a correctly
    /// encoded bit string.
    pub fn from_box(slice: Box<[u8]>) -> Result<Box<Self>, BitStringError> {
        Self::check_slice(&slice)?;
        Ok(unsafe { Self::from_box_unchecked(slice) })
    }

    /// Creates a boxed bit string from a boxed byte slice without checking.
    ///
    /// # Safety
    ///
    /// The caller needs to make sure that the byte slice contains a valid
    /// bit string. Specifically, the first byte must contain the number of
    /// unused bits and thus must be between 0 and 7. The unused bits in the
    /// last byte must be set to zero.
    pub unsafe fn from_box_unchecked(src: Box<[u8]>) -> Box<Self> {
        unsafe { mem::transmute(src) }
    }

    /// Checks that a slice contains a valid bit string.
    fn check_slice(slice: &[u8]) -> Result<(), BitStringError> {
        let Some(first) = slice.first().copied() else {
            return Err(BitStringError(BSErrorInner::Empty))
        };
        if slice.len() == 1 && first != 0 {
            return Err(BitStringError(
                BSErrorInner::EmptyUnusedBits(first)
            ))
        }
        if first > 7 {
            return Err(BitStringError(
                BSErrorInner::TooManyUnusedBits(first)
            ))
        }
        let mask = !(0xFF << first);

        // Unwrap: We know there is at least one byte.
        #[allow(clippy::unwrap_used)]
        if *slice.last().unwrap() & mask != 0 {
            return Err(BitStringError(BSErrorInner::NonzeroUnusedBits))
        }

        Ok(())
    }

    /// Creates a bit string by encoding data.
    ///
    /// The resulting bit string will have zero unused bits.
    pub fn capture_values<M, V: encode::Values<M>>(
        values: &V
    ) -> Box<BitString> {
        let mut target = BitStringTarget::new();
        encode::infallible(values.write_encoded(&mut target));
        target.finalize(0)
    }

    /// Returns the complete slice of the bit string.
    ///
    /// Note that this slice contains the number of unused bits as its first
    /// byte. If you only want the actual octets of the bit string, you can
    /// use [`octet_slice`][Self::octet_slice] instead.
    pub fn as_slice(&self) -> &[u8] {
        &self.0
    }

    /// Returns the octets of the bit string.
    pub fn octet_slice(&self) -> &[u8] {
        self.0.get(1..).unwrap_or(b"")
    }

    /// Returns the number of unused bits.
    pub fn unused(&self) -> u8 {
        self.0.first().copied().unwrap_or(0)
    }

    /// Returns the number of bits in the bit string.
    pub fn bit_len(&self) -> usize {
        self.0.len().saturating_sub(1) * 8 - usize::from(self.unused())
    }

    /// Returns the value of the given bit.
    ///
    /// Returns `false` for any bit greater than [`bit_len`][Self::bit_len].
    pub fn bit(&self, bit: usize) -> bool {
        let idx = (bit * 8).saturating_add(1);
        let Some(byte) = self.0.get(idx) else {
            return false
        };
        let mask = 1 << (7 - (bit as u8 & 7));
        byte & mask != 0
    }

    /// Returns the number of octets in the bit string.
    ///
    /// This is the length of the slice returns by
    /// [`octet_slice`][Self::octet_slice].
    pub fn octet_len(&self) -> usize {
        self.0.len().saturating_sub(1)
    }
}


/// # Decoding and Encoding
impl BitString {
    /// Decodes the next value as an bit string.
    ///
    /// If there is no next value, if the next value does not have the tag
    /// `Tag::BIT_STRING`, or if it doesn’t contain a correctly encoded
    /// bit string, an error is returned.
    pub fn decode_next<M: Mode, R: io::Read>(
        cons: &mut decode::Constructed<M, R>
    ) -> Result<Box<Self>, decode::Error> {
        Self::decode_value(cons.next_with(Tag::BIT_STRING)?)
    }

    /// Decodes the next value as an bit string.
    ///
    /// If there is no next value, if the next value does not have the tag
    /// `Tag::BIT_STRING`, or if it doesn’t contain a correctly encoded
    /// bit string, an error is returned.
    pub fn decode_next_borrowed<'s>(
        cons: &mut decode::Constructed<Der, &'s [u8]>
    ) -> Result<&'s Self, decode::Error> {
        Self::decode_value_borrowed(cons.next_with(Tag::BIT_STRING)?)
    }

    /// Decodes an optional next value as an bit string.
    ///
    /// If there is no next value, or if the next value does not have the
    /// tag `Tag::BIT_STRING`, returns `Ok(None)`.
    ///
    /// If there is an bit string, but it is not correctly encoded, returns
    /// an error.
    pub fn decode_opt_next<M: Mode, R: io::Read>(
        cons: &mut decode::Constructed<M, R>
    ) -> Result<Option<Box<Self>>, decode::Error> {
        let Some(content) = cons.next_opt_with(
            Tag::OCTET_STRING
        )? else {
            return Ok(None)
        };
        Self::decode_value(content).map(Some)
    }

    /// Decodes an optional next value as an bit string.
    ///
    /// If there is no next value, or if the next value does not have the
    /// tag `Tag::BIT_STRING`, returns `Ok(None)`.
    ///
    /// If there is an bit string, but it is not correctly encoded, returns
    /// an error.
    pub fn decode_opt_next_borrowed<'s>(
        cons: &mut decode::Constructed<Der, &'s [u8]>
    ) -> Result<Option<&'s Self>, decode::Error> {
        let Some(content) = cons.next_opt_with(
            Tag::OCTET_STRING
        )? else {
            return Ok(None)
        };
        Self::decode_value_borrowed(content).map(Some)
    }

    /// Decodes bit string content into a boxed bit string.
    pub fn decode_value<M: Mode, R: io::Read>(
        cons: decode::Value<M, R>
    ) -> Result<Box<Self>, decode::Error> {
        if M::IS_DER {
            Self::decode_value_der(cons)
        }
        else if M::IS_CER {
            Self::decode_value_cer(cons)
        }
        else {
            Self::decode_value_ber(cons)
        }
    }

    /// Decodes bit string content in BER mode.
    fn decode_value_ber<M: Mode, R: io::Read>(
        value: decode::Value<M, R>
    ) -> Result<Box<Self>, decode::Error> {
        match value {
            decode::Value::Constructed(cons) => {
                let mut res = vec![0u8];
                cons.process_nested(|item| {
                    match item {
                        NestedItem::Constructed(cons) => {
                            if cons.tag != Tag::BIT_STRING {
                                Err(decode::Error::content(
                                    "expected BIT STRING", cons.start
                                ))
                            }
                            else {
                                Ok(())
                            }
                        },
                        NestedItem::Primitive(mut prim) => {
                            if prim.tag() != Tag::BIT_STRING {
                                return Err(decode::Error::content(
                                    "expected BIT STRING", prim.start()
                                ))
                            }

                            // The unused bits of the collected data must be
                            // zero -- only the last one is allowed to not be.
                            //
                            // Safety: there is always at least one byte.
                            #[allow(clippy::indexing_slicing)]
                            if res[0] != 0 {
                                return Err(decode::Error::content(
                                    "intermediary with unused bits in BER \
                                     bit string",
                                     prim.start()
                                ))
                            }

                            // Read the first byte into the unused bits field.
                            //
                            // Safety: there is always at least one byte.
                            #[allow(clippy::indexing_slicing)]
                            prim.read_exact(&mut res[..1])?;

                            // Append the rest to the vec.
                            prim.read_all_to_vec(&mut res)?;

                            Self::check_slice(&res).map_err(|err| {
                                decode::Error::content(err, prim.start())
                            })
                        }
                    }
                })?;
                Ok(unsafe {
                    Self::from_box_unchecked(res.into_boxed_slice())
                })
            }
            decode::Value::Primitive(mut prim) => {
                let start = prim.start();
                Self::from_box(prim.read_all_into_box()?).map_err(|err| {
                    decode::Error::content(err, start)
                })
            }
        }
    }

    /// Decodes bit string content in CER mode.
    fn decode_value_cer<M: Mode, R: io::Read>(
        value: decode::Value<M, R>
    ) -> Result<Box<Self>, decode::Error> {
        let mut cons = value.into_constructed()?;
        let mut res = vec![0u8];
        let mut start = cons.pos();
        while let Some(mut prim) = cons.next_opt_primitive_with(
            Tag::BIT_STRING
        )? {
            // The collected data must be a multiple of 999 plus the initial
            // byte.
            if res.len() % 999 != 1 {
                return Err(decode::Error::content(
                    "short intermediary in CER bit string", start
                ))
            }

            // The unused bits of the collected data must be zero -- only the
            // last one is allowed to not be.
            //
            // Safety: there is always at least one byte.
            #[allow(clippy::indexing_slicing)]
            if res[0] != 0 {
                return Err(decode::Error::content(
                    "intermediary with unused bits in CER bit string", start
                ))
            }

            start = prim.start();
            let len = prim.remaining().try_to_usize().map_err(|_| {
                decode::Error::content(
                    "long intermediary in CER bit string", start
                )
            })?;
            if len > 1000 {
                return Err(decode::Error::content(
                    "long intermediary in CER bit string", start
                ))
            }

            // Read the first byte into the unused bits field.
            //
            // Safety: there is always at least one byte.
            #[allow(clippy::indexing_slicing)]
            prim.read_exact(&mut res[..1])?;

            // Append the rest to the vec.
            prim.read_all_to_vec(&mut res)?;

            Self::check_slice(&res).map_err(|err| {
                decode::Error::content(err, start)
            })?;
        }
        Ok(unsafe { Self::from_box_unchecked(res.into_boxed_slice()) })
    }

    /// Decodes bit string content in DER mode.
    fn decode_value_der<M: Mode, R: io::Read>(
        value: decode::Value<M, R>
    ) -> Result<Box<Self>, decode::Error> {
        let start = value.start();
        Self::from_box(
            value.into_primitive()?.read_all_into_box()?
        ).map_err(|err| decode::Error::content(err, start))
    }

    /// Decodes bit string content into a boxed bit string.
    pub fn decode_value_borrowed<'s>(
        value: decode::Value<Der, &'s [u8]>
    ) -> Result<&'s Self, decode::Error> {
        let start = value.start();
        Self::from_slice(
            value.into_primitive()?.read_all_borrowed()?
        ).map_err(|err| decode::Error::content(err, start))
    }

    /// Returns a value encoder for the octet string using the natural tag.
    ///
    pub fn encode<'a, M: Mode + 'a>(&'a self) -> impl encode::Values<M> + 'a {
        self.encode_as(Tag::BIT_STRING)
    }

    /// Returns a value encoder for the octet string using the given tag.
    pub fn encode_as<'a, M: Mode + 'a>(
        &'a self, tag: Tag,
    ) -> impl encode::Values<M> + 'a {
        BitStringEncoder::new(tag, self.as_slice())
    }
}

/// # Decoding (Legacy version)
///
/// The following contains the decoding functions with the names used in
/// previous versions of the crate. They are provied here for easier
/// transition and should be considered as deprecated.
impl BitString {
    /// Takes a single bit string value from constructed value content.
    ///
    /// If there is no next value, if the next value does not have the tag
    /// `Tag::BIT_STRING`, or if it doesn’t contain a correctly encoded
    /// bit string, a malformed error is returned.
    #[cfg_attr(
        feature = "mark-deprecated",
        deprecated(
            since = "0.8.0",
            note = "renamed to `decode_value`"
        )
    )]
    pub fn take_from<M: Mode, R: io::Read>(
        cons: &mut decode::Constructed<M, R>
    ) -> Result<Box<Self>, decode::Error> {
        Self::decode_next(cons)
    }

    /// Takes an optional bit string value from constructed value content.
    ///
    /// If there is no next value, or if the next value does not have the
    /// tag `Tag::BIT_STRING`, then `Ok(None)` is returned.
    ///
    /// If there is an bit string, but it is not correctly encoded, a
    /// malformed error is returned.
    #[cfg_attr(
        feature = "mark-deprecated",
        deprecated(
            since = "0.8.0",
            note = "renamed to `decode_opt_value`"
        )
    )]
    pub fn take_opt_value<M: Mode, R: io::Read>(
        cons: &mut decode::Constructed<M, R>
    ) -> Result<Option<Box<Self>>, decode::Error> {
        Self::decode_opt_next(cons)
    }
}


//--- From

impl<'a> From<&'a BitString> for Box<BitString> {
    fn from(src: &'a BitString) -> Self {
        unsafe { BitString::from_box_unchecked(Box::from(&src.0)) }
    }
}


//--- Clone

impl Clone for Box<BitString> {
    fn clone(&self) -> Self {
        unsafe { BitString::from_box_unchecked(Box::from(self.as_slice())) }
    }
}


//------------ BitStringEncoder ----------------------------------------------

struct BitStringEncoder<'a, M> {
    tag: Tag,
    slice: &'a [u8],
    marker: PhantomData<M>,
}

impl<'a, M> BitStringEncoder<'a, M> {
    fn new(tag: Tag, slice: &'a [u8]) -> Self {
        Self { tag, slice, marker: PhantomData }
    }

    fn encoded_len_cer(&self) -> Length {
        match self.slice.len().checked_sub(1) {
            Some(len) => {
                let full_count = len / 999;
                let full_len = encode::total_len(
                    Tag::BIT_STRING, Length::from_usize(1000)
                );
                let partial_size = self.slice.len() % 999;
                let partial_len = if partial_size != 0 {
                    encode::total_len(Tag::BIT_STRING,
                        Length::from_usize(partial_size) + 1
                    )
                }
                else {
                    Length::ZERO
                };

                encode::total_indefinite_len(
                    self.tag, full_len * full_count + partial_len
                )
            }
            None => {
                encode::total_indefinite_len(
                    self.tag,
                    encode::total_len(Tag::BIT_STRING, 1u8.into())
                )
            }
        }
    }

    fn write_encoded_cer<T: encode::Target>(
        &self, target: &mut T
    ) -> Result<(), T::Error> {
        encode::write_indefinite_header(target, self.tag)?;
        let Some((&unused, mut slice)) = self.slice.split_first() else {
            // Empty slice: Write a single empty bit string - which has only
            // the number of unused bits (i.e., 0) as its content. 
            encode::write_header(target, Tag::BIT_STRING, false, 1u8.into())?;
            target.write_all(&[0])?;

            encode::write_end_of_contents(target)?;
            return Ok(())
        };

        // Break slice into parts of 999 bytes length. All but the last one
        // get a zero prefixed. The last one gets `unused` prefixed,
        while let Some((head, tail)) = slice.split_at_checked(999) {
            encode::write_header(
                target, Tag::BIT_STRING, false,
                Length::from(head.len()) + 1,
            )?;
            if tail.is_empty() {
                target.write_all(&[unused])?;
            }
            else {
                target.write_all(&[0])?;
            }
            target.write_all(head)?;
            slice = tail;
        }
        if !slice.is_empty() {
            encode::write_header(
                target, Tag::BIT_STRING, false,
                Length::from(slice.len()) + 1,
            )?;
            target.write_all(&[unused])?;
            target.write_all(slice)?;
        }
        encode::write_end_of_contents(target)
    }

    fn encoded_len_der(&self) -> Length {
        encode::total_len(self.tag, self.slice.len().into())
    }

    fn write_encoded_der<T: encode::Target>(
        &self, target: &mut T
    ) -> Result<(), T::Error> {
        encode::write_header(
            target, self.tag, false, self.slice.len().into()
        )?;
        target.write_all(self.slice)
    }
}

impl<M: Mode> encode::Values<M> for BitStringEncoder<'_, M> {
    fn encoded_len(&self) -> Length {
        if M::IS_CER {
            self.encoded_len_cer()
        }
        else {
            self.encoded_len_der()
        }
    }

    fn write_encoded<T: encode::Target>(
        &self, target: &mut T
    ) -> Result<(), T::Error> {
        if M::IS_CER {
            self.write_encoded_cer(target)
        }
        else {
            self.write_encoded_der(target)
        }
    }
}


//------------ BitStringTarget -----------------------------------------------

/// A buffer to write the content of a bit string into.
#[derive(Clone, Debug)]
pub struct BitStringTarget {
    data: Vec<u8>,
}

impl BitStringTarget {
    pub fn new() -> Self {
        Self {
            data: vec![0u8],
        }
    }

    /// Appends a slice.
    pub fn append_slice(&mut self, slice: &[u8]) {
        self.data.extend_from_slice(slice)
    }

    /// Finalizes the target into a bit string.
    ///
    /// The number of unused bits in the last byte is given by `unsused`. This
    /// is quietly trimmed back to 8 if it is larger. If no data has been
    /// added to the target, `unused` is ignored.
    pub fn finalize(mut self, unused: u8) -> Box<BitString> {
        let len = self.data.len();
        if len > 1 {
            let unused = cmp::min(unused, 8);
            // Safety: We checked for len > 1.
            unsafe {
                *self.data.get_unchecked_mut(0) = unused;
                *self.data.get_unchecked_mut(len - 1) &= 0xFFu8 << unused;
            }
        }
        unsafe { BitString::from_box_unchecked(self.data.into()) }
    }
}

impl Default for BitStringTarget {
    fn default() -> Self {
        Self::new()
    }
}

impl encode::Target for BitStringTarget {
    type Error = Infallible;

    fn write_all(&mut self, data: &[u8]) -> Result<(), Self::Error> {
        self.append_slice(data);
        Ok(())
    }
}


//------------ BitStringError ------------------------------------------------

#[derive(Clone, Copy, Debug)]
pub struct BitStringError(BSErrorInner);

#[derive(Clone, Copy, Debug)]
enum BSErrorInner {
    Empty,
    EmptyUnusedBits(u8),
    TooManyUnusedBits(u8),
    NonzeroUnusedBits,
}

impl fmt::Display for BitStringError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.0 {
            BSErrorInner::Empty => {
                f.write_str("missing number of unused bits in bitstring")
            }
            BSErrorInner::EmptyUnusedBits(bits) => {
                write!(f, "{bits} unused bits in empty bitstring")
            }
            BSErrorInner::TooManyUnusedBits(bits) => {
                write!(f, "{bits} unused bits in bitstring")
            }
            BSErrorInner::NonzeroUnusedBits => {
                f.write_str("non-zero unused bits in bitstring")
            }
        }
    }
}

impl error::Error for BitStringError { }

