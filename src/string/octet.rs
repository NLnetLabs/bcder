//! Handling of OCTET STRING.

use std::{io, mem};
use std::marker::PhantomData;
use crate::{decode, encode};
use crate::ident::Tag;
use crate::length::Length;
use crate::mode::{Der, Mode};


//------------ OctetString ---------------------------------------------------

/// An octet string value.
///
/// An octet string is a sequence of octets. Basic Encoding Rules, however,
/// allow this sequence to be broken up into chunks that are encoded
/// separatedly to allow for very large octet strings and cases where one
/// doesn’t yet know the length of the string.
///
/// This type represents the content of such an octet string as a thin
/// wrapper around an unsized byte slice and provides means to decode and
/// encode such a string.
///
/// # BER Encoding
///
/// Octet strings are either encoded as a primitive or a constructed value.
/// In the primitive form, the content octets are the string’s octets. In a
/// constructed form, the content is a sequence of encoded octets strings
/// which in turn may be primitive or constructed. In this case, the string’s
/// octets are the concatenation of all the content octets of the primitive
/// forms in the order as encountered.
///
/// In CER, the string must use the primitive form if it is less than 1000
/// octets long and the constructed form otherwise. The constructed form must
/// consists of a sequence of primitive values each exactly with a 1000
/// octets of content except for the last one.
///
/// In DER, only the primitive form is allowed.
#[derive(Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
pub struct OctetString([u8]);

impl OctetString {
    /// Creates an octet string from a byte slice.
    pub fn from_slice(slice: &[u8]) -> &Self {
        unsafe { mem::transmute(slice) }
    }

    /// Creates a boxed octet string from a boxed byte slice.
    pub fn from_box(src: Box<[u8]>) -> Box<Self> {
        unsafe { mem::transmute(src) }
    }

    /// Returns the underlying byte slice.
    pub fn as_slice(&self) -> &[u8] {
        &self.0
    }
}


/// # Decoding and Encoding
impl OctetString {
    /// Decodes the next value as an octet string.
    ///
    /// If there is no next value, if the next value does not have the tag
    /// `Tag::OCTET_STRING`, or if it doesn’t contain a correctly encoded
    /// octet string, an error is returned.
    pub fn decode_next<M: Mode, R: io::Read>(
        cons: &mut decode::Constructed<M, R>
    ) -> Result<Box<Self>, decode::Error> {
        Self::decode_value(cons.next_with(Tag::OCTET_STRING)?)
    }

    /// Decodes the next value as an octet string.
    ///
    /// If there is no next value, if the next value does not have the tag
    /// `Tag::OCTET_STRING`, or if it doesn’t contain a correctly encoded
    /// octet string, an error is returned.
    pub fn decode_next_borrowed<'s>(
        cons: &mut decode::Constructed<Der, &'s [u8]>
    ) -> Result<&'s Self, decode::Error> {
        Self::decode_value_borrowed(
            cons.next_with(Tag::OCTET_STRING)?
        )
    }

    /// Decodes an optional next value as an octet string.
    ///
    /// If there is no next value, or if the next value does not have the
    /// tag `Tag::OCTET_STRING`, returns `Ok(None)`.
    ///
    /// If there is an octet string, but it is not correctly encoded, returns
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

    /// Decodes an optional next value as an octet string.
    ///
    /// If there is no next value, or if the next value does not have the
    /// tag `Tag::OCTET_STRING`, returns `Ok(None)`.
    ///
    /// If there is an octet string, but it is not correctly encoded, returns
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

    /// Decodes octet string content into a boxed slice.
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

    /// Decodes octet string content in BER mode.
    fn decode_value_ber<M: Mode, R: io::Read>(
        cont: decode::Value<M, R>
    ) -> Result<Box<Self>, decode::Error> {
        let mut target = Vec::new();
        match cont {
            decode::Value::Constructed(cons) => {
                cons.decode_nested(
                    |tag, pos, _| {
                        if tag != Tag::OCTET_STRING {
                            Err(decode::Error::content(
                                "expected OCTET STRING", pos
                            ))
                        }
                        else {
                            Ok(())
                        }
                    },
                    |mut prim| {
                        if prim.tag() != Tag::OCTET_STRING {
                            return Err(decode::Error::content(
                                "expected OCTET STRING", prim.pos()
                            ))
                        }
                        prim.read_all_to_vec(&mut target)
                    }
                )?;
            }
            decode::Value::Primitive(mut prim) => {
                prim.read_all_to_vec(&mut target)?
            }
        }
        Ok(Self::from_box(target.into_boxed_slice()))
    }

    fn decode_value_cer<M: Mode, R: io::Read>(
        content: decode::Value<M, R>
    ) -> Result<Box<Self>, decode::Error> {
        let mut cons = content.into_constructed()?;
        let mut res = Vec::new();
        let mut start = cons.pos();
        while let Some(mut prim) = cons.next_opt_primitive_with(
            Tag::OCTET_STRING
        )? {
            // The collected data must be a multiple of 1000.
            if res.len() % 1000 != 0 {
                return Err(decode::Error::content(
                    "short intermediary in CER octet string", start
                ))
            }
            start = prim.start();
            let len = prim.remaining().try_to_usize().map_err(|_| {
                decode::Error::content(
                    "long intermediary in CER octet string", start
                )
            })?;
            if len > 1000 {
                return Err(decode::Error::content(
                    "long intermediary in CER octet string", start
                ))
            }
            let pos = res.len();
            let Some(new_len) = pos.checked_add(len) else {
                return Err(decode::Error::content(
                    "long octets string", start
                ))
            };
            res.resize(new_len, 0);

            // Safety: pos was a valid index and we grew res.
            #[allow(clippy::indexing_slicing)]
            prim.read_exact(&mut res[pos..])?;
        }
        Ok(Self::from_box(res.into_boxed_slice()))
    }

    fn decode_value_der<M: Mode, R: io::Read>(
        content: decode::Value<M, R>
    ) -> Result<Box<Self>, decode::Error> {
        content.into_primitive()?.read_all_into_box().map(Self::from_box)
    }

    /// Decodes octet string content into a boxed slice.
    pub fn decode_value_borrowed<'s>(
        value: decode::Value<Der, &'s [u8]>
    ) -> Result<&'s Self, decode::Error> {
        value.into_primitive()?.read_all_borrowed().map(Self::from_slice)
    }

    /// Returns a value encoder for the octet string using the natural tag.
    ///
    pub fn encode<'a, M: Mode + 'a>(&'a self) -> impl encode::Values<M> + 'a {
        self.encode_as(Tag::OCTET_STRING)
    }

    /// Returns a value encoder for the octet string using the given tag.
    pub fn encode_as<'a, M: Mode + 'a>(
        &'a self, tag: Tag,
    ) -> impl encode::Values<M> + 'a {
        OctetStringEncoder::new(tag, self.as_slice())
    }
}

/// # Decoding (Legacy version)
///
/// The following contains the decoding functions with the names used in
/// previous versions of the crate. They are provied here for easier
/// transition and should be considered as deprecated.
impl OctetString {
    /// Takes a single octet string value from constructed value content.
    ///
    /// If there is no next value, if the next value does not have the tag
    /// `Tag::OCTET_STRING`, or if it doesn’t contain a correctly encoded
    /// octet string, a malformed error is returned.
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

    /// Takes an optional octet string value from constructed value content.
    ///
    /// If there is no next value, or if the next value does not have the
    /// tag `Tag::OCTET_STRING`, then `Ok(None)` is returned.
    ///
    /// If there is an octet string, but it is not correctly encoded, a
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

impl<'a> From<&'a [u8]> for &'a OctetString {
    fn from(src: &'a [u8]) -> Self {
        OctetString::from_slice(src)
    }
}

impl From<Box<[u8]>> for Box<OctetString> {
    fn from(src: Box<[u8]>) -> Self {
        OctetString::from_box(src)
    }
}

impl<'a> From<&'a OctetString> for Box<OctetString> {
    fn from(src: &'a OctetString) -> Self {
        OctetString::from_box(Box::from(&src.0))
    }
}


//--- AsRef

impl AsRef<[u8]> for OctetString {
    fn as_ref(&self) -> &[u8] {
        self.as_slice()
    }
}


//------------ OctetStringEncoder --------------------------------------------

pub(super) struct OctetStringEncoder<'a, M> {
    tag: Tag,
    slice: &'a [u8],
    marker: PhantomData<M>,
}

impl<'a, M> OctetStringEncoder<'a, M> {
    pub(super) fn new(tag: Tag, slice: &'a [u8]) -> Self {
        Self { tag, slice, marker: PhantomData }
    }

    fn encoded_len_cer(&self) -> Length {
        let full_count = self.slice.len() / 1000;
        let full_len = encode::total_len(
            Tag::OCTET_STRING, Length::from_usize(1000)
        );
        let partial_size = self.slice.len() % 1000;
        let partial_len = if partial_size != 0 {
            encode::total_len(Tag::OCTET_STRING,
                Length::from_usize(partial_size)
            )
        }
        else {
            Length::ZERO
        };

        encode::total_indefinite_len(
            self.tag, full_len * full_count + partial_len
        )
    }

    fn write_encoded_cer<T: encode::Target>(
        &self, target: &mut T
    ) -> Result<(), T::Error> {
        let mut slice = self.slice;
        encode::write_indefinite_header(target, self.tag)?;
        while let Some((head, tail)) = slice.split_at_checked(1000) {
            encode::write_header(
                target, Tag::OCTET_STRING, false, head.len().into()
            )?;
            target.write_all(head)?;
            slice = tail;
        }
        if !slice.is_empty() {
            encode::write_header(
                target, Tag::OCTET_STRING, false, slice.len().into()
            )?;
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


impl<M: Mode> encode::Values<M> for OctetStringEncoder<'_, M> {
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
    

