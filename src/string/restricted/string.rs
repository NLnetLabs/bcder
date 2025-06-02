
use std::{io, mem};
use std::borrow::Cow;
use std::marker::PhantomData;
use crate::{decode, encode};
use crate::ident::Tag;
use crate::mode::{Der, Mode};
use super::super::octet::OctetStringEncoder;
use super::charset::{
    CharSet, CharSetDecoder, CharSetDirectDecoder, CharSetDirectEncoder,
    CharSetEncoder
};


//------------ RestrictedString ----------------------------------------------

#[repr(transparent)]
pub struct RestrictedString<L> {
    /// A marker for the character set.
    marker: PhantomData<L>,

    /// The octets of the string.
    octets: [u8]
}

impl<L> RestrictedString<L> {
    /// Creates a restricted string from a byte slice.
    ///
    /// The byte slice must contain a valid octet sequence for the character
    /// set of the string or an error is returned.
    pub fn from_slice(
        slice: &[u8]
    ) -> Result<&Self, <L::Decoder as CharSetDecoder>::Error>
    where L: CharSet {
        Self::check_slice(slice)?;
        Ok(unsafe { Self::from_slice_unchecked(slice) })
    }

    /// Creates a new restricted string from a byte slice without checking.
    ///
    /// # Safety
    ///
    /// The caller needs to make sure that that byte slice contains is valid
    /// according to the character set of the restricted string, i.e.,
    /// calling `L::check` for the slice must return without error.
    pub unsafe fn from_slice_unchecked(slice: &[u8]) -> &Self {
        unsafe { mem::transmute(slice) }
    }

    /// Creates a restricted string from a boxed byte slice.
    ///
    /// The slice must contain a valid octet sequence for the character
    /// set of the string or an error is returned.
    pub fn from_box(
        slice: Box<[u8]>
    ) -> Result<Box<Self>, <L::Decoder as CharSetDecoder>::Error>
    where L: CharSet {
        Self::check_slice(&slice)?;
        Ok(unsafe { Self::from_box_unchecked(slice) })
    }

    /// Creates a boxed restricted string from a boxed slice without checking.
    ///
    /// # Safety
    ///
    /// The caller needs to make sure that that byte slice contains is valid
    /// according to the character set of the restricted string, i.e.,
    /// calling `L::check` for the slice must return without error.
    pub unsafe fn from_box_unchecked(src: Box<[u8]>) -> Box<Self> {
        unsafe { mem::transmute(src) }
    }

    /// Checks that a slice confirms to the character set.
    fn check_slice(
        slice: &[u8]
    ) -> Result<(), <L::Decoder as CharSetDecoder>::Error>
    where L: CharSet {
        L::Decoder::check_slice(slice)
    }

    /// Returns the underlying byte slice.
    pub fn as_slice(&self) -> &[u8] {
        &self.octets
    }
}

/// # Conversion from and to UTF-8 strings
impl<L: CharSet> RestrictedString<L> {
    pub fn cow_from_str(
        s: &str
    ) -> Result<Cow<Self>, <L::Encoder as CharSetEncoder>::Error> {
        match L::Encoder::encode_str(s)? {
            Cow::Borrowed(slice) => {
                Ok(Cow::Borrowed(unsafe { Self::from_slice_unchecked(slice) }))
            }
            Cow::Owned(vec) => {
                Ok(Cow::Owned(unsafe { Self::from_box_unchecked(vec.into()) }))
            }
        }
    }

    #[allow(clippy::should_implement_trait)]
    pub fn from_str(
        s: &str
    ) -> Result<&Self, <L::Encoder as CharSetEncoder>::Error>
    where L::Encoder: CharSetDirectEncoder {
        L::Encoder::encode_str_direct(s).map(|slice| {
            unsafe { Self::from_slice_unchecked(slice) }
        })
    }

    pub fn to_cow_str(&self) -> Cow<str> {
        L::Decoder::decode_slice_lossy(&self.octets)
    }

    pub fn to_str(&self) -> &str
    where L::Decoder: CharSetDirectDecoder {
        unsafe { L::Decoder::decode_slice_direct(&self.octets) }
    }
}


/// # Decoding and Encoding
impl<L: CharSet> RestrictedString<L> {
    /// Decodes the next value as a restricted string.
    ///
    /// If there is no next value, if the next value does not have the
    /// correct tag for this particular variant of a restricted string,
    /// or if it doesn’t contain a correctly encoded string, an error
    /// is returned.
    pub fn decode_value<M: Mode, R: io::Read>(
        cons: &mut decode::Constructed<M, R>
    ) -> Result<Box<Self>, decode::Error> {
        Self::decode_content(cons.decode_value_if(L::TAG)?)
    }

    /// Decodes the next value as a restricted string.
    ///
    /// If there is no next value, if the next value does not have the
    /// correct tag for this particular variant of a restricted string,
    /// or if it doesn’t contain a correctly encoded string, an error
    /// is returned.
    pub fn decode_value_borrowed<'s>(
        cons: &mut decode::Constructed<Der, &'s [u8]>
    ) -> Result<&'s Self, decode::Error> {
        Self::decode_content_borrowed(cons.decode_value_if(L::TAG)?)
    }

    /// Takes a single restricted string value from constructed value content.
    ///
    /// If there is no next value, if the next value does not have the
    /// correct tag for this particular variant of a restricted string,
    /// or if it doesn’t contain a correctly encoded string, an error
    /// is returned.
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
        Self::decode_value(cons)
    }

    /// Decodes an optional next value as a restricted string.
    ///
    /// If there is no next value, or if the next value does not have the
    /// tag for this variant of restricted string, returns `Ok(None)`.
    ///
    /// If there is restricted string, but it is not correctly encoded,
    /// returns an error.
    pub fn decode_opt_value<M: Mode, R: io::Read>(
        cons: &mut decode::Constructed<M, R>
    ) -> Result<Option<Box<Self>>, decode::Error> {
        let Some(content) = cons.decode_opt_value_if(
            L::TAG
        )? else {
            return Ok(None)
        };
        Self::decode_content(content).map(Some)
    }

    /// Decodes an optional next value as a restricted string.
    ///
    /// If there is no next value, or if the next value does not have the
    /// tag for this variant of restricted string, returns `Ok(None)`.
    ///
    /// If there is restricted string, but it is not correctly encoded,
    /// returns an error.
    pub fn decode_opt_value_borrowed<'s>(
        cons: &mut decode::Constructed<Der, &'s [u8]>
    ) -> Result<Option<&'s Self>, decode::Error> {
        let Some(content) = cons.decode_opt_value_if(
            L::TAG
        )? else {
            return Ok(None)
        };
        Self::decode_content_borrowed(content).map(Some)
    }

    /// Takes an optional restricted string from constructed value content.
    ///
    /// If there is no next value, or if the next value does not have the
    /// tag for this variant of restricted string, returns `Ok(None)`.
    ///
    /// If there is a restricted string, but it is not correctly encoded, an
    /// error is returned.
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
        Self::decode_opt_value(cons)
    }

    /// Decodes restricted string content into a boxed restricted string.
    pub fn decode_content<M: Mode, R: io::Read>(
        value: decode::Value<M, R>
    ) -> Result<Box<Self>, decode::Error> {
        if M::IS_DER {
            Self::decode_content_der(value)
        }
        else if M::IS_CER {
            Self::decode_content_cer(value)
        }
        else {
            Self::decode_content_ber(value)
        }
    }

    /// Decodes content in BER mode.
    fn decode_content_ber<M: Mode, R: io::Read>(
        value: decode::Value<M, R>
    ) -> Result<Box<Self>, decode::Error> {
        let start = value.start();
        match value {
            decode::Value::Constructed(cons) => {
                let mut res = Vec::new();
                let mut decoder = L::Decoder::default();
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
                                "expected OCTET STRING", prim.start()
                            ))
                        }
                        let add_start = res.len();
                        prim.read_all_to_vec(&mut res)?;
                        
                        // Safety: added_start was a valid index before
                        // appending.
                        #[allow(clippy::indexing_slicing)]
                        decoder.check_next(&res[add_start..]).map_err(|err| {
                            decode::Error::content(err, prim.start())
                        })
                    }
                )?;
                decoder.check_final().map_err(|err| {
                    decode::Error::content(err, start)
                })?;
                Ok(unsafe {
                    Self::from_box_unchecked(res.into_boxed_slice())
                })
            }
            decode::Value::Primitive(mut prim) => {
                Self::from_box(prim.read_all_into_box()?).map_err(|err| {
                    decode::Error::content(err, start)
                })
            }
        }
    }

    /// Decodes content in CER mode.
    fn decode_content_cer<M: Mode, R: io::Read>(
        value: decode::Value<M, R>
    ) -> Result<Box<Self>, decode::Error> {
        let mut cons = value.into_constructed()?;
        let mut res = Vec::new();
        let mut decoder = L::Decoder::default();
        let mut start = cons.pos();
        while let Some(mut prim) = cons.decode_opt_primitive_if(
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
                    "long restricted string", start
                ))
            };
            res.resize(new_len, 0);

            // Safety: pos was a valid index and we grew res.
            #[allow(clippy::indexing_slicing)] {
                prim.read_exact(&mut res[pos..])?;
                decoder.check_next(&res[pos..]).map_err(|err| {
                    decode::Error::content(err, prim.start())
                })?;
            }
        }
        decoder.check_final().map_err(|err| {
            decode::Error::content(err, start)
        })?;
        Ok(unsafe {
            Self::from_box_unchecked(res.into_boxed_slice())
        })
    }

    /// Decodes content in DER mode.
    fn decode_content_der<M: Mode, R: io::Read>(
        value: decode::Value<M, R>
    ) -> Result<Box<Self>, decode::Error> {
        let start = value.start();
        Self::from_box(
            value.into_primitive()?.read_all_into_box()?
        ).map_err(|err| decode::Error::content(err, start))
    }

    /// Decodes restricted string content into a boxed restricted string.
    pub fn decode_content_borrowed<'s>(
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
        self.encode_as(L::TAG)
    }

    /// Returns a value encoder for the octet string using the given tag.
    pub fn encode_as<'a, M: Mode + 'a>(
        &'a self, tag: Tag,
    ) -> impl encode::Values<M> + 'a {
        OctetStringEncoder::new(tag, self.as_slice())
    }
}


//--- From

impl<'a, L> From<&'a RestrictedString<L>> for Box<RestrictedString<L>> {
    fn from(src: &'a RestrictedString<L>) -> Self {
        unsafe { RestrictedString::from_box_unchecked(Box::from(&src.octets)) }
    }
}


//--- ToOwned

impl<L> ToOwned for RestrictedString<L> {
    type Owned = Box<RestrictedString<L>>;

    fn to_owned(&self) -> Self::Owned {
        Box::from(self)
    }
}

