//! Parsing BER encoded values.
//!
//! This is an internal module. The relevant items are re-exported by the
//! parent.

use std::{cmp, error, io};
use std::io::{BufRead, Read};
use std::marker::PhantomData;
use crate::ident::{Ident, Tag};
use crate::int::{IntegerArray, UnsignedArray};
use crate::length::{Length, LengthOctets};
use crate::mode::{Ber, Mode};
use super::error::Error;
use super::source::{DefiniteSource, IndefiniteSource, Source};


mod nested;


//------------ Data ----------------------------------------------------------

/// Encoded data.
///
/// This type wraps an IO reader and allows decoding it as a sequence of
/// encoded values.
pub struct Data<M, R> {
    source: Source<R>,
    nested_done: Option<bool>,
    marker: PhantomData<M>,
}


//------------ Content -------------------------------------------------------

/// The contents octets of a BER-encoded value.
///
/// A value is either primitive, containing actual octets of an actual value,
/// or constructed, in which case its content is zero or more BER encoded
/// values. This enum represents both of these types.
///
/// Note that this type represents the content octets only, i.e., it does not
/// contain the tag of the value.
pub enum Content<'a, M, R: 'a> {
    /// The value is a primitive value.
    Primitive(Primitive<'a, M, R>),

    /// The value is a constructed value.
    Constructed(Constructed<'a, M, R>)
}

impl<'a, M, R: 'a> Content<'a, M, R> {
    /// Returns the tag of the value.
    pub fn tag(&self) -> Tag {
        match self {
            Content::Primitive(inner) => inner.tag(),
            Content::Constructed(inner) => inner.tag(),
        }
    }

    /// Returns the source’s position at the start of the value.
    pub fn start(&self) -> Length {
        match self {
            Content::Primitive(inner) => inner.start(),
            Content::Constructed(inner) => inner.start(),
        }
    }

    /// Returns whether this value is a primitive value.
    pub fn is_primitive(&self) -> bool {
        match *self {
            Content::Primitive(_) => true,
            Content::Constructed(_) => false,
        }
    }

    /// Returns whether this value is a constructed value.
    pub fn is_constructed(&self) -> bool {
        match *self {
            Content::Primitive(_) => false,
            Content::Constructed(_) => true,
        }
    }

    /// Converts a reference into one to a primitive value or errors out.
    pub fn as_primitive(
        &mut self
    ) -> Result<&mut Primitive<'a, M, R>, Error> {
        match self {
            Content::Primitive(inner) => Ok(inner),
            Content::Constructed(inner) => {
                Err(inner.content_err_at_start("expected primitive value"))
            }
        }
    }

    /// Converts a reference into on to a constructed value or errors out.
    pub fn as_constructed(
        &mut self
    ) -> Result<&mut Constructed<'a, M, R>, Error> {
        match self {
            Content::Primitive(inner) => {
                Err(inner.content_err_at_start("expected constructed value"))
            }
            Content::Constructed(inner) => Ok(inner),
        }
    }

    /// Converts a reference into into one to a primitive value or errors out.
    pub fn into_primitive(
        self
    ) -> Result<Primitive<'a, M, R>, Error> {
        match self {
            Content::Primitive(inner) => Ok(inner),
            Content::Constructed(inner) => {
                Err(inner.content_err_at_start("expected primitive value"))
            }
        }
    }

    /// Converts a reference into on to a constructed value or errors out.
    pub fn into_constructed(
        self
    ) -> Result<Constructed<'a, M, R>, Error> {
        match self {
            Content::Primitive(inner) => {
                Err(inner.content_err_at_start("expected constructed value"))
            }
            Content::Constructed(inner) => Ok(inner),
        }
    }

    /// Produces a content error at the start of the value.
    pub fn content_err_at_start(
        &self, err: impl Into<Box<dyn error::Error + Send + Sync>>,
    ) -> Error {
        match self {
            Content::Primitive(inner) => inner.content_err_at_start(err),
            Content::Constructed(inner) => inner.content_err_at_start(err),
        }
    }

    /// Produces a content error at the current position.
    pub fn content_err_at_current(
        &self, err: impl Into<Box<dyn error::Error + Send + Sync>>,
    ) -> Error {
        match self {
            Content::Primitive(inner) => inner.content_err_at_current(err),
            Content::Constructed(inner) => inner.content_err_at_current(err),
        }
    }
}

/// # High-level parsing (closure version)
///
/// The following methods can be used when parsing content in a closure. They
/// start with the prefix `to_` for legacy reasons.
#[allow(clippy::wrong_self_convention)]
impl<'a, M, R: io::Read + 'a> Content<'a, M, R> {
    // XXX TODO
}


//------------ Primitive -----------------------------------------------------

/// The contents octets of a primitive value.
///
/// This type provides access to the contents octets. When processing the
/// value, you need to read all contents octets. If you don’t, the outer
/// constructed value will produce a “trailing data” error when trying to
/// progress to the next value. Thus, when decoding the contents, you can
/// stop reading when you think the contents should have ended and leave
/// it to the outer value to produce an error.
///
/// The type is generic over the decoding mode via the `M` type argument.
/// All methodes that decode data will honour the decoding mode and enforce
/// that data is encoded according to the mode.
pub struct Primitive<'a, M, R: 'a> {
    tag: Tag,
    start: Length,
    source: DefiniteSource<'a, R>,
    marker: PhantomData<M>,
}

impl<'a, M, R: 'a> Primitive<'a, M, R> {
    /// Creates a new primitive from the given source.
    fn new(tag: Tag, start: Length, source: DefiniteSource<'a, R>) -> Self {
        Self { tag, start, source, marker: PhantomData }
    }

    /// Switches the decoding mode.
    pub fn switch_mode<N>(self) -> Primitive<'a, N, R> {
        Primitive {
            tag: self.tag,
            start: self.start,
            source: self.source,
            marker: PhantomData,
        }
    }

    /// Returns the tag of the value.
    pub fn tag(&self) -> Tag {
        self.tag
    }

    /// Returns the source’s position at the start of the value.
    pub fn start(&self) -> Length {
        self.start
    }

    /// Returns the number of remaining octets.
    ///
    /// The returned value reflects what is left of the expected length of
    /// content and therefore decreases when data is read.
    pub fn remaining(&self) -> Length {
        self.source.remaining()
    }

    /// Checks that the remaining octets are zero.
    ///
    /// Returns a “trailing data” error if there are remaining octets.
    ///
    /// Calling this method is optional. The check also happens when later
    /// continuing to decode data.
    pub fn check_exhausted(&self) -> Result<(), Error> {
        if !self.remaining().is_zero() {
            Err(self.content_err_at_current("trailing data"))
        }
        else {
            Ok(())
        }
    }

    /// Checks for a specific remaining length.
    ///
    /// Returns a “trailing data” error if there are more octets remaining
    /// and a “unexpected end of value” error if there are less.
    pub fn check_len(
        &self, len: impl Into<Length>
    ) -> Result<(), Error> {
        let len = len.into();
        if self.remaining() > len {
            Err(self.content_err_at_current("trailing data"))
        }
        else if self.remaining() < len {
            Err(self.content_err_at_current("unexpected end of value"))
        }
        else {
            Ok(())
        }
    }

    /// Returns the current position in the underlying source.
    pub fn pos(&self) -> Length {
        self.source.pos()
    }

    /// Produces a content error at the start of the value.
    pub fn content_err_at_start(
        &self, err: impl Into<Box<dyn error::Error + Send + Sync>>,
    ) -> Error {
        Error::content(err, self.start)
    }

    /// Produces a content error at the current position.
    pub fn content_err_at_current(
        &self, err: impl Into<Box<dyn error::Error + Send + Sync>>,
    ) -> Error {
        Error::content(err, self.pos())
    }
}


/// # High-level parsing (legacy version)
///
/// The following methods were used for parsing primitive content in previous
/// versions of _bcder._ They are provided here for compatibility and will be
/// deprecated in a future version.
///
/// New code should use the [`FromPrimitive`] trait for builtin types instead.
#[allow(clippy::wrong_self_convention)]
impl<'a, M, R: io::Read + 'a> Primitive<'a, M, R> {
    /// Takes a single octet from the content.
    ///
    /// If there aren’t any more octets available from the source, returns
    /// an error.
    fn take_u8(&mut self) -> Result<u8, Error> {
        if self.remaining().to_u64() < 1 {
            return Err(self.content_err_at_current("unexpected end of data"))
        }
        self.read_u8()
    }

    /*
    /// Takes an optional octet from the source.
    ///
    /// If there aren’t any more octets available from the source, returns
    /// `Ok(None)`.
    fn take_opt_u8(&mut self) -> Result<Option<u8>, Error> {
        if self.remaining() < 1 {
            return Ok(None)
        }
        self.take_u8().map(Some)
    }
    */

    /// Decodes the primitive value as a BOOLEAN value.
    pub fn to_bool(&mut self) -> Result<bool, Error>
    where M: Mode {
        let res = self.take_u8()?;
        if M::IS_RESTRICTED {
            match res {
                0 => Ok(false),
                0xFF => Ok(true),
                _ => {
                    Err(self.content_err_at_start("invalid boolean"))
                }
            }
        }
        else {
            Ok(res != 0)
        }
    }

    /// Converts the content into an INTEGER limited to a `i8`.
    pub fn to_i8(&mut self) -> Result<i8, Error> {
        Ok(IntegerArray::from_primitive_ref(self)?.into())
    }

    /// Converts the content into an INTEGER limited to a `i16`.
    pub fn to_i16(&mut self) -> Result<i16, Error> {
        Ok(IntegerArray::from_primitive_ref(self)?.into())
    }

    /// Converts the content into an INTEGER limited to a `i32`.
    pub fn to_i32(&mut self) -> Result<i32, Error> {
        Ok(IntegerArray::from_primitive_ref(self)?.into())
    }

    /// Converts the content into an INTEGER limited to a `i64`.
    pub fn to_i64(&mut self) -> Result<i64, Error> {
        Ok(IntegerArray::from_primitive_ref(self)?.into())
    }

    /// Converts the content into an INTEGER limited to a `i128`.
    pub fn to_i128(&mut self) -> Result<i128, Error> {
        Ok(IntegerArray::from_primitive_ref(self)?.into())
    }

    /// Converts the content into an INTEGER limited to a `u8`.
    pub fn to_u8(&mut self) -> Result<u8, Error> {
        Ok(UnsignedArray::from_primitive_ref(self)?.into())
    }

    /// Converts the content into an INTEGER limited to a `u16`.
    pub fn to_u16(&mut self) -> Result<u16, Error> {
        Ok(UnsignedArray::from_primitive_ref(self)?.into())
    }

    /// Converts the content into an INTEGER limited to a `u32`.
    pub fn to_u32(&mut self) -> Result<u32, Error> {
        Ok(UnsignedArray::from_primitive_ref(self)?.into())
    }

    /// Converts the content into an INTEGER limited to a `u64`.
    pub fn to_u64(&mut self) -> Result<u64, Error> {
        Ok(UnsignedArray::from_primitive_ref(self)?.into())
    }

    /// Converts the content into an INTEGER limited to a `u128`.
    pub fn to_u128(&mut self) -> Result<u128, Error> {
        Ok(UnsignedArray::from_primitive_ref(self)?.into())
    }

    /// Decodes a NULL value.
    ///
    /// Since such a value is empty, this doesn’t really do anything.
    pub fn to_null(&mut self) -> Result<(), Error> {
        if !self.remaining().is_zero() {
            Err(self.content_err_at_start("invalid NULL value"))
        }
        else {
            Ok(())
        }
    }
}


/// # Low-level access
///
impl<'a, M, R: io::Read + 'a> Primitive<'a, M, R> {
    /// Reads data into a buffer, returning the number of bytes read.
    ///
    /// This method behaves nearly identical to `std::io::Read::read`.
    /// However, upon error it returns a `Error` which also reports the
    /// position in the source where the error happened.
    pub fn read(&mut self, buf: &mut [u8]) -> Result<usize, Error> {
        self.source.read(buf).map_err(|err| {
            Error::from_io(err, self.pos())
        })
    }

    /// Reads the exact number of bytes required to fill the buffer.
    pub fn read_exact(&mut self, buf: &mut [u8]) -> Result<(), Error> {
        self.source.read_exact(buf).map_err(|err| {
            Error::from_io(err, self.pos())
        })
    }

    /// Reads the exact number of bytes and appends them to a vec.
    pub fn read_exact_to_vec(
        &mut self, len: usize, target: &mut Vec<u8>
    ) -> Result<(), Error> {
        let start = target.len();
        let target_len = start.checked_add(len).ok_or_else(|| {
            self.content_err_at_start("length overflow")
        })?;
        target.resize(target_len, 0);
        self.read_exact(&mut target[start..])?;
        Ok(())
    }

    /// Reads the exact number of bytes into a box.
    pub fn read_exact_into_box(
        &mut self, len: usize
    ) -> Result<Box<[u8]>, Error> {
        let mut res = vec![0u8; len];
        self.read_exact(&mut res)?;
        Ok(res.into())
    }

    /// Reads the entire content into a boxed slice.
    ///
    /// Will return an overflow error if the remaining length cannot be
    /// converted into a `usize`.
    pub fn read_all_into_box(
        &mut self
    ) -> Result<Box<[u8]>, Error> {
        let len = usize::try_from(self.remaining()).map_err(|_| {
            self.content_err_at_start("content too large")
        })?;
        self.read_exact_into_box(len)
    }

    /// Reads the entire content and appends it to a vec.
    pub fn read_all_to_vec(
        &mut self, target: &mut Vec<u8>
    ) -> Result<(), Error> {
        let len = usize::try_from(self.remaining()).map_err(|_| {
            self.content_err_at_start("content too large")
        })?;
        self.read_exact_to_vec(len, target)
    }

    /// Reads a single bytes from the source.
    pub fn read_u8(&mut self) -> Result<u8, Error> {
        let mut buf = [0u8];
        self.read_exact(&mut buf)?;
        Ok(buf[0])
    }

    pub fn fill_buf(&mut self) -> Result<&[u8], Error>
    where R: io::BufRead {
        let pos = self.pos();
        self.source.fill_buf().map_err(|err| {
            Error::from_io(err, pos)
        })
    }

    pub fn consume(&mut self, amt: usize)
    where R: io::BufRead {
        self.source.consume(amt)
    }

    /// Skip over the next `len` bytes.
    ///
    /// If less than `len` bytes are left, returns an error.
    pub fn skip(&mut self, mut len: Length) -> Result<(), Error>
    where R: io::BufRead {
        while !len.is_zero() {
            let pos = self.pos();
            let buf = self.source.fill_buf().map_err(|err| {
                Error::from_io(err, pos)
            })?;
            let skip = cmp::min(buf.len(), len.to_usize_saturating());
            self.source.consume(skip);
            len -= skip;
        }
        Ok(())
    }

    /// Skips the rest of the content.
    ///
    /// Returns an error if the underlying source ends before the expected
    /// length of content.
    pub fn skip_all(mut self) -> Result<(), Error>
    where R: io::BufRead {
        self.skip(self.remaining())
    }
}


/// # Support for Testing
///
impl Primitive<'static, (), ()> {
    /// Decode a bytes slice via a closure.
    ///
    /// This method can be used in testing code for decoding primitive
    /// values by providing a bytes slice with the content. For instance,
    /// decoding the `to_bool` method could be tested like this:
    ///
    /// ```
    /// use bcder::Tag;
    /// use bcder::decode::{FromPrimitive, Primitive};
    ///
    /// assert_eq!(
    ///     Primitive::decode_slice_ber(
    ///         Tag::BOOLEAN,
    ///         b"\x00",
    ///         |prim| bool::from_primitive(prim)
    ///     ).unwrap(),
    ///     false
    /// )
    /// ```
    pub fn decode_slice_ber<'a, F, T>(
        data: &'a [u8],
        op: F
    ) -> Result<T, Error>
    where
        F: FnOnce(
            Primitive<Ber, &'a [u8]>
        ) -> Result<T, Error>
    {
        let mut source = Source::new(data);
        let mut done = false;
        let prim = Primitive::new(
            Tag::NULL, Length::default(),
            DefiniteSource::new(
                &mut source, &mut done,
                data.len().into()
            ),
        );
        let res = op(prim)?;
        if done {
            Ok(res)
        }
        else {
            Err(Error::content("trailing data", Length::default()))
        }
    }
}


//------------ Constructed ---------------------------------------------------


/// # Processing values (legacy version)
impl<'a, M: Mode, R: io::Read + 'a> Constructed<'a, M, R> {

    /// Decodes the content as a sequence of nested value.
    ///
    /// The method takes two closures. The first is called for constructed
    /// values. It receives a imutable reference to the constructed value,
    /// allowing it to look at the tag and produce an error if necessary.
    /// The second closure receives the primitive values an is expected to
    /// decode their content.
    ///
    /// While both closures return `()` on success, they are `FnMut` closures
    /// so they can capture a mutable reference to some outer variable and
    /// modify it.
    pub fn decode_nested<C, P>(
        self,
        cons_op: C,
        prim_op: P
    ) -> Result<(), Error>
    where
        M: Mode,
        R: io::Read,
        C: FnMut(Tag, Length) -> Result<(), Error>,
        P: FnMut(Primitive<M, R>) -> Result<(), Error>,
    {
        self::nested::decode_nested(self, cons_op, prim_op)
    }
}


// XXX /// # Processing Standard Values


//------------ DefiniteConstructed--------------------------------------------

/// The content of a constructed value with a definite length.
struct DefiniteConstructed<'a, M, R: 'a> {
    source: DefiniteSource<'a, R>,
    nested_done: Option<bool>,
    marker: PhantomData<M>,
}

impl<'a, M: Mode, R: io::Read + 'a> DefiniteConstructed<'a, M, R> {
    fn new(
        source: DefiniteSource<'a, R>
    ) -> Result<Self, io::Error> {
        if M::ALLOW_DEFINITE_CONSTRUCTED {
            Ok(Self {
                source,
                nested_done: None,
                marker: PhantomData,
            })
        }
        else {
            Err(io::Error::new(io::ErrorKind::InvalidData,
                "definite length constructed in CER mode"
            ))
        }
    }

    fn is_end_of_value(&mut self) -> bool {
        if let Some(done) = self.nested_done {
            if done {
                self.nested_done = None;
                true
            }
            else {
                false
            }
        }
        else {
            true
        }
    }

    fn read_ident(&mut self) -> Result<Option<Ident>, io::Error> {
         Ident::read_opt(&mut self.source)
    }

    fn next_value(
        &mut self, ident: Ident, start: Length
    ) -> Result<Content<M, R>, io::Error> {
        match LengthOctets::read::<M>(&mut self.source)?.definite() {
            Some(Length::ZERO) if ident == Ident::END_OF_CONTENTS => {
                Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    "end-of-contents in definite length value"
                ))
            }
            Some(length) => {
                let limit = self.source.pos() + length;
                if limit > self.source.limit() {
                    return Err(io::Error::new(
                        io::ErrorKind::InvalidData,
                        "nested value too long"
                    ))
                }
                let done = self.nested_done.get_or_insert_default();
                let source = DefiniteSource::new(
                    self.source.source(), done, limit
                );
                if ident.is_constructed() {
                    Ok(Content::Constructed(
                        Constructed::new(
                            ident.tag(),
                            start,
                            ConstructedEnum::Definite(
                                DefiniteConstructed::new(source)?
                            ),
                        )
                    ))
                }
                else {
                    Ok(Content::Primitive(Primitive::new(
                        ident.tag(), start, source
                    )))
                }
            }
            None => {
                if !ident.is_constructed() {
                    return Err(io::Error::new(
                        io::ErrorKind::InvalidData,
                        "indefinite length primitive value",
                    ))
                }
                let done = self.nested_done.get_or_insert_default();
                let limit = self.source.limit();
                let source = IndefiniteSource::new(
                    self.source.source(), Some(limit),
                );
                Ok(Content::Constructed(
                    Constructed::new(
                        ident.tag(),
                        start,
                        ConstructedEnum::Indefinite(
                            IndefiniteConstructed::new(source, done)?
                        ),
                    )
                ))
            }
        }
    }
}


//------------ IndefiniteConstructed -----------------------------------------

/// The content of a constructed value with a definite length.
struct IndefiniteConstructed<'a, M, S: 'a> {
    source: IndefiniteSource<'a, S>,
    done: &'a mut bool,
    nested_done: Option<bool>,
    marker: PhantomData<M>,
}

impl<'a, M: Mode, R: io::Read + 'a> IndefiniteConstructed<'a, M, R> {
    fn new(
        source: IndefiniteSource<'a, R>,
        done: &'a mut bool,
    ) -> Result<Self, io::Error> {
        if M::ALLOW_DEFINITE_CONSTRUCTED {
            Ok(Self {
                source,
                done,
                nested_done: None,
                marker: PhantomData
            })
        }
        else {
            Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "indefinite length constructed in DER mode"
            ))
        }
    }

    fn is_end_of_value(&mut self) -> bool {
        if let Some(done) = self.nested_done {
            if done {
                self.nested_done = None;
                true
            }
            else {
                false
            }
        }
        else {
            true
        }
    }

    fn read_ident(&mut self) -> Result<Option<Ident>, io::Error> {
        let ident = Ident::read(&mut self.source)?;
        if ident == Ident::END_OF_CONTENTS {
            if LengthOctets::read::<M>(&mut self.source)?.definite()
                != Some(Length::ZERO)
            {
                Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    "invalid end-of-contents"
                ))
            }
            else {
                *self.done = true;
                Ok(None)
            }
        }
        else {
            Ok(Some(ident))
        }
    }

    fn next_value(
        &mut self, ident: Ident, start: Length
    ) -> Result<Content<M, R>, io::Error> {
        match LengthOctets::read::<M>(&mut self.source)?.definite() {
            Some(length) => {
                let limit = self.source.pos() + length;
                if let Some(parent_limit) = self.source.limit() {
                    if limit > parent_limit {
                        return Err(io::Error::new(
                            io::ErrorKind::InvalidData,
                            "nested value too long"
                        ))
                    }
                }
                let done = self.nested_done.get_or_insert_default();
                let source = DefiniteSource::new(
                    self.source.source(), done, limit
                );
                if ident.is_constructed() {
                    Ok(Content::Constructed(
                        Constructed::new(
                            ident.tag(),
                            start,
                            ConstructedEnum::Definite(
                                DefiniteConstructed::new(source)?
                            ),
                        )
                    ))
                }
                else {
                    Ok(Content::Primitive(Primitive::new(
                        ident.tag(), start, source
                    )))
                }
            }
            None => {
                if !ident.is_constructed() {
                    return Err(io::Error::new(
                        io::ErrorKind::InvalidData,
                        "indefinite length primitive value"
                    ))
                }
                let done = self.nested_done.get_or_insert_default();
                let limit = self.source.limit();
                let source = IndefiniteSource::new(
                    self.source.source(), limit,
                );
                Ok(Content::Constructed(
                    Constructed::new(
                        ident.tag(),
                        start,
                        ConstructedEnum::Indefinite(
                            IndefiniteConstructed::new(source, done)?
                        ),
                    )
                ))
            }
        }
    }
}

