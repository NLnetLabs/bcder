//! Decoding primitive values.
//!
//! This is a private module. The relevant items are re-exported by the
//! parent.

use std::{cmp, error, io};
use std::io::{BufRead, Read};
use std::marker::PhantomData;
use crate::encode;
use crate::captured::Captured;
use crate::ident::Tag;
use crate::int::{IntegerArray, UnsignedArray};
use crate::length::Length;
use crate::mode::Mode;
use super::constructed::Constructed;
use super::error::Error;
use super::source::{CaptureSource, Source, SourceError};


//------------ Primitive -----------------------------------------------------

/// A primitive value for decoding.
///
/// This type provides access to the contents octets. When processing the
/// value, you need to read all contents octets. If you don’t, the outer
/// constructed value will produce a “trailing data” error when trying to
/// progress to the next value. Thus, when decoding the contents, you can
/// stop reading when you think the contents should have ended and leave
/// it to the outer value to produce an error.
///
/// The type is generic over the decoding mode via the `M` type argument.
/// This can be used when certain types have different requirements for the
/// different modes.
pub struct Primitive<'a, M, R: 'a> {
    /// A reference to the underlying source.
    source: PrimitiveSource<'a, R>,

    /// The tag of the value.
    tag: Tag,

    /// The start position of the value in the source.
    ///
    /// This is only used for the ability to produce errors at that position.
    start: Length,

    /// A place for the mode.
    marker: PhantomData<M>,
}

impl<'a, M, R: 'a> Primitive<'a, M, R> {
    /// Creates a new primitive.
    pub(super) fn new(
        source: &'a mut Source<R>, limit: Length, tag: Tag, start: Length
    ) -> Self {
        Self {
            source: PrimitiveSource::new(source, limit),
            tag,
            start,
            marker: PhantomData,
        }
    }

    /// Converts the value into on using a different encoding mode.
    pub fn switch_mode<N>(self) -> Primitive<'a, N, R> {
        Primitive {
            source: self.source,
            tag: self.tag,
            start: self.start,
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

    /// Returns the source’s current position.
    pub fn pos(&self) -> Length {
        self.source.pos()
    }

    /// Returns the number of bytes of content remaning.
    ///
    /// The primitive has been completely read when this value reaches zero.
    pub fn remaining(&self) -> Length {
        self.source.remaining()
    }

    /// Checks for a specific remaining length.
    ///
    /// Returns a “trailing data” error if there are more octets remaining
    /// and a “unexpected end of value” error if there are less.
    pub fn check_remaining(
        &self, len: impl Into<Length>
    ) -> Result<(), Error> {
        let len = len.into();
        match self.remaining().cmp(&len) {
            cmp::Ordering::Greater => {
                Err(self.err_at_current("trailing data"))
            }
            cmp::Ordering::Less => {
                Err(self.err_at_current("unexpected end of value"))
            }
            cmp::Ordering::Equal => {
                Ok(())
            }
        }
    }

    /// Checks that the remaining octets are zero.
    ///
    /// Returns a “trailing data” error if there are remaining octets.
    ///
    /// Calling this method is optional. The check also happens when later
    /// continuing to decode data.
    pub fn check_exhausted(&self) -> Result<(), Error> {
        if !self.remaining().is_zero() {
            Err(self.err_at_current("trailing data"))
        }
        else {
            Ok(())
        }
    }

    /// Produces a content error at the start of the value.
    pub fn err_at_start(
        &self, err: impl Into<Box<dyn error::Error + Send + Sync>>,
    ) -> Error {
        Error::content(err, self.start)
    }

    /// Produces a content error at the current position.
    pub fn err_at_current(
        &self, err: impl Into<Box<dyn error::Error + Send + Sync>>,
    ) -> Error {
        Error::content(err, self.pos())
    }
}


/// # Basic reading
///
impl<'a, M, R: io::BufRead + 'a> Primitive<'a, M, R> {
    /// Reads data until the provided buffer is filled.
    pub fn read_exact(
        &mut self, buf: &mut [u8]
    ) -> Result<(), Error> {
        self.source.read_exact(buf).map_err(|err| {
            Error::from_io(err, self.source.pos())
        })
    }

    /// Reads the exact number of bytes and appends them to a vec.
    pub fn read_exact_to_vec(
        &mut self, len: usize, target: &mut Vec<u8>
    ) -> Result<(), Error> {
        let start = target.len();
        let target_len = start.checked_add(len).ok_or_else(|| {
            self.err_at_start("length overflow")
        })?;
        target.resize(target_len, 0);

        // Safety: start was the length of target before resizing which
        // increases the length.
        #[allow(clippy::indexing_slicing)]
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
            Error::content("content too large", self.start)
        })?;
        self.read_exact_into_box(len)
    }

    /// Reads the entire content and appends it to a vec.
    pub fn read_all_to_vec(
        &mut self, target: &mut Vec<u8>
    ) -> Result<(), Error> {
        let len = usize::try_from(self.remaining()).map_err(|_| {
            self.err_at_start("content too large")
        })?;
        self.read_exact_to_vec(len, target)
    }

    /// Reads a single bytes from the source.
    pub fn read_u8(&mut self) -> Result<u8, Error> {
        let mut buf = [0u8];
        self.read_exact(&mut buf)?;
        Ok(buf[0])
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

    pub fn capture<F>(self, op: F) -> Result<Box<Captured<M>>, Error>
    where F: FnOnce(Primitive<M, CaptureSource<M, R>>) -> Result<(), Error> {
        let mut target = Vec::new();
        encode::infallible(
            encode::write_header(
                &mut target, self.tag, false,
                self.source.limit.saturating_sub(self.source.source.pos())
            )
        );
        let mut source = self.source.source.capture(target);
        op(
            Primitive {
                source: PrimitiveSource {
                    source: &mut source,
                    limit: self.source.limit,
                },
                tag: self.tag,
                start: self.start,
                marker: PhantomData::<M>,
            }
        )?;
        source.into_reader()?.finalize()
    }
}

impl<'s, M> Primitive<'_, M, &'s [u8]> {
    pub fn read_exact_borrowed(
        &mut self, len: usize
    ) -> Result<&'s [u8], Error> {
        self.source.read_exact_borrowed(len).map_err(|err| {
            Error::from_io(err, self.source.pos())
        })
    }

    pub fn read_all_borrowed(&mut self) -> Result<&'s [u8], Error> {
        self.source.read_all_borrowed().map_err(|err| {
            Error::from_io(err, self.source.pos())
        })
    }
}

impl<'a, M, R: io::BufRead + 'a> Primitive<'a, M, R> {
    pub(crate) fn fill_buf(&mut self) -> Result<&[u8], Error> {
        let pos = self.source.pos();
        self.source.fill_buf().map_err(|err| Error::from_io(err, pos))
    }

    pub(crate) fn consume(&mut self, len: usize) {
        self.source.consume(len)
    }
}


/// # High-level parsing.
impl<'a, M, R: io::BufRead + 'a> Primitive<'a, M, R> {
    /// Decodes the primitive value as a BOOLEAN value.
    pub fn into_bool(mut self) -> Result<bool, Error>
    where M: Mode {
        let res = self.read_u8()?;
        self.check_exhausted()?;
        if M::IS_RESTRICTED {
            match res {
                0 => Ok(false),
                0xFF => Ok(true),
                _ => {
                    Err(self.err_at_start("invalid boolean"))
                }
            }
        }
        else {
            Ok(res != 0)
        }
    }

    /// Converts the content into an INTEGER limited to a `i8`.
    pub fn into_i8(self) -> Result<i8, Error> {
        Ok(IntegerArray::from_primitive(self)?.into())
    }

    /// Converts the content into an INTEGER limited to a `i16`.
    pub fn into_i16(self) -> Result<i16, Error> {
        Ok(IntegerArray::from_primitive(self)?.into())
    }

    /// Converts the content into an INTEGER limited to a `i32`.
    pub fn into_i32(self) -> Result<i32, Error> {
        Ok(IntegerArray::from_primitive(self)?.into())
    }

    /// Converts the content into an INTEGER limited to a `i64`.
    pub fn into_i64(self) -> Result<i64, Error> {
        Ok(IntegerArray::from_primitive(self)?.into())
    }

    /// Converts the content into an INTEGER limited to a `i128`.
    pub fn into_i128(self) -> Result<i128, Error> {
        Ok(IntegerArray::from_primitive(self)?.into())
    }

    /// Converts the content into an INTEGER limited to a `u8`.
    pub fn into_u8(self) -> Result<u8, Error> {
        Ok(UnsignedArray::from_primitive(self)?.into())
    }

    /// Converts the content into an INTEGER limited to a `u16`.
    pub fn into_u16(self) -> Result<u16, Error> {
        Ok(UnsignedArray::from_primitive(self)?.into())
    }

    /// Converts the content into an INTEGER limited to a `u32`.
    pub fn into_u32(self) -> Result<u32, Error> {
        Ok(UnsignedArray::from_primitive(self)?.into())
    }

    /// Converts the content into an INTEGER limited to a `u64`.
    pub fn into_u64(self) -> Result<u64, Error> {
        Ok(UnsignedArray::from_primitive(self)?.into())
    }

    /// Converts the content into an INTEGER limited to a `u128`.
    pub fn into_u128(self) -> Result<u128, Error> {
        Ok(UnsignedArray::from_primitive(self)?.into())
    }

    /// Decodes a NULL value.
    ///
    /// Since such a value is empty, this doesn’t really do anything.
    pub fn into_null(self) -> Result<(), Error> {
        if !self.remaining().is_zero() {
            Err(self.err_at_start("invalid NULL value"))
        }
        else {
            Ok(())
        }
    }
}


//------------ PrimitiveSource -----------------------------------------------

/// A private type implementing fundamental reading of primitive content.
struct PrimitiveSource<'a, R: 'a> {
    /// A reference to the underlying source.
    source: &'a mut Source<R>,

    /// The position in the source where this value ends.
    limit: Length,
}

impl<'a, R: 'a> PrimitiveSource<'a, R> {
    fn new(
        source: &'a mut Source<R>, limit: Length
    ) -> Self {
        Self { source, limit }
    }

    /// Returns the source’s current position.
    fn pos(&self) -> Length {
        self.source.pos()
    }

    /// Returns the number of bytes of content remaning.
    ///
    /// The primitive has been completely read when this value reaches zero.
    fn remaining(&self) -> Length {
        self.limit - self.source.pos()
    }
}

impl<'s> PrimitiveSource<'_, &'s [u8]> {
    /// Reads and returns the remainder of the data.
    ///
    /// Returns an error if there are less bytes available than the length of
    /// the primitive.
    fn read_all_borrowed(&mut self) -> Result<&'s [u8], io::Error> {
        self.source.read_exact_borrowed(
            self.remaining().try_to_usize().map_err(|_| {
                io::Error::new(
                    io::ErrorKind::UnexpectedEof,
                    "unexpected end of data"
                )
            })?
        )
    }

    /// Reads and returns the exact number of bytes requested.
    ///
    /// If at least `len` bytes are remaining in the reader, returns a slice
    /// of length `len` and progresses the reader by `len` bytes.
    ///
    /// Returns an error if less than `len` bytes are left.
    fn read_exact_borrowed(
        &mut self, len: usize
    ) -> Result<&'s [u8], io::Error> {
        let len = self.limit.checked_sub(len.into()).ok_or_else(|| {
            io::Error::new(
                io::ErrorKind::UnexpectedEof,
                "unexpected end of data"
            )
        })?.try_to_usize().map_err(|_| {
            io::Error::new(
                io::ErrorKind::UnexpectedEof,
                "unexpected end of data"
            )
        })?;
        self.source.read_exact_borrowed(len)
    }
}


//--- Drop

impl<'a, R: 'a> Drop for PrimitiveSource<'a, R> {
    fn drop(&mut self) {
        if self.source.pos() != self.limit {
            self.source.set_err(SourceError::InvalidData(
                "trailing data"
            ));
        }
    }
}


//--- Read and BufRead

impl<'a, R: io::BufRead + 'a> io::Read for PrimitiveSource<'a, R> {
    fn read(&mut self, buf: &mut [u8]) -> Result<usize, io::Error> {
        let len = cmp::min(
            buf.len(),
            self.remaining().to_usize_saturating(),
        );
        // Safety: len is capped to buf.len()
        #[allow(clippy::indexing_slicing)]
        self.source.read(&mut buf[..len])
    }
}

impl<'a, R: io::BufRead + 'a> io::BufRead for PrimitiveSource<'a, R> {
    fn fill_buf(&mut self) -> Result<&[u8], io::Error> {
        let remaining = self.remaining().to_usize_saturating();
        let res = self.source.fill_buf()?;
        match res.get(..remaining) {
            Some(shortened) => Ok(shortened),
            None => Ok(res)
        }
    }

    fn consume(&mut self, amt: usize) {
        self.source.consume(
            cmp::min(amt, self.remaining().to_usize_saturating())
        );
            
    }
}


//------------ FromPrimitive ------------------------------------------------

pub trait FromPrimitive<M>: Sized {
    /// The natural tag of an encoded value of this type.
    const TAG: Tag;

    fn from_primitive<R: io::BufRead>(
        primitive: Primitive<M, R>
    ) -> Result<Self, Error>;

    fn take_from<R: io::BufRead>(
        cons: &mut Constructed<M, R>
    ) -> Result<Self, Error>
    where M: Mode {
        cons.take_primitive_with(Self::TAG, Self::from_primitive)
    }

    fn take_opt_from<R: io::BufRead>(
        cons: &mut Constructed<M, R>
    ) -> Result<Option<Self>, Error>
    where M: Mode {
        cons.take_opt_primitive_with(Self::TAG, Self::from_primitive)
    }
}

impl<M: Mode> FromPrimitive<M> for bool {
    const TAG: Tag = Tag::BOOLEAN;

    fn from_primitive<R: io::BufRead>(
        mut prim: Primitive<M, R>
    ) -> Result<Self, Error> {
        prim.check_remaining(1u64)?;
        let res = prim.read_u8()?;
        if M::IS_RESTRICTED {
            match res {
                0x00 => Ok(false),
                0xFF => Ok(true),
                _ => {
                    Err(prim.err_at_start("invalid boolean"))
                }
            }
        }
        else {
            Ok(res != 0)
        }
    }
}

impl<M> FromPrimitive<M> for () {
    const TAG: Tag = Tag::NULL;

    fn from_primitive<R: io::BufRead>(
        prim: Primitive<M, R>
    ) -> Result<Self, Error> {
        prim.check_exhausted()
    }
}


//============ Testing =======================================================

#[cfg(test)]
mod test {
    use crate::mode::Ber;
    use super::*;

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
            let res = {
                let prim = Primitive::new(
                    &mut source, data.len().into(),
                    Tag::NULL, Length::default(),
                );
                op(prim)?
            };
            source.check_status().map_err(|err| {
                Error::from_io(err, source.pos())
            })?;
            Ok(res)
        }
    }
}

