#![allow(dead_code)] // XXXX REMOVE

// XXX Continue with Constructed::skip_opt, then do Content.

use std::{error, fmt};
use std::convert::Infallible;
use std::marker::PhantomData;
use crate::mode::{Ber, Cer, Der, Mode, Restricted};
use crate::length::Length;
use crate::tag::Tag;
use super::error::{ContentError, DecodeError};
use super::source::{
    Fragment, IntoSource, LimitedFragment, LimitedSource,
    MaybeLimitedSource, Pos, SliceSource, Source
};


//------------ Content -------------------------------------------------------

/// The content octets of a BER-encoded value.
///
/// A value is either primitive, containing actual octets of an actual value,
/// or constructed, in which case its content contains additional BER encoded
/// values. This enum is useful for cases where a certain type may be encoded
/// as either a primitive value or a complex constructed value.
///
/// Note that this type represents the content octets only, i.e., it does not
/// contain the tag of the value.
pub enum Content<'a, M, S: 'a> {
    /// The value is a primitive value.
    Primitive(Primitive<'a, M, S>),

    /// The value is a constructed value.
    Constructed(Constructed<'a, M, S>)
}

impl <'a, M: Mode, S: Source + 'a> Content<'a, M, S> {
    fn check_exhausted(&mut self) -> Result<(), DecodeError<S::Error>> {
        match self {
            Self::Primitive(inner) => inner.check_exhausted(),
            Self::Constructed(inner) => inner.check_exhausted(),
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

    /// Converts a reference into into one to a primitive value or errors out.
    pub fn as_primitive(
        &mut self
    ) -> Result<&mut Primitive<'a, M, S>, DecodeError<S::Error>> {
        match *self {
            Content::Primitive(ref mut inner) => Ok(inner),
            Content::Constructed(ref inner) => {
                Err(inner.content_err("expected primitive value"))
            }
        }
    }

    /// Converts a reference into on to a constructed value or errors out.
    pub fn as_constructed(
        &mut self
    ) -> Result<&mut Constructed<'a, M, S>, DecodeError<S::Error>> {
        match *self {
            Content::Primitive(ref inner) => {
                Err(inner.content_err("expected constructed value"))
            }
            Content::Constructed(ref mut inner) => Ok(inner),
        }
    }
}


//------------ Primitive -----------------------------------------------------

/// The content of a primitive value.
///
/// You will receive a reference to a value of this type through a closure,
/// possibly wrapped in a [`Content`] value. Your task will be to read out all
/// the octets of the value before returning from the closure or produce an
/// error if the value isn’t correctly encoded. If you read less octets than
/// are available, whoever called the closure will produce an error after
/// you returned. Thus, you can read as many octets as you expect and not
/// bother to check whether you did read all the way to the end.
///
/// The most basic way to do this is through the primitive’s implementation
/// of the [`Source`] trait. Thus, you can gain access to [`Fragment`]s of
/// the content and consuming them. You can safely attempt to request larger
/// fragments than than available as that will reliably result in an
/// error.
///
/// A number of methods are available to deal with the encodings defined for
/// various types. These are prefixed by `to_` to indicate that they are
/// intended to convert the content to a certain type. They all read exactly
/// one encoded value.
///
/// The value is generic over the decoding mode via the `M` type argument.
/// All methodes that decode data will honour the decoding mode and enforce
/// that data is encoded according to the mode.
pub struct Primitive<'a, M, S: 'a> {
    /// The underlying source limited to the length of the value.
    source: LimitedSource<'a, S>,

    /// The start position of the value in the source.
    start: Pos,

    /// The decoding mode to operate in.
    marker: PhantomData<M>,
}

impl<'a, M, S: 'a> Primitive<'a, M, S> {
    /// Creates a new primitive from the given source and mode.
    fn new(source: LimitedSource<'a, S>) -> Self
    where S: Source {
        Primitive {
            start: source.pos(),
            source,
            marker: PhantomData
        }
    }
}

impl<'a, M, S: Source + 'a> Primitive<'a, M, S> {
    /// Produces a content error at the start of the primitive.
    ///
    /// If you instead want to produce an error at the currrent source
    /// position, you can use [`content_err`] provided by the [`Source`]
    /// impl instead.
    pub fn content_err_at_start(
        &self, err: impl Into<ContentError>,
    ) -> DecodeError<S::Error> {
        DecodeError::content(err, self.start)
    }
}


/// # High-level Decoding
///
impl<'a, S: Source + 'a> Primitive<'a, Ber, S> {
    /// Parses the primitive value as a BOOLEAN value.
    pub fn to_bool(&mut self) -> Result<bool, DecodeError<S::Error>> {
        self.to_single_u8().map(|value| value != 0)
    }
}

impl<'a, M: Restricted, S: Source + 'a> Primitive<'a, M, S> {
    /// Parses the primitive value as a BOOLEAN value.
    pub fn to_bool(&mut self) -> Result<bool, DecodeError<S::Error>> {
        match self.to_single_u8()? {
            0x00 => Ok(false),
            0xFF => Ok(true),
            _ => {
                Err(DecodeError::content("invalid boolean", self.pos()))
            }
        }
    }
}

impl<'a, M: Restricted, S: Source + 'a> Primitive<'a, M, S> {
    /// Converts the content octets to a NULL value.
    ///
    /// Since such a value is empty, this doesn’t really do anything.
    pub fn to_null(&mut self) -> Result<(), DecodeError<S::Error>> {
        if self.remaining() > 0 {
            Err(self.content_err("invalid NULL value"))
        }
        else {
            Ok(())
        }
    }
}


/// # Low-level Access
///
/// For basic low-level access, `Primitive` implements the [`Source`] trait.
/// Because the length of the content is guaranteed to be known, it can
/// provide a few additional methods. Note that these may still fail because
/// the underlying source doesn’t guarantee that as many octets are actually
/// available.
impl<'a, M, S: Source + 'a> Primitive<'a, M, S> {
    /// Returns the number of remaining octets.
    ///
    /// The returned value reflects what is left of the expected length of
    /// content and therefore decreases when the primitive is advanced.
    pub fn remaining(&self) -> usize {
        self.source.limit()
    }

    /// Skips the rest of the content.
    ///
    /// Returns a malformed error if the source ends before the expected
    /// length of content.
    pub fn skip_all(&mut self) -> Result<(), DecodeError<S::Error>> {
        self.request_all().map(|frag| frag.consume())
    }

    /// Requests a fragment with the complete remaining content.
    ///
    /// Returns an error if the source ends before the end of the content.
    /// Thus, the slice of the returned fragment is guaranteed to be the full
    /// content.
    pub fn request_all<'f>(
        &'f mut self
    ) -> Result<LimitedFragment<'f, S>, DecodeError<S::Error>> {
        self.source.request_all()
    }

    fn to_single_u8(&mut self) -> Result<u8, DecodeError<S::Error>> {
        let frag = self.source.request_all()?;
        let Some(res) = frag.slice().first().copied() else {
            return Err(DecodeError::content("empty primitive", self.start))
        };
        if frag.slice().len() > 1 {
            return Err(DecodeError::content(
                "trailing data in primitive", self.start
            ))
        }
        Ok(res)
    }

    /// Checks that all content has been consumed.
    fn check_exhausted(&self) -> Result<(), DecodeError<S::Error>> {
        if self.source.is_exhausted() {
            Ok(())
        }
        else {
            Err(self.source.content_err("trailing_data"))
        }
    }
}


/// # Support for Testing
///
impl<M> Primitive<'static, M, ()> {
    /// Decode a bytes slice in BER mode via a closure.
    ///
    /// This method can be used in testing code for decoding primitive
    /// values by providing a bytes slice with the content. For instance,
    /// decoding the `to_bool` method could be tested like this:
    ///
    /// ```
    /// use bcder::decode::Primitive;
    ///
    /// assert_eq!(
    ///     Primitive::decode_slice_ber(
    ///         b"\x00".as_ref(),
    ///         |prim| prim.to_bool()
    ///     ).unwrap(),
    ///     false
    /// )
    /// ```
    pub fn decode_slice_ber<F, T>(
        data: &[u8],
        op: F
    ) -> Result<T, DecodeError<Infallible>>
    where
        F: FnOnce(
            &mut Primitive<Ber, SliceSource>
        ) -> Result<T, DecodeError<Infallible>>
    {
        let mut source = data.into_source();
        let lim = LimitedSource::new(&mut source, data.len());
        let mut prim = Primitive::new(lim);
        let res = op(&mut prim)?;
        prim.check_exhausted()?;
        Ok(res)
    }

    /// Decode a bytes slice in CER mode via a closure.
    ///
    /// This method can be used in testing code for decoding primitive
    /// values by providing a bytes slice with the content. For instance,
    /// decoding the `to_bool` method could be tested like this:
    ///
    /// ```
    /// use bcder::decode::Primitive;
    ///
    /// assert_eq!(
    ///     Primitive::decode_slice_cer(
    ///         b"\x00".as_ref()
    ///         |prim| prim.to_bool()
    ///     ).unwrap(),
    ///     false
    /// )
    /// ```
    pub fn decode_slice_cer<F, T>(
        data: &[u8],
        op: F
    ) -> Result<T, DecodeError<Infallible>>
    where
        F: FnOnce(
            &mut Primitive<Cer, SliceSource>
        ) -> Result<T, DecodeError<Infallible>>
    {
        let mut source = data.into_source();
        let lim = LimitedSource::new(&mut source, data.len());
        let mut prim = Primitive::new(lim);
        let res = op(&mut prim)?;
        prim.check_exhausted()?;
        Ok(res)
    }

    /// Decode a bytes slice in DER mode via a closure.
    ///
    /// This method can be used in testing code for decoding primitive
    /// values by providing a bytes slice with the content. For instance,
    /// decoding the `to_bool` method could be tested like this:
    ///
    /// ```
    /// use bcder::decode::Primitive;
    ///
    /// assert_eq!(
    ///     Primitive::decode_slice_der(
    ///         b"\x00".as_ref()
    ///         |prim| prim.to_bool()
    ///     ).unwrap(),
    ///     false
    /// )
    /// ```
    pub fn decode_slice_der<F, T>(
        data: &[u8],
        op: F
    ) -> Result<T, DecodeError<Infallible>>
    where
        F: FnOnce(
            &mut Primitive<Der, SliceSource>
        ) -> Result<T, DecodeError<Infallible>>
    {
        let mut source = data.into_source();
        let lim = LimitedSource::new(&mut source, data.len());
        let mut prim = Primitive::new(lim);
        let res = op(&mut prim)?;
        prim.check_exhausted()?;
        Ok(res)
    }
}


//--- Source

impl<'a, M, S: Source + 'a> Source for Primitive<'a, M, S> {
    type Fragment<'f> = LimitedFragment<'f, S> where Self: 'f, S: 'f;
    type Error = S::Error;

    fn pos(&self) -> Pos {
        self.source.pos()
    }

    fn request<'f>(
        &'f mut self, len: usize
    ) -> Result<LimitedFragment<'f, S>, Self::Error> {
        self.source.request(len)
    }
}


//------------ Constructed ---------------------------------------------------

/// The content of a constructed value.
///
/// You will only ever receive a mutable reference to a value of this type
/// as an argument to a closure provided to some function. The closure will
/// have to process all content of the constructed value.
///
/// Since constructed values consist of a sequence of values, the methods
/// allow you to process these values one by one. The most basic of these
/// are [`take_value`] and [`take_opt_value`] which process exactly one
/// value or up to one value, respectively. A number of convenience functions
/// exists on top of them for commonly encountered types and cases.
///
/// Because the caller of your closure checks whether all content has been
/// advanced over and raising an error of not, you only need to read as many
/// values as you expected to be present and can simply return when you think
/// you are done.
///
/// [`take_value`]: #method.take_value
/// [`take_opt_value`]: #method.take_opt_value
pub struct Constructed<'a, M, S: 'a> {
    inner: ConstructedEnum<'a, M, S>,

    /// The start position of the value in the source.
    start: Pos,
}

enum ConstructedEnum<'a, M, S> {
    Definite(DefiniteConstructed<'a, M, S>),
    Indefinite(IndefiniteConstructed<'a, M, S>),
    Unbounded(UnboundedConstructed<'a, M, S>),
}

/// # General Management
///
impl<'a, M: Mode, S: Source + 'a> Constructed<'a, M, S> {
    /// Decode a source as constructed content.
    ///
    /// The function will start decoding of `source` in the given mode. It
    /// will pass a constructed content value to the closure `op` which
    /// has to process all the content and return a result or error.
    ///
    /// This function is identical to calling `decode` on one of the mode
    /// structs, e.g., [`Der::decode`].
    pub fn decode<I, F, T>(
        source: I, op: F,
    ) -> Result<T, DecodeError<S::Error>>
    where
        I: IntoSource<Source = S>,
        F: FnOnce(&mut Constructed<M, S>) -> Result<T, DecodeError<S::Error>>
    {
        let mut source = source.into_source();
        let mut cons = Constructed {
            inner: {
                ConstructedEnum::Unbounded(
                    UnboundedConstructed::new(&mut source)
                )
            },
            start: 0.into(),
        };
        let res = op(&mut cons)?;
        cons.check_exhausted()?;
        Ok(res)
    }

    /// Produces a content error at the current position.
    pub fn content_err(
        &self, err: impl Into<ContentError>,
    ) -> DecodeError<S::Error> {
        match &self.inner {
            ConstructedEnum::Definite(inner) => {
                inner.source.content_err(err)
            }
            ConstructedEnum::Indefinite(inner) => {
                inner.source.content_err(err)
            }
            ConstructedEnum::Unbounded(inner) => {
                inner.source.content_err(err)
            }
        }
    }
            

    /// Produces a content error at the start of the value.
    pub fn content_err_at_start(
        &self, err: impl Into<ContentError>,
    ) -> DecodeError<S::Error> {
        DecodeError::content(err, self.start)
    }
}

/// # Fundamental Reading
///
impl<'a, M: Mode, S: Source + 'a> Constructed<'a, M, S> {
    /// Processes the next value.
    ///
    /// If `expected` is not `None`, the method will only process a value
    /// with the given tag and return `Ok(None)` if there isn’t another value
    /// or if the next value has a different tag.
    ///
    /// If `expected` is `None`, the method will process a value with any
    /// tag and only return `Ok(None)` if it reached the end of the value.
    ///
    /// The closure `op` receives both the tag and content for the next
    /// value. It must process the value, advancing the source to its end
    /// or return an error.
    fn process_next_value<F, T>(
        &mut self,
        expected: Option<Tag>,
        op: F
    ) -> Result<Option<T>, DecodeError<S::Error>>
    where
        F: FnOnce(
            Tag, &mut Content<M, S>
        ) -> Result<T, DecodeError<S::Error>>
    {
        match &mut self.inner {
            ConstructedEnum::Definite(inner) => {
                inner.process_next_value(expected, op)
            }
            ConstructedEnum::Indefinite(inner) => {
                inner.process_next_value(expected, op)
            }
            ConstructedEnum::Unbounded(inner) => {
                inner.process_next_value(expected, op)
            }
        }
    }

    /// Checks that the content has been exhausted.
    fn check_exhausted(&mut self) -> Result<(), DecodeError<S::Error>> {
        match &mut self.inner {
            ConstructedEnum::Definite(inner) => inner.check_exhausted(),
            ConstructedEnum::Indefinite(inner) => inner.check_exhausted(),
            ConstructedEnum::Unbounded(inner) => inner.check_exhausted(),
        }
    }

    /// Makes sure the next value is present.
    fn mandatory<F, T>(
        &mut self, op: F,
    ) -> Result<T, DecodeError<S::Error>>
    where
        F: FnOnce(
            &mut Constructed<M, S>
        ) -> Result<Option<T>, DecodeError<S::Error>>,
    {
        match op(self)? {
            Some(res) => Ok(res),
            None => Err(self.content_err("missing further values")),
        }
    }
}

/// # Processing Contained Values
///
/// The methods in this section each process one value of the constructed
/// value’s content.
impl<'a, M: Mode, S: Source + 'a> Constructed<'a, M, S> {
    /// Process one value of content.
    ///
    /// The closure `op` receives the tag and content of the next value
    /// and must process it completely, advancing to the content’s end.
    ///
    /// Upon success, the method returns the closure’s return value. The
    /// method returns a malformed error if there isn’t at least one more
    /// value available. It also returns an error if the closure returns one
    /// or if reading from the source fails.
    pub fn take_value<F, T>(
        &mut self, op: F,
    ) -> Result<T, DecodeError<S::Error>>
    where
        F: FnOnce(Tag, &mut Content<M, S>) -> Result<T, DecodeError<S::Error>>,
    {
        match self.process_next_value(None, op)? {
            Some(res) => Ok(res),
            None => Err(self.content_err("missing further values")),
        }
    }

    /// Processes an optional value.
    ///
    /// If there is at least one more value available, the closure `op` is
    /// given the tag and content of that value and must process it
    /// completely, advancing to the end of its content. If the closure
    /// succeeds, its return value is returned as ‘some’ result.
    ///
    /// If there are no more values available, the method returns `Ok(None)`.
    /// It returns an error if the closure returns one or if reading from
    /// the source fails.
    pub fn take_opt_value<F, T>(
        &mut self, op: F,
    ) -> Result<Option<T>, DecodeError<S::Error>>
    where
        F: FnOnce(Tag, &mut Content<M, S>) -> Result<T, DecodeError<S::Error>>,
    {
        self.process_next_value(None, op)
    }

    /// Processes a value with the given tag.
    ///
    /// If the next value has the tag `expected`, its content is being given
    /// to the closure which has to process it completely and return whatever
    /// is being returned upon success.
    ///
    /// The method will return a malformed error if it encounters any other
    /// tag or the end of the value. It will also return an error if the
    /// closure returns an error or doesn’t process the complete values, or
    /// if accessing the underlying source fails.
    pub fn take_value_if<F, T>(
        &mut self,
        expected: Tag,
        op: F
    ) -> Result<T, DecodeError<S::Error>>
    where F: FnOnce(&mut Content<M, S>) -> Result<T, DecodeError<S::Error>> {
        let res = self.process_next_value(Some(expected), |_, content| {
            op(content)
        })?;
        match res {
            Some(res) => Ok(res),
            None => Err(self.content_err(ExpectedTag(expected))),
        }
    }

    /// Processes an optional value with the given tag.
    ///
    /// If the next value has the tag `expected`, its content is being given
    /// to the closure which has to process it completely and return whatever
    /// is to be returned as some value.
    ///
    /// If the next value has a different tag or if the end of the value has
    /// been reached, the method returns `Ok(None)`. It will return an error
    /// if the closure fails or doesn’t process the complete value, or if
    /// accessing the underlying source fails.
    pub fn take_opt_value_if<F, T>(
        &mut self,
        expected: Tag,
        op: F
    ) -> Result<Option<T>, DecodeError<S::Error>>
    where F: FnOnce(&mut Content<M, S>) -> Result<T, DecodeError<S::Error>> {
        self.process_next_value(Some(expected), |_, content| op(content))
    }

    /// Processes a constructed value.
    ///
    /// If the next value is a constructed value, its tag and content are
    /// being given to the closure `op` which has to process it completely.
    /// If it succeeds, its return value is returned.
    ///
    /// If the next value is not a constructed value or there is no next
    /// value or if the closure doesn’t process the next value completely,
    /// a malformed error is returned. An error is also returned if the
    /// closure returns one or if accessing the underlying source fails.
    pub fn take_constructed<F, T>(
        &mut self, op: F
    ) -> Result<T, DecodeError<S::Error>>
    where
        F: FnOnce(
            Tag, &mut Constructed<M, S>
        ) -> Result<T, DecodeError<S::Error>>,
    {
        self.mandatory(|cons| cons.take_opt_constructed(op))
    }

    /// Processes an optional constructed value.
    ///
    /// If the next value is a constructed value, its tag and content are
    /// being given to the closure `op` which has to process it completely.
    /// If it succeeds, its return value is returned as some value.
    ///
    /// If the end of the value has been reached, the method returns
    /// `Ok(None)`.
    ///
    /// If the next value is not a constructed value or if the closure
    /// doesn’t process the next value completely, a malformed error is
    /// returned. An error is also returned if the closure returns one or
    /// if accessing the underlying source fails.
    pub fn take_opt_constructed<F, T>(
        &mut self,
        op: F
    ) -> Result<Option<T>, DecodeError<S::Error>>
    where
        F: FnOnce(
            Tag, &mut Constructed<M, S>,
        ) -> Result<T, DecodeError<S::Error>>
    {
        self.process_next_value(None, |tag, content| {
            op(tag, content.as_constructed()?)
        })
    }

    /// Processes a constructed value with a required tag.
    ///
    /// If the next value is a constructed value with a tag equal to
    /// `expected`, its content is given to the closure `op` which has to
    /// process it completely. If the closure succeeds, its return value
    /// is returned.
    ///
    /// If the next value is not constructed or has a different tag, if
    /// the end of the value has been reached, or if the closure does not
    /// process the contained value’s content completely, a malformed error
    /// is returned. An error is also returned if the closure returns one or
    /// if accessing the underlying source fails.
    pub fn take_constructed_if<F, T>(
        &mut self,
        expected: Tag,
        op: F,
    ) -> Result<T, DecodeError<S::Error>>
    where
        F: FnOnce(&mut Constructed<M, S>) -> Result<T, DecodeError<S::Error>>,
    {
        self.mandatory(|cons| cons.take_opt_constructed_if(expected, op))
    }

    /// Processes an optional constructed value if it has a given tag.
    ///
    /// If the next value is a constructed value with a tag equal to
    /// `expected`, its content is given to the closure `op` which has to
    /// process it completely. If the closure succeeds, its return value
    /// is returned.
    ///
    /// If the next value is not constructed, does not have the expected tag,
    /// or the end of this value has been reached, the method returns
    /// `Ok(None)`. It returns a malformed error if the closure does not
    /// process the content of the next value fully.
    ///
    /// An error is also returned if the closure returns one or if accessing
    /// the underlying source fails.
    pub fn take_opt_constructed_if<F, T>(
        &mut self,
        expected: Tag,
        op: F,
    ) -> Result<Option<T>, DecodeError<S::Error>>
    where
        F: FnOnce(&mut Constructed<M, S>) -> Result<T, DecodeError<S::Error>>,
    {
        self.process_next_value(Some(expected), |_, content| {
            op(content.as_constructed()?)
        })
    }

    /// Processes a primitive value.
    ///
    /// If the next value is primitive, its tag and content are given to the
    /// closure `op` which has to process it fully. Upon success, the
    /// closure’s return value is returned.
    ///
    /// If the next value is not primitive, if the end of value has been
    /// reached, or if the closure fails to process the next value’s content
    /// fully, a malformed error is returned. An error is also returned if
    /// the closure returns one or if accessing the underlying source fails.
    pub fn take_primitive<F, T>(
        &mut self, op: F,
    ) -> Result<T, DecodeError<S::Error>>
    where
        F: FnOnce(
            Tag, &mut Primitive<M, S>
        ) -> Result<T, DecodeError<S::Error>>,
    {
        self.mandatory(|cons| cons.take_opt_primitive(op))
    }

    /// Processes an optional primitive value.
    ///
    /// If the next value is primitive, its tag and content are given to the
    /// closure `op` which has to process it fully. Upon success, the
    /// closure’s return value is returned.
    /// 
    /// If the next value is not primitive or if the end of value has been
    /// reached, `Ok(None)` is returned.
    /// If the closure fails to process the next value’s content fully, a
    /// malformed error is returned. An error is also returned if
    /// the closure returns one or if accessing the underlying source fails.
    pub fn take_opt_primitive<F, T>(
        &mut self, op: F,
    ) -> Result<Option<T>, DecodeError<S::Error>>
    where
        F: FnOnce(
            Tag, &mut Primitive<M, S>
        ) -> Result<T, DecodeError<S::Error>>,
    {
        self.process_next_value(None, |tag, content| {
            op(tag, content.as_primitive()?)
        })
    }

    /// Processes a primitive value if it has the right tag.
    ///
    /// If the next value is a primitive and its tag matches `expected`, its
    /// content is given to the closure `op` which has to process it
    /// completely or return an error, either of which is returned.
    ///
    /// The method returns a malformed error if there is no next value, if the
    /// next value is not a primitive, if it doesn’t have the right tag, or if
    /// the closure doesn’t advance over the complete content. If access to
    /// the underlying source fails, an error is returned, too.
    pub fn take_primitive_if<F, T>(
        &mut self, expected: Tag, op: F,
    ) -> Result<T, DecodeError<S::Error>>
    where F: FnOnce(&mut Primitive<M, S>) -> Result<T, DecodeError<S::Error>> {
        self.mandatory(|cons| cons.take_opt_primitive_if(expected, op))
    }

    /// Processes an optional primitive value of a given tag.
    ///
    /// If the next value is a primitive and its tag matches `expected`, its
    /// content is given to the closure `op` which has to process it
    /// completely or return an error, either of which is returned.
    ///
    /// If the end of this value has been reached, if the next value is not
    /// a primitive or if its tag doesn’t match, the method returns
    /// `Ok(None)`. If the closure doesn’t process the next value’s content
    /// fully the method returns a malformed error. If access to the
    /// underlying source fails, it returns an appropriate error.
    pub fn take_opt_primitive_if<F, T>(
        &mut self, expected: Tag, op: F,
    ) -> Result<Option<T>, DecodeError<S::Error>>
    where F: FnOnce(&mut Primitive<M, S>) -> Result<T, DecodeError<S::Error>> {
        self.process_next_value(Some(expected), |_, content| {
            op(content.as_primitive()?)
        })
    }
}


//------------ DefiniteConstructed--------------------------------------------

/// The content of a constructed value with a definite length.
pub struct DefiniteConstructed<'a, M, S: 'a> {
    source: LimitedSource<'a, S>,
    marker: PhantomData<M>,
}

impl<'a, M: Mode, S: Source + 'a> DefiniteConstructed<'a, M, S> {
    fn new(
        source: LimitedSource<'a, S>,
    ) -> Result<Self, DecodeError<S::Error>> {
        if M::ALLOW_DEFINITE_CONSTRUCTED {
            Ok(Self { source, marker: PhantomData, })
        }
        else {
            Err(source.content_err("definite length constructed in CER mode"))
        }
    }

    fn process_next_value<F, T>(
        &mut self,
        expected: Option<Tag>,
        op: F
    ) -> Result<Option<T>, DecodeError<S::Error>>
    where
        F: FnOnce(
            Tag, &mut Content<M, S>
        ) -> Result<T, DecodeError<S::Error>>
    {
        if self.source.is_exhausted() {
            return Ok(None)
        }

        let (tag, constructed) = if let Some(expected) = expected {
            (
                expected,
                match expected.take_from_if(&mut self.source)? {
                    Some(constructed) => constructed,
                    None => return Ok(None)
                }
            )
        }
        else {
            Tag::take_from(&mut self.source)?
        };

        if tag == Tag::END_OF_VALUE {
            return Err(self.source.content_err("unexpected end of value"))
        }
        let length = Length::<M>::take_from(&mut self.source)?;

        let start = self.source.pos();
        match length.definite() {
            Some(len) => {
                if len > self.source.limit() {
                    return Err(self.source.content_err(
                        "nested value with excessive length"
                    ))
                }
                let source = LimitedSource::new(
                    self.source.source_mut(),
                    len
                );
                let mut content = if constructed {
                    Content::Constructed(
                        Constructed {
                            inner: ConstructedEnum::Definite(
                                DefiniteConstructed::new(source)?,
                            ),
                            start,
                        }
                    )
                }
                else {
                    Content::Primitive(Primitive::new(source))
                };
                let res = op(tag, &mut content)?;
                content.check_exhausted()?;
                Ok(Some(res))
            }
            None => {
                if constructed {
                    return Err(self.source.content_err(
                        "indefinite length primitive value"
                    ))
                }
                let limit = self.source.limit();
                let source = MaybeLimitedSource::new(
                    self.source.source_mut(),
                    Some(limit),
                );
                let mut content = Content::Constructed(
                    Constructed {
                        inner: ConstructedEnum::Indefinite(
                            IndefiniteConstructed::new(source)?,
                        ),
                        start,
                    }
                );
                let res = op(tag, &mut content)?;
                content.check_exhausted()?;
                Ok(Some(res))
            }
        }
    }

    fn check_exhausted(&self) -> Result<(), DecodeError<S::Error>> {
        if self.source.is_exhausted() {
            Ok(())
        }
        else {
            Err(self.source.content_err("unexpected trailing values"))
        }
    }
}


//------------ IndefiniteConstructed -----------------------------------------

/// The content of a constructed value with a definite length.
pub struct IndefiniteConstructed<'a, M, S: 'a> {
    source: MaybeLimitedSource<'a, S>,
    done: bool,
    marker: PhantomData<M>,
}

impl<'a, M: Mode, S: Source + 'a> IndefiniteConstructed<'a, M, S> {
    fn new(
        source: MaybeLimitedSource<'a, S>,
    ) -> Result<Self, DecodeError<S::Error>> {
        if M::ALLOW_DEFINITE_CONSTRUCTED {
            Ok(Self {
                source,
                done: false,
                marker: PhantomData,
            })
        }
        else {
            Err(source.content_err(
                "indefinite length constructed in DER mode"
            ))
        }
    }

    fn process_next_value<F, T>(
        &mut self,
        expected: Option<Tag>,
        op: F
    ) -> Result<Option<T>, DecodeError<S::Error>>
    where
        F: FnOnce(
            Tag, &mut Content<M, S>
        ) -> Result<T, DecodeError<S::Error>>
    {
        if self.done {
            return Ok(None)
        }

        let (tag, constructed) = if let Some(expected) = expected {
            (
                expected,
                match expected.take_from_if(&mut self.source)? {
                    Some(constructed) => constructed,
                    None => return Ok(None)
                }
            )
        }
        else {
            Tag::take_from(&mut self.source)?
        };
        let length = Length::<M>::take_from(&mut self.source)?;

        if tag == Tag::END_OF_VALUE {
            if constructed {
                return Err(self.source.content_err(
                    "constructed end of value"
                ))
            }
            if !length.is_zero() {
                return Err(self.source.content_err(
                    "non-empty end of value"
                ))
            }
            self.done = true;
            return Ok(None)
        }

        let start = self.source.pos();
        match length.definite() {
            Some(len) => {
                if let Some(limit) = self.source.limit() {
                    if len > limit {
                        return Err(self.source.content_err(
                            "nested value with excessive length"
                        ))
                    }
                }
                let source = LimitedSource::new(
                    self.source.source_mut(), len
                );
                let mut content = if constructed {
                    Content::Constructed(
                        Constructed {
                            inner: ConstructedEnum::Definite(
                                DefiniteConstructed::new(source)?,
                            ),
                            start,
                        }
                    )
                }
                else {
                    Content::Primitive(Primitive::new(source))
                };
                let res = op(tag, &mut content)?;
                content.check_exhausted()?;
                Ok(Some(res))
            }
            None => {
                if constructed {
                    return Err(self.source.content_err(
                        "indefinite length primitive value"
                    ))
                }
                let limit = self.source.limit();
                let source = MaybeLimitedSource::new(
                    self.source.source_mut(),
                    limit,
                );
                let mut content = Content::Constructed(
                    Constructed {
                        inner: ConstructedEnum::Indefinite(
                            IndefiniteConstructed::new(source)?,
                        ),
                        start,
                    }
                );
                let res = op(tag, &mut content)?;
                content.check_exhausted()?;
                Ok(Some(res))
            }
        }
    }

    fn check_exhausted(&mut self) -> Result<(), DecodeError<S::Error>> {
        // If we are self.done, we read the end-of-value as the last thing,
        // probably as part of some sort of take_opt. Otherwise we need to
        // read the next value and it better be an end-of-value.
        if self.done {
            return Ok(())
        }
        let (tag, constructed) = Tag::take_from(&mut self.source)?;
        if tag != Tag::END_OF_VALUE {
            return Err(self.source.content_err("unexpected trailing values"));
        }
        if constructed {
            return Err(self.source.content_err(
                "constructed end of value"
            ))
        }
        if !Length::<M>::take_from(&mut self.source)?.is_zero() {
            return Err(self.source.content_err(
                "non-empty end of value"
            ))
        }
        self.done = true;
        return Ok(())
    }
}


//------------ UnboundedConstructed ------------------------------------------

/// The content of a constructed value covering the entire source.
pub struct UnboundedConstructed<'a, M, S: 'a> {
    source: &'a mut S,
    marker: PhantomData<M>,
}

impl<'a, M: Mode, S: Source + 'a> UnboundedConstructed<'a, M, S> {
    fn new(
        source: &'a mut S,
    ) -> Self {
        Self { source, marker: PhantomData }
    }

    fn process_next_value<F, T>(
        &mut self,
        expected: Option<Tag>,
        op: F
    ) -> Result<Option<T>, DecodeError<S::Error>>
    where
        F: FnOnce(
            Tag, &mut Content<M, S>
        ) -> Result<T, DecodeError<S::Error>>
    {
        if self.source.request(1)?.slice().is_empty() {
            return Ok(None)
        }

        let (tag, constructed) = if let Some(expected) = expected {
            (
                expected,
                match expected.take_from_if(self.source)? {
                    Some(constructed) => constructed,
                    None => return Ok(None)
                }
            )
        }
        else {
            Tag::take_from(self.source)?
        };

        if tag == Tag::END_OF_VALUE {
            return Err(self.source.content_err("unexpected end of value"))
        }
        let length = Length::<M>::take_from(self.source)?;

        let start = self.source.pos();
        match length.definite() {
            Some(len) => {
                let source = LimitedSource::new(
                    self.source,
                    len
                );
                let mut content = if constructed {
                    Content::Constructed(
                        Constructed {
                            inner: ConstructedEnum::Definite(
                                DefiniteConstructed::new(source)?,
                            ),
                            start,
                        }
                    )
                }
                else {
                    Content::Primitive(Primitive::new(source))
                };
                let res = op(tag, &mut content)?;
                content.check_exhausted()?;
                Ok(Some(res))
            }
            None => {
                if constructed {
                    return Err(self.source.content_err(
                        "indefinite length primitive value"
                    ))
                }
                let source = MaybeLimitedSource::new(
                    self.source,
                    None,
                );
                let mut content = Content::Constructed(
                    Constructed {
                        inner: ConstructedEnum::Indefinite(
                            IndefiniteConstructed::new(source)?,
                        ),
                        start,
                    }
                );
                let res = op(tag, &mut content)?;
                content.check_exhausted()?;
                Ok(Some(res))
            }
        }
    }

    fn check_exhausted(&mut self) -> Result<(), DecodeError<S::Error>> {
        if self.source.request(1)?.slice().is_empty() {
            Ok(())
        }
        else {
            Err(self.source.content_err("unexpected trailing values"))
        }
    }
}


//============ Error Types ===================================================

/// A value with a certain tag was expected.
#[derive(Clone, Copy, Debug)]
struct ExpectedTag(Tag);

impl fmt::Display for ExpectedTag {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "expected tag {}", self.0)
    }
}

impl error::Error for ExpectedTag { }

impl From<ExpectedTag> for ContentError {
    fn from(err: ExpectedTag) -> Self {
        ContentError::from_boxed(Box::new(err))
    }
}


/// An integer with a certain value was expected.
#[derive(Clone, Copy, Debug)]
struct ExpectedIntValue<T>(T);

impl<T: fmt::Display> fmt::Display for ExpectedIntValue<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "expected integer value {}", self.0)
    }
}

impl<T: fmt::Debug + fmt::Display> error::Error for ExpectedIntValue<T> { }

impl<T> From<ExpectedIntValue<T>> for ContentError
where T: fmt::Display + Send + Sync + 'static {
    fn from(err: ExpectedIntValue<T>) -> Self {
        ContentError::from_boxed(Box::new(err))
    }
}

