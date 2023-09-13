//! Parsing BER encoded values.
//!
//! This is an internal module. Its public types are re-exported by the
//! parent.

#![allow(unused_imports)]
#![allow(dead_code)]

use std::fmt;
use std::convert::Infallible;
use bytes::Bytes;
use smallvec::SmallVec;
use crate::captured::Captured;
use crate::int::{Integer, Unsigned};
use crate::length::Length;
use crate::mode::Mode;
use crate::tag::Tag;
use super::error::{ContentError, DecodeError};
use super::source::{
    CaptureSource, IntoSource, LimitedSource, Pos, SliceSource, Source,
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
pub enum Content<'a, S: 'a> {
    /// The value is a primitive value.
    Primitive(Primitive<'a, S>),

    /// The value is a constructed value.
    Constructed(Constructed<'a, S>)
}

impl<'a, S: Source + 'a> Content<'a, S> {
    /// Checks that the content has been parsed completely.
    ///
    /// Returns a malformed error if not.
    fn exhausted(self) -> Result<(), DecodeError<S::Error>> {
        match self {
            Content::Primitive(inner) => inner.exhausted(),
            Content::Constructed(mut inner) => inner.exhausted()
        }
    }

    /// Returns the encoding mode used by the value.
    pub fn mode(&self) -> Mode {
        match *self {
            Content::Primitive(ref inner) => inner.mode(),
            Content::Constructed(ref inner) => inner.mode()
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
    ) -> Result<&mut Primitive<'a, S>, DecodeError<S::Error>> {
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
    ) -> Result<&mut Constructed<'a, S>, DecodeError<S::Error>> {
        match *self {
            Content::Primitive(ref inner) => {
                Err(inner.content_err("expected constructed value"))
            }
            Content::Constructed(ref mut inner) => Ok(inner),
        }
    }

    /// Produces a content error at the current source position.
    pub fn content_err(
        &self, err: impl Into<ContentError>,
    ) -> DecodeError<S::Error> {
        match *self {
            Content::Primitive(ref inner) => inner.content_err(err),
            Content::Constructed(ref inner) => inner.content_err(err),
        }
    }
}

#[allow(clippy::wrong_self_convention)]
impl<'a, S: Source + 'a> Content<'a, S> {
    /// Converts content into a `u8`.
    ///
    /// If the content is not primitive or does not contain a single BER
    /// encoded INTEGER value between 0 and 256, returns a malformed error.
    pub fn to_u8(&mut self) -> Result<u8, DecodeError<S::Error>> {
        if let Content::Primitive(ref mut prim) = *self {
            prim.to_u8()
        }
        else {
            Err(self.content_err("expected integer (0..255)"))
        }
    }

    /// Skips over the content if it contains an INTEGER of value `expected`.
    ///
    /// The content needs to be primitive and contain a validly encoded
    /// integer of value `expected` or else a malformed error will be
    /// returned.
    pub fn skip_u8_if(
        &mut self, expected: u8,
    ) -> Result<(), DecodeError<S::Error>> {
        let res = self.to_u8()?;
        if res == expected {
            Ok(())
        }
        else {
            Err(self.content_err(ExpectedIntValue(expected)))
        }
    }

    /// Converts content into a `u16`.
    ///
    /// If the content is not primitive or does not contain a single BER
    /// encoded INTEGER value between 0 and 2^16-1, returns a malformed error.
    pub fn to_u16(&mut self) -> Result<u16, DecodeError<S::Error>> {
        if let Content::Primitive(ref mut prim) = *self {
            prim.to_u16()
        }
        else {
            Err(self.content_err("expected integer (0..65535)"))
        }
    }

    /// Converts content into a `u32`.
    ///
    /// If the content is not primitive or does not contain a single BER
    /// encoded INTEGER value between 0 and 2^32-1, returns a malformed error.
    pub fn to_u32(&mut self) -> Result<u32, DecodeError<S::Error>> {
        if let Content::Primitive(ref mut prim) = *self {
            prim.to_u32()
        }
        else {
            Err(self.content_err("expected integer (0..4294967295)"))
        }
    }

    /// Converts content into a `u64`.
    ///
    /// If the content is not primitive or does not contain a single BER
    /// encoded INTEGER value between 0 and 2^64-1, returns a malformed error.
    pub fn to_u64(&mut self) -> Result<u64, DecodeError<S::Error>> {
        if let Content::Primitive(ref mut prim) = *self {
            prim.to_u64()
        }
        else {
            Err(self.content_err("expected integer (0..2**64-1)"))
        }
    }

    /// Converts the content into a NULL value.
    ///
    /// If the content isn’t primitive and contains a single BER encoded
    /// NULL value (i.e., nothing), returns a malformed error.
    pub fn to_null(&mut self) -> Result<(), DecodeError<S::Error>> {
        if let Content::Primitive(ref mut prim) = *self {
            prim.to_null()
        }
        else {
            Err(self.content_err("expected NULL"))
        }
    }
}


//------------ Primitive -----------------------------------------------------

/// The content octets of a primitive value.
///
/// You will receive a reference to a value of this type through a closure,
/// possibly wrapped in a `Content` value. Your task will be to read out all
/// the octets of the value before returning from the closure or produce an
/// error if the value isn’t correctly encoded. If you read less octets than
/// are available, whoever called the closure will produce an error after
/// you returned. Thus, you can read as many octets as you expect and not
/// bother to check whether that was all available octets.
///
/// The most basic way to do this is through the primitive’s implementation
/// of the `Source` trait. Thus, you can gain access to some or all of the
/// octets and mark them read by advancing over them. You can safely attempt
/// to read more octets than available as that will reliably result in a 
/// malformed error.
///
/// A number of methods are available to deal with the encodings defined for
/// various types. These are prefixed by `to_` to indicate that they are
/// intended to convert the content to a certain type. They all read exactly
/// one encoded value.
///
/// The value provides access to the decoding mode via the `mode` method.
/// All methodes that decode data will honour the decoding mode and enforce
/// that data is encoded according to the mode.
pub struct Primitive<'a, S: 'a> {
    /// The underlying source limited to the length of the value.
    source: &'a mut LimitedSource<S>,

    /// The decoding mode to operate in.
    mode: Mode,

    /// The start position of the value in the source.
    start: Pos,
}

/// # Value Management
///
impl<'a, S: 'a> Primitive<'a, S> {
    /// Creates a new primitive from the given source and mode.
    fn new(source: &'a mut LimitedSource<S>, mode: Mode) -> Self
    where S: Source {
        Primitive { start: source.pos(), source, mode }
    }

    /// Returns the current decoding mode.
    ///
    /// The higher-level `to_` methods will use this mode to enforce that
    /// data is encoded correctly.
    pub fn mode(&self) -> Mode {
        self.mode
    }

    /// Sets the current decoding mode.
    pub fn set_mode(&mut self, mode: Mode) {
        self.mode = mode
    }
}

impl<'a, S: Source + 'a> Primitive<'a, S> {
    /// Produces a content error at the current source position.
    pub fn content_err(
        &self, err: impl Into<ContentError>,
    ) -> DecodeError<S::Error> {
        DecodeError::content(err, self.start)
    }
}


/// # High-level Decoding
///
#[allow(clippy::wrong_self_convention)]
impl<'a, S: Source + 'a> Primitive<'a, S> {
    /// Parses the primitive value as a BOOLEAN value.
    pub fn to_bool(&mut self) -> Result<bool, DecodeError<S::Error>> {
        let res = self.take_u8()?;
        if self.mode != Mode::Ber {
            match res {
                0 => Ok(false),
                0xFF => Ok(true),
                _ => {
                    Err(self.content_err("invalid boolean"))
                }
            }
        }
        else {
            Ok(res != 0)
        }
    }

    /// Parses the primitive value as an INTEGER limited to a `i8`.
    pub fn to_i8(&mut self) -> Result<i8, DecodeError<S::Error>> {
        Integer::i8_from_primitive(self)
    }

    /// Parses the primitive value as an INTEGER limited to a `i8`.
    pub fn to_i16(&mut self) -> Result<i16, DecodeError<S::Error>> {
        Integer::i16_from_primitive(self)
    }

    /// Parses the primitive value as an INTEGER limited to a `i8`.
    pub fn to_i32(&mut self) -> Result<i32, DecodeError<S::Error>> {
        Integer::i32_from_primitive(self)
    }

    /// Parses the primitive value as an INTEGER limited to a `i8`.
    pub fn to_i64(&mut self) -> Result<i64, DecodeError<S::Error>> {
        Integer::i64_from_primitive(self)
    }

    /// Parses the primitive value as an INTEGER limited to a `i8`.
    pub fn to_i128(&mut self) -> Result<i128, DecodeError<S::Error>> {
        Integer::i128_from_primitive(self)
    }

    /// Parses the primitive value as an INTEGER limited to a `u8`.
    pub fn to_u8(&mut self) -> Result<u8, DecodeError<S::Error>> {
        Unsigned::u8_from_primitive(self)
    }

    /// Parses the primitive value as an INTEGER limited to a `u16`.
    pub fn to_u16(&mut self) -> Result<u16, DecodeError<S::Error>> {
        Unsigned::u16_from_primitive(self)
    }

    /// Parses the primitive value as an INTEGER limited to a `u32`.
    pub fn to_u32(&mut self) -> Result<u32, DecodeError<S::Error>> {
        Unsigned::u32_from_primitive(self)
    }

    /// Parses the primitive value as a INTEGER value limited to a `u64`.
    pub fn to_u64(&mut self) -> Result<u64, DecodeError<S::Error>> {
        Unsigned::u64_from_primitive(self)
    }

    /// Parses the primitive value as a INTEGER value limited to a `u128`.
    pub fn to_u128(&mut self) -> Result<u64, DecodeError<S::Error>> {
        Unsigned::u64_from_primitive(self)
    }

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
/// For basic low-level access, `Primitive` implements the `Source` trait.
/// Because the length of the content is guaranteed to be known, it can
/// provide a few additional methods. Note that these may still fail because
/// the underlying source doesn’t guarantee that as many octets are actually
/// available.
impl<'a, S: Source + 'a> Primitive<'a, S> {
    /// Returns the number of remaining octets.
    ///
    /// The returned value reflects what is left of the expected length of
    /// content and therefore decreases when the primitive is advanced.
    pub fn remaining(&self) -> usize {
        self.source.limit().unwrap()
    }

    /// Skips the rest of the content.
    ///
    /// Returns a malformed error if the source ends before the expected
    /// length of content.
    pub fn skip_all(&mut self) -> Result<(), DecodeError<S::Error>> {
        self.source.skip_all()
    }

    /// Returns the remainder of the content as a `Bytes` value.
    pub fn take_all(&mut self) -> Result<Bytes, DecodeError<S::Error>> {
        self.source.take_all()
    }

    /// Returns a bytes slice of the remainder of the content.
    pub fn slice_all(&mut self) -> Result<&[u8], DecodeError<S::Error>> {
        let remaining = self.remaining();
        if self.source.request(remaining)? < remaining {
            Err(self.source.content_err("unexpected end of data"))
        }
        else {
            Ok(&self.source.slice()[..remaining])
        }
    }

    /// Process a slice of the remainder of the content via a closure.
    pub fn with_slice_all<F, T, E>(
        &mut self, op: F,
    ) -> Result<T, DecodeError<S::Error>>
    where
        F: FnOnce(&[u8]) -> Result<T, E>,
        E: Into<ContentError>,
    {
        let remaining = self.remaining();
        if self.source.request(remaining)? < remaining {
            return Err(self.source.content_err("unexpected end of data"));
        }
        let res = op(&self.source.slice()[..remaining]).map_err(|err| {
            self.content_err(err)
        })?;
        self.source.advance(remaining);
        Ok(res)
    }

    /// Checkes whether all content has been advanced over.
    fn exhausted(self) -> Result<(), DecodeError<S::Error>> {
        self.source.exhausted()
    }
}


/// # Support for Testing
///
impl Primitive<'static, ()> {
    /// Decode a bytes slice via a closure.
    ///
    /// This method can be used in testing code for decoding primitive
    /// values by providing a bytes slice with the content. For instance,
    /// decoding the `to_bool` method could be tested like this:
    ///
    /// ```
    /// use bcder::Mode;
    /// use bcder::decode::Primitive;
    ///
    /// assert_eq!(
    ///     Primitive::decode_slice(
    ///         b"\x00".as_ref(), Mode::Der,
    ///         |prim| prim.to_bool()
    ///     ).unwrap(),
    ///     false
    /// )
    /// ```
    pub fn decode_slice<F, T>(
        data: &[u8],
        mode: Mode,
        op: F
    ) -> Result<T, DecodeError<Infallible>>
    where
        F: FnOnce(
            &mut Primitive<SliceSource>
        ) -> Result<T, DecodeError<Infallible>>
    {
        let mut lim = LimitedSource::new(data.into_source());
        lim.set_limit(Some(data.len()));
        let mut prim = Primitive::new(&mut lim, mode);
        let res = op(&mut prim)?;
        prim.exhausted()?;
        Ok(res)
    }
}


//--- Source

impl<'a, S: Source + 'a> Source for Primitive<'a, S> {
    type Error = S::Error;

    fn pos(&self) -> Pos {
        self.source.pos()
    }

    fn request(&mut self, len: usize) -> Result<usize, Self::Error> {
        self.source.request(len)
    }

    fn slice(&self) -> &[u8] {
        self.source.slice()
    }

    fn bytes(&self, start: usize, end: usize) -> Bytes {
        self.source.bytes(start, end)
    }

    fn advance(&mut self, len: usize) {
        self.source.advance(len)
    }
}


//------------ Constructed ---------------------------------------------------

/// The content octets of a constructed value.
///
/// You will only ever receive a mutable reference to a value of this type
/// as an argument to a closure provided to some function. The closure will
/// have to process all content of the constructed value.
///
/// Since constructed values consist of a sequence of values, the methods
/// allow you to process these values one by one. The most basic of these
/// are [`take_value`] and [`take_opt_value`] which process exactly one
/// value or up to one value. A number of convenience functions exists on
/// top of them for commonly encountered types and cases.
///
/// Because the caller of your closure checks whether all content has been
/// advanced over and raising an error of not, you only need to read as many
/// values as you expected to be present and can simply return when you think
/// you are done.
///
/// [`take_value`]: #method.take_value
/// [`take_opt_value`]: #method.take_opt_value
#[derive(Debug)]
pub struct Constructed<'a, S: 'a> {
    /// The underlying source.
    source: &'a mut LimitedSource<S>,

    /// The state we are in so we can determine the end of the content.
    state: State,

    /// The encoding mode to use.
    mode: Mode,

    /// The start position of the value in the source.
    start: Pos,
}

/// # General Management
///
impl<'a, S: Source + 'a> Constructed<'a, S> {
    /// Creates a new source from the given components.
    fn new(
        source: &'a mut LimitedSource<S>,
        state: State,
        mode: Mode
    ) -> Self {
        Constructed { start: source.pos(), source, state, mode }
    }

    /// Decode a source as constructed content.
    ///
    /// The function will start decoding of `source` in the given mode. It
    /// will pass a constructed content value to the closure `op` which
    /// has to process all the content and return a result or error.
    ///
    /// This function is identical to calling [`Mode::decode`].
    ///
    /// [`Mode::decode`]: ../enum.Mode.html#method.decode
    pub fn decode<I, F, T>(
        source: I, mode: Mode, op: F,
    ) -> Result<T, DecodeError<S::Error>>
    where
        I: IntoSource<Source = S>,
        F: FnOnce(&mut Constructed<S>) -> Result<T, DecodeError<S::Error>>
    {
        let mut source = LimitedSource::new(source.into_source());
        let mut cons = Constructed::new(&mut source, State::Unbounded, mode);
        let res = op(&mut cons)?;
        cons.exhausted()?;
        Ok(res)
    }

    /// Returns the encoding mode used by the value.
    pub fn mode(&self) -> Mode {
        self.mode
    }

    /// Sets the encoding mode to be used for the value.
    pub fn set_mode(&mut self, mode: Mode) {
        self.mode = mode
    }
}

impl<'a, S: Source + 'a> Constructed<'a, S> {
    /// Produces a content error at start of the value.
    pub fn content_err(
        &self, err: impl Into<ContentError>,
    ) -> DecodeError<S::Error> {
        DecodeError::content(err, self.start)
    }
}

/// # Fundamental Reading
///
impl<'a, S: Source + 'a> Constructed<'a, S> {
    /// Checks whether all content has been advanced over.
    ///
    /// For a value of definite length, this is the case when the limit of the
    /// source has been reached. For indefinite values, we need to have either
    /// already read or can now read the end-of-value marker.
    fn exhausted(&mut self) -> Result<(), DecodeError<S::Error>> {
        match self.state {
            State::Done => Ok(()),
            State::Definite => {
                self.source.exhausted()
            }
            State::Indefinite => {
                let (tag, constructed) = Tag::take_from(self.source)?;
                if tag != Tag::END_OF_VALUE || constructed
                    || !Length::take_from(self.source, self.mode)?.is_zero()
                {
                    Err(self.content_err("unexpected trailing values"))
                }
                else {
                    Ok(())
                }
            }
            State::Unbounded => Ok(())
        }
    }

    /// Returns whether we have already reached the end.
    ///
    /// For indefinite values, we may be at the end right now but don’t
    /// know it yet.
    fn is_exhausted(&self) -> bool {
        match self.state {
            State::Definite => {
                self.source.limit().unwrap() == 0
            }
            State::Indefinite => false,
            State::Done => true,
            State::Unbounded => false,
        }
    }

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
        F: FnOnce(Tag, &mut Content<S>) -> Result<T, DecodeError<S::Error>>
    {
        if self.is_exhausted() {
            return Ok(None)
        }
        let (tag, constructed) = if let Some(expected) = expected {
            (
                expected,
                match expected.take_from_if(self.source)? {
                    Some(compressed) => compressed,
                    None => return Ok(None)
                }
            )
        }
        else {
            Tag::take_from(self.source)?
        };
        let length = Length::take_from(self.source, self.mode)?;

        if tag == Tag::END_OF_VALUE {
            if let State::Indefinite = self.state {
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
                self.state = State::Done;
                return Ok(None)
            }
            else {
                return Err(self.source.content_err(
                    "unexpected end of value"
                ))
            }
        }

        match length {
            Length::Definite(len) => {
                if let Some(limit) = self.source.limit() {
                    if len > limit {
                        return Err(self.source.content_err(
                            "nested value with excessive length"
                        ))
                    }
                }
                let old_limit = self.source.limit_further(Some(len));
                let res = {
                    let mut content = if constructed {
                        // Definite length constructed values are not allowed
                        // in CER.
                        if self.mode == Mode::Cer {
                            return Err(self.source.content_err(
                                "definite length constructed in CER mode"
                            ))
                        }
                        Content::Constructed(
                            Constructed::new(
                                self.source, State::Definite, self.mode
                            )
                        )
                    }
                    else {
                        Content::Primitive(
                            Primitive::new(self.source, self.mode)
                        )
                    };
                    let res = op(tag, &mut content)?;
                    content.exhausted()?;
                    res
                };
                self.source.set_limit(old_limit.map(|x| x - len));
                Ok(Some(res))
            }
            Length::Indefinite => {
                if !constructed || self.mode == Mode::Der {
                    return Err(self.source.content_err(
                        "indefinite length constructed in DER mode"
                    ))
                }
                let mut content = Content::Constructed(
                    Constructed::new(
                        self.source, State::Indefinite, self.mode
                    )
                );
                let res = op(tag, &mut content)?;
                content.exhausted()?;
                Ok(Some(res))
            }
        }
    }

    /// Makes sure the next value is present.
    fn mandatory<F, T>(
        &mut self, op: F,
    ) -> Result<T, DecodeError<S::Error>>
    where
        F: FnOnce(
            &mut Constructed<S>
        ) -> Result<Option<T>, DecodeError<S::Error>>,
    {
        match op(self)? {
            Some(res) => Ok(res),
            None => Err(self.source.content_err("missing further values")),
        }
    }
}

/// # Processing Contained Values
///
/// The methods in this section each process one value of the constructed
/// value’s content.
impl<'a, S: Source + 'a> Constructed<'a, S> {
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
        F: FnOnce(Tag, &mut Content<S>) -> Result<T, DecodeError<S::Error>>,
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
        F: FnOnce(Tag, &mut Content<S>) -> Result<T, DecodeError<S::Error>>,
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
    where F: FnOnce(&mut Content<S>) -> Result<T, DecodeError<S::Error>> {
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
    where F: FnOnce(&mut Content<S>) -> Result<T, DecodeError<S::Error>> {
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
            Tag, &mut Constructed<S>
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
            Tag, &mut Constructed<S>,
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
        F: FnOnce(&mut Constructed<S>) -> Result<T, DecodeError<S::Error>>,
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
        F: FnOnce(&mut Constructed<S>) -> Result<T, DecodeError<S::Error>>,
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
        F: FnOnce(Tag, &mut Primitive<S>) -> Result<T, DecodeError<S::Error>>,
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
        F: FnOnce(Tag, &mut Primitive<S>) -> Result<T, DecodeError<S::Error>>,
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
    where F: FnOnce(&mut Primitive<S>) -> Result<T, DecodeError<S::Error>> {
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
    where F: FnOnce(&mut Primitive<S>) -> Result<T, DecodeError<S::Error>> {
        self.process_next_value(Some(expected), |_, content| {
            op(content.as_primitive()?)
        })
    }

    /// Captures content for later processing
    ///
    /// The method gives a representation of the content to the closure `op`.
    /// If it succeeds, it returns whatever the closure advanced over as a
    /// [`Captured`] value.
    ///
    /// The closure may process no, one, several, or all values of this
    /// value’s content.
    ///
    /// If the closure returns an error, this error is returned.
    ///
    /// [`Captured`]: ../captures/struct.Captured.html
    pub fn capture<F>(
        &mut self, op: F,
    ) -> Result<Captured, DecodeError<S::Error>>
    where
        F: FnOnce(
            &mut Constructed<CaptureSource<LimitedSource<S>>>
        ) -> Result<(), DecodeError<S::Error>>
    {
        let limit = self.source.limit();
        let start = self.source.pos();
        let mut source = LimitedSource::new(CaptureSource::new(self.source));
        source.set_limit(limit);
        {
            let mut constructed = Constructed::new(
                &mut source, self.state, self.mode
            );
            op(&mut constructed)?;
            self.state = constructed.state;
        }
        Ok(Captured::new(
            source.unwrap().into_bytes(), self.mode, start,
        ))
    }

    /// Captures one value for later processing
    ///
    /// The method takes the next value from this value’s content, whatever
    /// it its, end returns its encoded form as a [`Captured`] value.
    ///
    /// If there is no next value, a malformed error is returned. If access
    /// to the underlying source fails, an appropriate error is returned.
    ///
    /// [`Captured`]: ../captures/struct.Captured.html
    pub fn capture_one(&mut self) -> Result<Captured, DecodeError<S::Error>> {
        self.capture(|cons| cons.mandatory(|cons| cons.skip_one()))
    }

    /// Captures all remaining content for later processing.
    ///
    /// The method takes all remaining values from this value’s content and
    /// returns their encoded form in a `Bytes` value.
    pub fn capture_all(
        &mut self
    ) -> Result<Captured, DecodeError<S::Error>> {
        self.capture(|cons| cons.skip_all())
    }

    /// Skips over content.
    pub fn skip_opt<F>(
        &mut self, mut op: F,
    ) -> Result<Option<()>, DecodeError<S::Error>>
    where F: FnMut(Tag, bool, usize) -> Result<(), ContentError> {
        // If we already know we are at the end of the value, we can return.
        if self.is_exhausted() {
            return Ok(None)
        }

        // The stack for unrolling the recursion. For each level, we keep the
        // limit the source should be set to when the value ends. For
        // indefinite values, we keep `None`.
        let mut stack = SmallVec::<[Option<Option<usize>>; 4]>::new();

        loop {
            // Get a the ‘header’ of a value.
            let (tag, constructed) = Tag::take_from(self.source)?;
            let length = Length::take_from(self.source, self.mode)?;

            if !constructed {
                if tag == Tag::END_OF_VALUE {
                    if length != Length::Definite(0) {
                        return Err(self.content_err("non-empty end of value"))
                    }

                    // End-of-value: The top of the stack needs to be an
                    // indefinite value for it to be allowed. If it is, pop
                    // that value off the stack and continue. The limit is
                    // still that from the value one level above.
                    match stack.pop() {
                        Some(None) => { }
                        None => {
                            // We read end-of-value as the very first value.
                            // This can only happen if the outer value is
                            // an indefinite value. If so, change state and
                            // return.
                            if self.state == State::Indefinite {
                                self.state = State::Done;
                                return Ok(None)
                            }
                            else {
                                return Err(self.content_err(
                                    "invalid nested values"
                                ))
                            }
                        }
                        _ => {
                            return Err(self.content_err(
                                "invalid nested values"
                            ))
                        }
                    }
                }
                else {
                    // Primitive value. Check for the length to be definite,
                    // check that the caller likes it, then try to read over
                    // it.
                    if let Length::Definite(len) = length {
                        if let Err(err) = op(tag, constructed, stack.len()) {
                            return Err(self.content_err(err));
                        }
                        if self.source.request(len)? < len {
                            return Err(self.content_err(
                                "short primitive value"
                            ))
                        }
                        self.source.advance(len);
                    }
                    else {
                        return Err(self.content_err(
                            "primitive value with indefinite length"
                        ))
                    }
                }
            }
            else if let Length::Definite(len) = length {
                // Definite constructed value. First check if the caller
                // likes it. Check that there is enough limit left for the
                // value. If so, push the limit at the end of the value to
                // the stack, update the limit to our length, and continue.
                if let Err(err) = op(tag, constructed, stack.len()) {
                    return Err(self.content_err(err));
                }
                stack.push(Some(match self.source.limit() {
                    Some(limit) => {
                        match limit.checked_sub(len) {
                            Some(len) => Some(len),
                            None => {
                                return Err(self.content_err(
                                    "invalid nested values"
                                ));
                            }
                        }
                    }
                    None => None,
                }));
                self.source.set_limit(Some(len));
            }
            else {
                // Indefinite constructed value. Simply push a `None` to the
                // stack, if the caller likes it.
                if let Err(err) = op(tag, constructed, stack.len()) {
                    return Err(self.content_err(err));
                }
                stack.push(None);
                continue;
            }

            // Now we need to check if we have reached the end of a
            // constructed value. This happens if the limit of the
            // source reaches 0. Since the ends of several stacked values
            // can align, we need to loop here. Also, if we run out of
            // stack, we are done.
            loop {
                if stack.is_empty() {
                    return Ok(Some(()))
                }
                else if self.source.limit() == Some(0) {
                    match stack.pop() {
                        Some(Some(limit)) => {
                            self.source.set_limit(limit)
                        }
                        Some(None) => {
                            // We need a End-of-value, so running out of
                            // data is an error.
                            return Err(self.content_err("
                                missing further values"
                            ))
                        }
                        None => unreachable!(),
                    }
                }
                else {
                    break;
                }
            }

        }
    }

    pub fn skip<F>(&mut self, op: F) -> Result<(), DecodeError<S::Error>>
    where F: FnMut(Tag, bool, usize) -> Result<(), ContentError> {
        self.mandatory(|cons| cons.skip_opt(op))
    }

    /// Skips over all remaining content.
    pub fn skip_all(&mut self) -> Result<(), DecodeError<S::Error>> {
        while let Some(()) = self.skip_one()? { }
        Ok(())
    }

    /// Attempts to skip over the next value.
    ///
    /// If there is a next value, returns `Ok(Some(()))`, if the end of value
    /// has already been reached, returns `Ok(None)`.
    pub fn skip_one(&mut self) -> Result<Option<()>, DecodeError<S::Error>> {
        if self.is_exhausted() {
            Ok(None)
        }
        else {
            self.skip(|_, _, _| Ok(()))?;
            Ok(Some(()))
        }
    }
}


/// # Processing Standard Values
///
/// These methods provide short-cuts for processing fundamental values in
/// their standard form. That is, the values use their regular tag and
/// encoding.
impl<'a, S: Source + 'a> Constructed<'a, S> {
    /// Processes and returns a mandatory boolean value.
    pub fn take_bool(&mut self) -> Result<bool, DecodeError<S::Error>> {
        self.take_primitive_if(Tag::BOOLEAN, |prim| prim.to_bool())
    }

    /// Processes and returns an optional boolean value.
    pub fn take_opt_bool(
        &mut self,
    ) -> Result<Option<bool>, DecodeError<S::Error>> {
        self.take_opt_primitive_if(Tag::BOOLEAN, |prim| prim.to_bool())
    }

    /// Processes a mandatory NULL value.
    pub fn take_null(&mut self) -> Result<(), DecodeError<S::Error>> {
        self.take_primitive_if(Tag::NULL, |_| Ok(())).map(|_| ())
    }

    /// Processes an optional NULL value.
    pub fn take_opt_null(&mut self) -> Result<(), DecodeError<S::Error>> {
        self.take_opt_primitive_if(Tag::NULL, |_| Ok(())).map(|_| ())
    }

    /// Processes a mandatory INTEGER value of the `u8` range.
    ///
    /// If the integer value is less than 0 or greater than 255, a malformed
    /// error is returned.
    pub fn take_u8(&mut self) -> Result<u8, DecodeError<S::Error>> {
        self.take_primitive_if(Tag::INTEGER, |prim| prim.to_u8())
    }

    /// Processes an optional INTEGER value of the `u8` range.
    ///
    /// If the integer value is less than 0 or greater than 255, a malformed
    /// error is returned.
    pub fn take_opt_u8(
        &mut self,
    ) -> Result<Option<u8>, DecodeError<S::Error>> {
        self.take_opt_primitive_if(Tag::INTEGER, |prim| prim.to_u8())
    }

    /// Skips over a mandatory INTEGER if it has the given value.
    ///
    /// If the next value is an integer but of a different value, returns
    /// a malformed error.
    pub fn skip_u8_if(
        &mut self, expected: u8,
    ) -> Result<(), DecodeError<S::Error>> {
        self.take_primitive_if(Tag::INTEGER, |prim| {
            let got = prim.take_u8()?;
            if got != expected {
                Err(prim.content_err(ExpectedIntValue(expected)))
            }
            else {
                Ok(())
            }
        })
    }

    /// Skips over an optional INTEGER if it has the given value.
    ///
    /// If the next value is an integer but of a different value, returns
    /// a malformed error.
    pub fn skip_opt_u8_if(
        &mut self, expected: u8,
    ) -> Result<(), DecodeError<S::Error>> {
        self.take_opt_primitive_if(Tag::INTEGER, |prim| {
            let got = prim.take_u8()?;
            if got != expected {
                Err(prim.content_err(ExpectedIntValue(expected)))
            }
            else {
                Ok(())
            }
        }).map(|_| ())
    }

    /// Processes a mandatory INTEGER value of the `u16` range.
    ///
    /// If the integer value is less than 0 or greater than 65535, a
    /// malformed error is returned.
    pub fn take_u16(&mut self) -> Result<u16, DecodeError<S::Error>> {
        self.take_primitive_if(Tag::INTEGER, |prim| prim.to_u16())
    }

    /// Processes an optional INTEGER value of the `u16` range.
    ///
    /// If the integer value is less than 0 or greater than 65535, a
    /// malformed error is returned.
    pub fn take_opt_u16(
        &mut self,
    ) -> Result<Option<u16>, DecodeError<S::Error>> {
        self.take_opt_primitive_if(Tag::INTEGER, |prim| prim.to_u16())
    }

    /// Processes a mandatory INTEGER value of the `u32` range.
    ///
    /// If the integer value is less than 0 or greater than 2^32-1, a
    /// malformed error is returned.
    pub fn take_u32(&mut self) -> Result<u32, DecodeError<S::Error>> {
        self.take_primitive_if(Tag::INTEGER, |prim| prim.to_u32())
    }

    /// Processes a optional INTEGER value of the `u32` range.
    ///
    /// If the integer value is less than 0 or greater than 2^32-1, a
    /// malformed error is returned.
    pub fn take_opt_u32(
        &mut self,
    ) -> Result<Option<u32>, DecodeError<S::Error>> {
        self.take_opt_primitive_if(Tag::INTEGER, |prim| prim.to_u32())
    }

    /// Processes a mandatory INTEGER value of the `u64` range.
    ///
    /// If the integer value is less than 0 or greater than 2^64-1, a
    /// malformed error is returned.
    pub fn take_u64(&mut self) -> Result<u64, DecodeError<S::Error>> {
        self.take_primitive_if(Tag::INTEGER, |prim| prim.to_u64())
    }

    /// Processes a optional INTEGER value of the `u64` range.
    ///
    /// If the integer value is less than 0 or greater than 2^64-1, a
    /// malformed error is returned.
    pub fn take_opt_u64(
        &mut self,
    ) -> Result<Option<u64>, DecodeError<S::Error>> {
        self.take_opt_primitive_if(Tag::INTEGER, |prim| prim.to_u64())
    }

    /// Processes a mandatory SEQUENCE value.
    ///
    /// This is a shortcut for `self.take_constructed(Tag::SEQUENCE, op)`.
    pub fn take_sequence<F, T>(
        &mut self, op: F,
    ) -> Result<T, DecodeError<S::Error>>
    where F: FnOnce(&mut Constructed<S>) -> Result<T, DecodeError<S::Error>> {
        self.take_constructed_if(Tag::SEQUENCE, op)
    }

    /// Processes an optional SEQUENCE value.
    ///
    /// This is a shortcut for
    /// `self.take_opt_constructed(Tag::SEQUENCE, op)`.
    pub fn take_opt_sequence<F, T>(
        &mut self, op: F,
    ) -> Result<Option<T>, DecodeError<S::Error>>
    where F: FnOnce(&mut Constructed<S>) -> Result<T, DecodeError<S::Error>> {
        self.take_opt_constructed_if(Tag::SEQUENCE, op)
    }

    /// Processes a mandatory SET value.
    ///
    /// This is a shortcut for `self.take_constructed(Tag::SET, op)`.
    pub fn take_set<F, T>(
        &mut self, op: F,
    ) -> Result<T, DecodeError<S::Error>>
    where F: FnOnce(&mut Constructed<S>) -> Result<T, DecodeError<S::Error>> {
        self.take_constructed_if(Tag::SET, op)
    }

    /// Processes an optional SET value.
    ///
    /// This is a shortcut for `self.take_opt_constructed(Tag::SET, op)`.
    pub fn take_opt_set<F, T>(
        &mut self, op: F
    ) -> Result<Option<T>, DecodeError<S::Error>>
    where F: FnOnce(&mut Constructed<S>) -> Result<T, DecodeError<S::Error>> {
        self.take_opt_constructed_if(Tag::SET, op)
    }
}


//------------ State ---------------------------------------------------------

/// The processing state of a constructed value.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum State {
    /// We are reading until the end of the reader.
    Definite,

    /// Indefinite value, we haven’t reached the end yet.
    Indefinite,

    /// End of indefinite value reached.
    Done,

    /// Unbounded value: read as far as we get.
    Unbounded,
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

impl<T> From<ExpectedIntValue<T>> for ContentError
where T: fmt::Display + Send + Sync + 'static {
    fn from(err: ExpectedIntValue<T>) -> Self {
        ContentError::from_boxed(Box::new(err))
    }
}
 

//============ Tests =========================================================

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn constructed_skip() {
        // Two primitives.
        Constructed::decode(
            b"\x02\x01\x00\x02\x01\x00".into_source(), Mode::Ber, |cons| {
                cons.skip(|_, _, _| Ok(())).unwrap();
                cons.skip(|_, _, _| Ok(())).unwrap();
                Ok(())
            }
        ).unwrap();

        // One definite constructed with two primitives, then one primitive
        Constructed::decode(
            b"\x30\x06\x02\x01\x00\x02\x01\x00\x02\x01\x00".into_source(),
            Mode::Ber,
            |cons| {
                cons.skip(|_, _, _| Ok(())).unwrap();
                cons.skip(|_, _, _| Ok(())).unwrap();
                Ok(())
            }
        ).unwrap();

        // Two nested definite constructeds with two primitives, then one
        // primitive.
        Constructed::decode(
            b"\x30\x08\
            \x30\x06\
            \x02\x01\x00\x02\x01\x00\
            \x02\x01\x00".into_source(),
            Mode::Ber,
            |cons| {
                cons.skip(|_, _, _| Ok(())).unwrap();
                cons.skip(|_, _, _| Ok(())).unwrap();
                Ok(())
            }
        ).unwrap();

        // One definite constructed with one indefinite with two primitives.
        Constructed::decode(
            b"\x30\x0A\
            \x30\x80\
            \x02\x01\x00\x02\x01\x00\
            \0\0".into_source(),
            Mode::Ber,
            |cons| {
                cons.skip(|_, _, _| Ok(())).unwrap();
                Ok(())
            }
        ).unwrap();
    }
}


