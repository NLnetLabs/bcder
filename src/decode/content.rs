//! Parsing BER encoded values.
//!
//! This is an internal module. Its public types are re-exported by the
//! parent.

use bytes::Bytes;
use ::captured::Captured;
use ::int::{Integer, Unsigned};
use ::length::Length;
use ::mode::Mode;
use ::tag::Tag;
use super::error::Error;
use super::source::{CaptureSource, LimitedSource, Source};


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
    /// Checkes that the content has been parsed completely.
    ///
    /// Returns a malformed error if not.
    fn exhausted(self) -> Result<(), S::Err> {
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
    pub fn as_primitive(&mut self) -> Result<&mut Primitive<'a, S>, S::Err> {
        match *self {
            Content::Primitive(ref mut inner) => Ok(inner),
            Content::Constructed(_) => {
                xerr!(Err(Error::Malformed.into()))
            }
        }
    }

    /// Converts a reference into on to a constructed value or errors out.
    pub fn as_constructed(
        &mut self
    ) -> Result<&mut Constructed<'a, S>, S::Err> {
        match *self {
            Content::Primitive(_) => {
                xerr!(Err(Error::Malformed.into()))
            }
            Content::Constructed(ref mut inner) => Ok(inner),
        }
    }
}

impl<'a, S: Source + 'a> Content<'a, S> {
    /// Converts content into a `u8`.
    ///
    /// If the content is not primitive or does not contain a single BER
    /// encoded INTEGER value between 0 and 256, returns a malformed error.
    pub fn to_u8(&mut self) -> Result<u8, S::Err> {
        if let Content::Primitive(ref mut prim) = *self {
            prim.to_u8()
        }
        else {
            xerr!(Err(Error::Malformed.into()))
        }
    }

    /// Skips over the content if it contains an INTEGER of value `expected`.
    ///
    /// The content needs to be primitive and contain a validly encoded
    /// integer of value `expected` or else a malformed error will be
    /// returned.
    pub fn skip_u8_if(&mut self, expected: u8) -> Result<(), S::Err> {
        let res = self.to_u8()?;
        if res == expected {
            Ok(())
        }
        else {
            xerr!(Err(Error::Malformed.into()))
        }
    }

    /// Converts content into a `u16`.
    ///
    /// If the content is not primitive or does not contain a single BER
    /// encoded INTEGER value between 0 and 2^16-1, returns a malformed error.
    pub fn to_u16(&mut self) -> Result<u16, S::Err> {
        if let Content::Primitive(ref mut prim) = *self {
            prim.to_u16()
        }
        else {
            xerr!(Err(Error::Malformed.into()))
        }
    }

    /// Converts content into a `u32`.
    ///
    /// If the content is not primitive or does not contain a single BER
    /// encoded INTEGER value between 0 and 2^32-1, returns a malformed error.
    pub fn to_u32(&mut self) -> Result<u32, S::Err> {
        if let Content::Primitive(ref mut prim) = *self {
            prim.to_u32()
        }
        else {
            xerr!(Err(Error::Malformed.into()))
        }
    }

    /// Converts content into a `u64`.
    ///
    /// If the content is not primitive or does not contain a single BER
    /// encoded INTEGER value between 0 and 2^64-1, returns a malformed error.
    pub fn to_u64(&mut self) -> Result<u64, S::Err> {
        if let Content::Primitive(ref mut prim) = *self {
            prim.to_u64()
        }
        else {
            xerr!(Err(Error::Malformed.into()))
        }
    }

    /// Converts the content into a NULL value.
    ///
    /// If the content isn’t primitive and contains a single BER encoded
    /// NULL value (i.e., nothing), returns a malformed error.
    pub fn to_null(&mut self) -> Result<(), S::Err> {
        if let Content::Primitive(ref mut prim) = *self {
            prim.to_null()
        }
        else {
            xerr!(Err(Error::Malformed.into()))
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
}

/// # Value Management
///
impl<'a, S: 'a> Primitive<'a, S> {
    /// Creates a new primitive from the given source and mode.
    fn new(source: &'a mut LimitedSource<S>, mode: Mode) -> Self {
        Primitive { source, mode }
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


/// # High-level Decoding
///
impl<'a, S: Source + 'a> Primitive<'a, S> {
    /// Parses the primitive value as a BOOLEAN value.
    pub fn to_bool(&mut self) -> Result<bool, S::Err> {
        let res = self.take_u8()?;
        if self.mode != Mode::Ber {
            match res {
                0 => Ok(false),
                0xFF => Ok(true),
                _ => {
                    xerr!(Err(Error::Malformed.into()))
                }
            }
        }
        else {
            Ok(res != 0)
        }
    }

    /// Parses the primitive value as an INTEGER limited to a `i8`.
    pub fn to_i8(&mut self) -> Result<i8, S::Err> {
        Integer::i8_from_primitive(self)
    }

    /// Parses the primitive value as an INTEGER limited to a `i8`.
    pub fn to_i16(&mut self) -> Result<i16, S::Err> {
        Integer::i16_from_primitive(self)
    }

    /// Parses the primitive value as an INTEGER limited to a `i8`.
    pub fn to_i32(&mut self) -> Result<i32, S::Err> {
        Integer::i32_from_primitive(self)
    }

    /// Parses the primitive value as an INTEGER limited to a `i8`.
    pub fn to_i64(&mut self) -> Result<i64, S::Err> {
        Integer::i64_from_primitive(self)
    }

    /// Parses the primitive value as an INTEGER limited to a `i8`.
    pub fn to_i128(&mut self) -> Result<i128, S::Err> {
        Integer::i128_from_primitive(self)
    }

    /// Parses the primitive value as an INTEGER limited to a `u8`.
    pub fn to_u8(&mut self) -> Result<u8, S::Err> {
        Unsigned::u8_from_primitive(self)
    }

    /// Parses the primitive value as an INTEGER limited to a `u16`.
    pub fn to_u16(&mut self) -> Result<u16, S::Err> {
        Unsigned::u16_from_primitive(self)
    }

    /// Parses the primitive value as an INTEGER limited to a `u32`.
    pub fn to_u32(&mut self) -> Result<u32, S::Err> {
        Unsigned::u32_from_primitive(self)
    }

    /// Parses the primitive value as a INTEGER value limited to a `u64`.
    pub fn to_u64(&mut self) -> Result<u64, S::Err> {
        Unsigned::u64_from_primitive(self)
    }

    /// Parses the primitive value as a INTEGER value limited to a `u128`.
    pub fn to_u128(&mut self) -> Result<u64, S::Err> {
        Unsigned::u64_from_primitive(self)
    }

    /// Converts the content octets to a NULL value.
    ///
    /// Since such a value is empty, this doesn’t really do anything.
    pub fn to_null(&mut self) -> Result<(), S::Err> {
        // The rest is taken care of by the exhausted check later ...
        Ok(())
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
    /// The returned value reflects what is left of the content and therefore
    /// decreases when the primitive is advanced.
    pub fn remaining(&self) -> usize {
        self.source.limit().unwrap()
    }

    /// Skips the rest of the content.
    pub fn skip_all(&mut self) -> Result<(), S::Err> {
        self.source.skip_all()
    }

    /// Returns the remainder of the content as a `Bytes` value.
    pub fn take_all(&mut self) -> Result<Bytes, S::Err> {
        self.source.take_all()
    }

    /// Returns a bytes slice of the remainder of the content.
    pub fn slice_all(&mut self) -> Result<&[u8], S::Err> {
        let remaining = self.remaining();
        self.source.request(remaining)?;
        Ok(&self.source.slice()[..remaining])
    }

    /// Checkes whether all content has been advanced over.
    fn exhausted(self) -> Result<(), S::Err> {
        self.source.exhausted()
    }
}


/// # Support for Testing
///
impl<'a> Primitive<'a, &'a [u8]> {
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
        source: &'a [u8],
        mode: Mode,
        op: F
    ) -> Result<T, Error>
    where F: FnOnce(&mut Primitive<&[u8]>) -> Result<T, Error> {
        let mut lim = LimitedSource::new(source);
        lim.set_limit(Some(source.len()));
        let mut prim = Self::new(&mut lim, mode);
        let res = op(&mut prim)?;
        prim.exhausted()?;
        Ok(res)
    }
}


//--- Source

impl<'a, S: Source + 'a> Source for Primitive<'a, S> {
    type Err = S::Err;

    fn request(&mut self, len: usize) -> Result<usize, Self::Err> {
        self.source.request(len)
    }

    fn advance(&mut self, len: usize) -> Result<(), Self::Err> {
        self.source.advance(len)
    }

    fn slice(&self) -> &[u8] {
        self.source.slice()
    }

    fn bytes(&self, start: usize, end: usize) -> Bytes {
        self.source.bytes(start, end)
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
        Constructed { source, state, mode }
    }

    /// Decode a source as a constructed content.
    ///
    /// The function will start decoding of `source` in the given mode. It
    /// will pass a constructed content value to the closure `op` which
    /// has to process all the content and return a result or error.
    ///
    /// This function is identical to calling [`Mode::decode`].
    ///
    /// [`Mode::decode`]: ../enum.Mode.html#method.decode
    pub fn decode<F, T>(source: S, mode: Mode, op: F) -> Result<T, S::Err>
    where F: FnOnce(&mut Constructed<S>) -> Result<T, S::Err> {
        let mut source = LimitedSource::new(source);
        let mut cons = Self::new(&mut source, State::Unbounded, mode);
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

/// # Fundamental Reading
///
impl<'a, S: Source + 'a> Constructed<'a, S> {
    /// Checks whether all content has been advanced over.
    ///
    /// For a value of definite length, this is the case when the limit of the
    /// source has been reached. For indefinite values, we need to have either
    /// already read or can now read the end-of-value marker.
    fn exhausted(&mut self) -> Result<(), S::Err> {
        match self.state {
            State::Done => Ok(()),
            State::Definite => {
                self.source.exhausted()
            }
            State::Indefinite => {
                let (tag, constructed) = Tag::take_from(self.source)?;
                if tag != Tag::END_OF_VALUE {
                    xerr!(Err(Error::Malformed.into()))
                }
                else if constructed {
                    xerr!(Err(Error::Malformed.into()))
                }
                else if !Length::take_from(self.source, self.mode)?.is_zero() {
                    xerr!(Err(Error::Malformed.into()))
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
    ) -> Result<Option<T>, S::Err>
    where F: FnOnce(Tag, &mut Content<S>) -> Result<T, S::Err> {
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
                    xerr!(return Err(Error::Malformed.into()))
                }
                if !length.is_zero() {
                    xerr!(return Err(Error::Malformed.into()))
                }
                self.state = State::Done;
                return Ok(None)
            }
            else {
                xerr!(return Err(Error::Malformed.into()))
            }
        }

        match length {
            Length::Definite(len) => {
                let old_limit = self.source.limit_further(Some(len));
                let res = {
                    let mut content = if constructed {
                        // Definite length constructed values are not allowed
                        // in CER.
                        if self.mode == Mode::Cer {
                            xerr!(return Err(Error::Malformed.into()))
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
                if !constructed {
                    xerr!(return Err(Error::Malformed.into()))
                }
                else if self.mode == Mode::Der {
                    xerr!(return Err(Error::Malformed.into()))
                }
                let mut content = Content::Constructed(
                    Constructed::new(self.source, State::Indefinite, self.mode)
                );
                let res = op(tag, &mut content)?;
                content.exhausted()?;
                Ok(Some(res))
            }
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
    pub fn take_value<F, T>(&mut self, op: F) -> Result<T, S::Err>
    where F: FnOnce(Tag, &mut Content<S>) -> Result<T, S::Err> {
        match self.process_next_value(None, op)? {
            Some(res) => Ok(res),
            None => {
                xerr!(Err(Error::Malformed.into()))
            }
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
    pub fn take_opt_value<F, T>(&mut self, op: F) -> Result<Option<T>, S::Err>
    where F: FnOnce(Tag, &mut Content<S>) -> Result<T, S::Err> {
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
    ) -> Result<T, S::Err>
    where F: FnOnce(&mut Content<S>) -> Result<T, S::Err> {
        let res = self.process_next_value(Some(expected), |_, content| {
            op(content)
        })?;
        match res {
            Some(res) => Ok(res),
            None => {
                xerr!(Err(Error::Malformed.into()))
            }
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
    ) -> Result<Option<T>, S::Err>
    where F: FnOnce(&mut Content<S>) -> Result<T, S::Err> {
        self.process_next_value(Some(expected), |_, content| op(content))
    }

    /// Process a constructed value.
    ///
    /// If the next value is a constructed value, its tag and content are
    /// being given to the closure `op` which has to process it completely.
    /// If it succeeds, its return value is returned.
    ///
    /// If the next value is not a constructed value or there is no next
    /// value or if the closure doesn’t process the next value completely,
    /// a malformed error is returned. An error is also returned if the
    /// closure returns one or if accessing the underlying source fails.
    pub fn take_constructed<F, T>(&mut self, op: F) -> Result<T, S::Err>
    where F: FnOnce(Tag, &mut Constructed<S>) -> Result<T, S::Err> {
        match self.take_opt_constructed(op)? {
            Some(res) => Ok(res),
            None => {
                xerr!(Err(Error::Malformed.into()))
            }
        }
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
    ) -> Result<Option<T>, S::Err>
    where F: FnOnce(Tag, &mut Constructed<S>) -> Result<T, S::Err> {
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
        op: F
    ) -> Result<T, S::Err>
    where F: FnOnce(&mut Constructed<S>) -> Result<T, S::Err> {
        match self.take_opt_constructed_if(expected, op)? {
            Some(res) => Ok(res),
            None => {
                xerr!(Err(Error::Malformed.into()))
            }
        }
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
        op: F
    ) -> Result<Option<T>, S::Err>
    where F: FnOnce(&mut Constructed<S>) -> Result<T, S::Err> {
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
    pub fn take_primitive<F, T>(&mut self, op: F) -> Result<T, S::Err>
    where F: FnOnce(Tag, &mut Primitive<S>) -> Result<T, S::Err> {
        match self.take_opt_primitive(op)? {
            Some(res) => Ok(res),
            None => {
                xerr!(Err(Error::Malformed.into()))
            }
        }
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
        &mut self,
        op: F
    ) -> Result<Option<T>, S::Err>
    where F: FnOnce(Tag, &mut Primitive<S>) -> Result<T, S::Err> {
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
        &mut self,
        expected: Tag,
        op: F
    ) -> Result<T, S::Err>
    where F: FnOnce(&mut Primitive<S>) -> Result<T, S::Err> {
        match self.take_opt_primitive_if(expected, op)? {
            Some(res) => Ok(res),
            None => {
                xerr!(Err(Error::Malformed.into()))
            }
        }
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
        &mut self,
        expected: Tag,
        op: F
    ) -> Result<Option<T>, S::Err>
    where F: FnOnce(&mut Primitive<S>) -> Result<T, S::Err> {
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
    pub fn capture<F>(&mut self, op: F) -> Result<Captured, S::Err>
    where
        F: FnOnce(
            &mut Constructed<CaptureSource<LimitedSource<S>>>
        ) -> Result<(), S::Err>
    {
        let limit = self.source.limit();
        let mut source = LimitedSource::new(CaptureSource::new(self.source));
        source.set_limit(limit);
        {
            let mut constructed = Constructed::new(
                &mut source, self.state, self.mode
            );
            op(&mut constructed)?
        }
        Ok(Captured::new(source.unwrap().into_bytes(), self.mode))
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
    pub fn capture_one(&mut self) -> Result<Captured, S::Err> {
        self.capture(|cons| {
            match cons.skip_one()? {
                Some(()) => Ok(()),
                None => {
                    xerr!(Err(Error::Malformed.into()))
                }
            }
        })
    }

    /// Captures all remaining content for later processing.
    ///
    /// The method takes all remaining values from this value’s content and
    /// returns their encoded form in a `Bytes` value.
    pub fn capture_all(&mut self) -> Result<Captured, S::Err> {
        self.capture(|cons| cons.skip_all())
    }

    /// Skips over all remaining content.
    pub fn skip_all(&mut self) -> Result<(), S::Err> {
        while let Some(()) = self.skip_one()? { }
        Ok(())
    }

    /// Attempts to skip over the next value.
    ///
    /// If there is a next value, returns `Ok(Some(()))`, if the end of value
    /// has already been reached, returns `Ok(None)`.
    pub fn skip_one(&mut self) -> Result<Option<()>, S::Err> {
        self.take_opt_value(|_tag, content| {
            match *content {
                Content::Primitive(ref mut inner) => {
                    inner.skip_all()
                }
                Content::Constructed(ref mut inner) => {
                    inner.skip_all()?;
                    Ok(())
                }
            }
        })
    }
}


/// # Processing Standard Values
///
/// These methods provide short-cuts for processing fundamental values in
/// their standard form. That is, the values use their regular tag and
/// encoding.
impl<'a, S: Source + 'a> Constructed<'a, S> {
    /// Processes and returns a mandatory boolean value.
    pub fn take_bool(&mut self) -> Result<bool, S::Err> {
        self.take_primitive_if(Tag::BOOLEAN, |prim| prim.to_bool())
    }

    /// Processes and returns an optional boolean value.
    pub fn take_opt_bool(&mut self) -> Result<Option<bool>, S::Err> {
        self.take_opt_primitive_if(Tag::BOOLEAN, |prim| prim.to_bool())
    }

    /// Processes a mandatory NULL value.
    pub fn take_null(&mut self) -> Result<(), S::Err> {
        self.take_primitive_if(Tag::NULL, |_| Ok(())).map(|_| ())
    }

    /// Processes an optional NULL value.
    pub fn take_opt_null(&mut self) -> Result<(), S::Err> {
        self.take_opt_primitive_if(Tag::NULL, |_| Ok(())).map(|_| ())
    }

    /// Processes a mandatory INTEGER value of the `u8` range.
    ///
    /// If the integer value is less than 0 or greater than 255, a malformed
    /// error is returned.
    pub fn take_u8(&mut self) -> Result<u8, S::Err> {
        self.take_primitive_if(Tag::INTEGER, |prim| prim.to_u8())
    }

    /// Processes an optional INTEGER value of the `u8` range.
    ///
    /// If the integer value is less than 0 or greater than 255, a malformed
    /// error is returned.
    pub fn take_opt_u8(&mut self) -> Result<Option<u8>, S::Err> {
        self.take_opt_primitive_if(Tag::INTEGER, |prim| prim.to_u8())
    }

    /// Skips over a mandatory INTEGER if it has the given value.
    ///
    /// If the next value is an integer but of a different value, returns
    /// a malformed error.
    pub fn skip_u8_if(&mut self, expected: u8) -> Result<(), S::Err> {
        self.take_primitive_if(Tag::INTEGER, |prim| {
            let got = prim.take_u8()?;
            if got != expected {
                xerr!(Err(Error::Malformed.into()))
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
    pub fn skip_opt_u8_if(&mut self, expected: u8) -> Result<(), S::Err> {
        self.take_opt_primitive_if(Tag::INTEGER, |prim| {
            let got = prim.take_u8()?;
            if got != expected {
                xerr!(Err(Error::Malformed.into()))
            }
            else {
                Ok(())
            }
        }).map(|_| ())
    }

    /// Processes a mandatory INTEGER value of the `u16` range.
    ///
    /// If the integer value is less than 0 or greater than 65535, a malformed
    /// error is returned.
    pub fn take_u16(&mut self) -> Result<u16, S::Err> {
        self.take_primitive_if(Tag::INTEGER, |prim| prim.to_u16())
    }

    /// Processes an optional INTEGER value of the `u16` range.
    ///
    /// If the integer value is less than 0 or greater than 65535, a malformed
    /// error is returned.
    pub fn take_opt_u16(&mut self) -> Result<Option<u16>, S::Err> {
        self.take_opt_primitive_if(Tag::INTEGER, |prim| prim.to_u16())
    }

    /// Processes a mandatory INTEGER value of the `u32` range.
    ///
    /// If the integer value is less than 0 or greater than 2^32-1, a
    /// malformed error is returned.
    pub fn take_u32(&mut self) -> Result<u32, S::Err> {
        self.take_primitive_if(Tag::INTEGER, |prim| prim.to_u32())
    }

    /// Processes a optional INTEGER value of the `u32` range.
    ///
    /// If the integer value is less than 0 or greater than 2^32-1, a
    /// malformed error is returned.
    pub fn take_opt_u32(&mut self) -> Result<Option<u32>, S::Err> {
        self.take_opt_primitive_if(Tag::INTEGER, |prim| prim.to_u32())
    }

    /// Processes a mandatory INTEGER value of the `u64` range.
    ///
    /// If the integer value is less than 0 or greater than 2^64-1, a
    /// malformed error is returned.
    pub fn take_u64(&mut self) -> Result<u64, S::Err> {
        self.take_primitive_if(Tag::INTEGER, |prim| prim.to_u64())
    }

    /// Processes a optional INTEGER value of the `u64` range.
    ///
    /// If the integer value is less than 0 or greater than 2^64-1, a
    /// malformed error is returned.
    pub fn take_opt_u64(&mut self) -> Result<Option<u64>, S::Err> {
        self.take_opt_primitive_if(Tag::INTEGER, |prim| prim.to_u64())
    }

    /// Processes a mandatory SEQUENCE value.
    ///
    /// This is a shortcut for `self.take_constructed(Tag::SEQUENCE, op)`.
    pub fn take_sequence<F, T>(&mut self, op: F) -> Result<T, S::Err>
    where F: FnOnce(&mut Constructed<S>) -> Result<T, S::Err> {
        self.take_constructed_if(Tag::SEQUENCE, op)
    }

    /// Processes an optional SEQUENCE value.
    ///
    /// This is a shortcut for `self.take_opt_constructed(Tag::SEQUENCE, op)`.
    pub fn take_opt_sequence<F, T>(
        &mut self,
        op: F
    ) -> Result<Option<T>, S::Err>
    where F: FnOnce(&mut Constructed<S>) -> Result<T, S::Err> {
        self.take_opt_constructed_if(Tag::SEQUENCE, op)
    }

    /// Processes a mandatory SET value.
    ///
    /// This is a shortcut for `self.take_constructed(Tag::SET, op)`.
    pub fn take_set<F, T>(&mut self, op: F) -> Result<T, S::Err>
    where F: FnOnce(&mut Constructed<S>) -> Result<T, S::Err> {
        self.take_constructed_if(Tag::SET, op)
    }

    /// Processes an optional SET value.
    ///
    /// This is a shortcut for `self.take_opt_constructed(Tag::SET, op)`.
    pub fn take_opt_set<F, T>(&mut self, op: F) -> Result<Option<T>, S::Err>
    where F: FnOnce(&mut Constructed<S>) -> Result<T, S::Err> {
        self.take_opt_constructed_if(Tag::SET, op)
    }
}


//------------ State ---------------------------------------------------------

/// The processing state of a constructed value.
#[derive(Clone, Copy, Debug)]
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

