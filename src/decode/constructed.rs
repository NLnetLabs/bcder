//! Decoding constructed values.
//!
//! This is a private module. The relevant items are re-exported by the
//! parent.
//
//  XXX TODO: Change reading of end-of-contents to (a) error out in
//            `read_ident` already in definite length values and (b) read
//            the length as a single zero (i.e., as the short form).

use std::{cmp, error, io};
use std::io::Read;
use std::marker::PhantomData;
use crate::encode;
use crate::captured::Captured;
use crate::ident::{Ident, Tag};
use crate::length::{Length, LengthOctets};
use crate::mode::Mode;
use super::error::Error;
use super::nested::{NestedItem, NestedIter};
use super::primitive::{FromPrimitive, Primitive};
use super::source::{CaptureSource, Source, SourceError};
use super::value::Value;


//------------ Data ----------------------------------------------------------

/// Encoded data.
///
/// This type wraps an IO reader and allows decoding it as a sequence of
/// encoded values.
pub struct Data<M, R> {
    source: Source<R>,
    marker: PhantomData<M>,
}

impl<M, R> Data<M, R> {
    /// Creates a new data value for the given reader.
    pub fn new(reader: R) -> Self {
        Self {
            source: Source::new(reader),
            marker: PhantomData
        }
    }

    /// Returns the current position in the source.
    pub fn pos(&self) -> Length {
        self.source.pos()
    }
}

impl<M: Mode, R: io::Read> Data<M, R> {
    /// Starts decoding the next mandatory value.
    ///
    /// Returns an error if there are no more values available.
    pub fn next_value(&mut self) -> Result<Value<M, R>, Error> {
        let (ident, start) = self.read_ident()?;
        self.read_value(ident, start)
    }

    /// Starts decoding an optional next value.
    ///
    /// Returns an error if error if it encounters any other
    /// tag or the end of the content.
    pub fn next_value_with(
        &mut self, expected: Tag,
    ) -> Result<Value<M, R>, Error> {
        let (ident, start) = self.read_ident()?;
        if ident.tag() != expected {
            return Err(Error::content(
                format!("expected value with tag {expected}"),
                start
            ))
        }
        self.read_value(ident, start)
    }

    /// Starts decoding the next mandatory constructed value.
    ///
    /// Returns an error if the next value is not a constructed value or if
    /// there is no next value.
    pub fn next_constructed(
        &mut self
    ) -> Result<Constructed<M, R>, Error> {
        let (ident, start) = self.read_ident()?;
        if !ident.is_constructed() {
            return Err(Error::content(
                "expected constructed value", start
            ))
        }
        self.read_value(ident, start)?.into_constructed()
    }

    /// Processes a constructed value with a required tag.
    ///
    /// If the next value is a constructed value with a tag equal to
    /// `expected`, returns this value’s content.
    ///
    /// If the next value is not constructed or has a different tag, or if
    /// the end of the value has been reached, an error is returned.
    pub fn next_constructed_with(
        &mut self,
        expected: Tag,
    ) -> Result<Constructed<M, R>, Error> {
        let (ident, start) = self.read_ident()?;
        if ident.tag() != expected {
            return Err(Error::content(
                format!("expected value with tag {expected}"),
                start
            ))
        }
        if !ident.is_constructed() {
            return Err(Error::content(
                "expected constructed value", start
            ))
        }
        self.read_value(ident, start)?.into_constructed()
    }

    /// Decodes a reader as a single constructed value.
    ///
    /// The function will start decoding of `reader`. It will pass a
    /// constructed content value to the closure `op` which has to process
    /// all the content and return a result or error.
    pub fn process<F, T>(reader: R, op: F) -> Result<T, Error>
    where
        R: io::Read,
        M: Mode,
        F: FnOnce(&mut Constructed<M, R>) -> Result<T, Error>
    {
        let mut data = Self::new(reader);
        let res = op(&mut data.next_constructed()?)?;
        data.check_exhausted()?;
        Ok(res)
    }

    /// Checks that the underlying reader has reached its end.
    pub fn check_exhausted(&mut self) -> Result<(), Error> {
        // By trying to read a single byte, we can both check that we are
        // actually at the end of the reader and that the source’s status
        // is still ok.
        let mut buf = [0u8];
        let pos = self.source.pos();
        match self.source.read_exact(&mut buf) {
            Ok(()) => {
                Err(Error::content("trailing data", pos))
            }
            Err(err) if err.kind() == io::ErrorKind::UnexpectedEof => {
                Ok(())
            }
            Err(err) => Err(Error::from_io(err, pos))
        }
    }
}

impl<M: Mode, R: io::Read> Data<M, R> {
    /// Reads the next identifier octets from the source.
    ///
    /// Returns an error if the source has reached its end.
    fn read_ident(&mut self) -> Result<(Ident, Length), Error> {
        let start = self.pos();
        match Ident::read_opt(&mut self.source) {
            Ok(Some(ident)) => Ok((ident, start)),
            Ok(None) => {
                Err(Error::content(
                    "expected further values", self.pos()
                ))
            }
            Err(err) => Err(Error::content(err, self.pos())),
        }
    }

    /// Prepares the next value.
    ///
    /// Reads the length octets and then uses that and `ident` to prepare and
    /// return the next value.
    fn read_value(
        &mut self, ident: Ident, start: Length
    ) -> Result<Value<M, R>, Error> {
        self.read_value_io(ident, start).map_err(|err| {
            Error::content(err, start)
        })
    }

    /// Prepares the next value.
    ///
    /// This is the same as `read_value` but produces a raw `io::Error`, so
    /// we can use the question mark operator.
    fn read_value_io(
        &mut self, ident: Ident, start: Length
    ) -> Result<Value<M, R>, io::Error> {
        match LengthOctets::read::<M>(&mut self.source)?.definite() {
            Some(length) => {
                let limit = self.source.pos() + length;
                if ident.is_constructed() {
                    Ok(Value::Constructed(
                        Constructed::new(
                            ident.tag(),
                            start,
                            ConstructedEnum::Definite(
                                DefiniteConstructed::new::<M>(
                                    &mut self.source, limit
                                )?
                            ),
                        )
                    ))
                }
                else {
                    Ok(Value::Primitive(Primitive::new(
                        &mut self.source, limit, ident.tag(), start
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
                Ok(Value::Constructed(
                    Constructed::new(
                        ident.tag(),
                        start,
                        ConstructedEnum::Indefinite(
                            IndefiniteConstructed::new::<M>(
                                &mut self.source, None
                            )?
                        ),
                    )
                ))
            }
        }
    }
}


//------------ Constructed ---------------------------------------------------

/// A constructed value.
///
/// Constructed values contain other values as their content. When decoding
/// a constructed value, you need to decode all of these contained values in
/// turn. A number of methods are provided that each allow processing one
/// contained value and should be called repeatedly until the end is reached.
/// The most basic of those are [`decode_value`][Self::decode_value], which
/// expects there to be a next value and otherwise errors out, and
/// [`decode_opt_value`][Self::decode_opt_value] which is okay with reaching
/// the end of the value.
pub struct Constructed<'a, M: Mode, R: io::Read + 'a> {
    /// The tag of the value.
    tag: Tag,

    /// The position in the source of the start of the value.
    start: Length,

    /// Access to the content.
    ///
    /// There are two types of constructed values -- definite length
    /// and indefinite length -- which need to be processed differently, so
    /// this is an enum.
    inner: ConstructedEnum<'a, R>,

    /// The identifer and startof the last value if we didn’t process it.
    ///
    /// Some methods allow to only process a value if it fullfills certain
    /// criteria. If they don’t like it, they park the identifier octets and
    /// start position of the value here.
    stored_ident: Option<(Ident, Length)>,

    /// A place for the mode.
    marker: PhantomData<M>,
}

/// The type of constructed value.
enum ConstructedEnum<'a, R: io::Read + 'a> {
    /// A definite-length constructed value.
    Definite(DefiniteConstructed<'a, R>),

    /// An indefinite-length constructed value.
    Indefinite(IndefiniteConstructed<'a, R>),
}

impl<'a, M: Mode, R: io::Read + 'a> Constructed<'a, M, R> {
    /// Creates a new constructed value from its components.
    fn new(
        tag: Tag, start: Length, inner: ConstructedEnum<'a, R>
    ) -> Self {
        Self {
            tag, start, inner,
            stored_ident: None,
            marker: PhantomData,
        }
    }

    /// Converts the value into on using a different encoding mode.
    pub fn switch_mode<N: Mode>(self) -> Constructed<'a, N, R> {
        Constructed {
            tag: self.tag,
            start: self.start,
            inner: self.inner,
            stored_ident: self.stored_ident,
            marker: PhantomData,
        }
    }

    /// Returns the tag of the value.
    pub fn tag(&self) -> Tag {
        self.tag
    }

    /// Returns the start position of the value in the source.
    pub fn start(&self) -> Length {
        self.start
    }

    /// Returns the current read position in the source.
    pub fn pos(&self) -> Length {
        match &self.inner {
            ConstructedEnum::Definite(inner) => inner.source.pos(),
            ConstructedEnum::Indefinite(inner) => inner.source.pos(),
        }
    }

    /// Produces an error at the start of the value.
    pub fn err_at_start(
        &self, err: impl Into<Box<dyn error::Error + Send + Sync>>,
    ) -> Error {
        Error::content(err, self.start)
    }

    /// Produces an error at the current position.
    pub fn err_at_current(
        &self, err: impl Into<Box<dyn error::Error + Send + Sync>>,
    ) -> Error {
        Error::content(err, self.pos())
    }
}

/// # Fundamental reading
///
/// The private methods in this section are used as building blocks for the
/// public methods.
///
/// Reading is broken up into two steps: First you get the identifier octets
/// of the next value via [`read_ident`][Self::read_ident] or
/// [`read_opt_ident`][Self::read_opt_ident] so you can check if you want to
/// process that value.
///
/// If you like do not want to process the value, you retain the identifer
/// octets for later via [`keep_ident`][Self::keep_ident].
///
/// If you do want to process the value, [`read_value`][Self::read_value]
/// produces a [`Value`] for it.
impl<'a, M: Mode, R: io::Read + 'a> Constructed<'a, M, R> {
    /// Returns the identifier octets and start position of the next value.
    ///
    /// Returns `Ok(None)` if the end of the value was reached.
    fn read_opt_ident(
        &mut self
    ) -> Result<Option<(Ident, Length)>, Error> {
        if let Some(ident) = self.stored_ident.take() {
            return Ok(Some(ident))
        }
        let pos = self.pos();
        let ident = match &mut self.inner {
            ConstructedEnum::Definite(inner) => inner.read_ident(),
            ConstructedEnum::Indefinite(inner) => inner.read_ident::<M>(),
        };
        match ident {
            Ok(None) => Ok(None),
            Ok(Some(ident)) => Ok(Some((ident, pos))),
            Err(err) => Err(Error::content(err, pos))
        }
    }

    /// Returns the identifier octets and start position of the next value.
    ///
    /// Returns an error if the end of the value was reached.
    fn read_ident(&mut self) -> Result<(Ident, Length), Error> {
        match self.read_opt_ident() {
            Ok(Some(some)) => Ok(some),
            Ok(None) => {
                Err(Error::content(
                    "expected further values", self.pos()
                ))
            }
            Err(err) => Err(err),
        }
    }

    /// Stores the identifier octets and start position.
    ///
    /// This method must be called when the values retrieved via `read_ident`
    /// aren’t actually used.
    fn keep_ident(&mut self, ident: Ident, start: Length) {
        self.stored_ident = Some((ident, start))
    }

    /// Creates the content of the next value.
    fn read_value(
        &mut self, ident: Ident, start: Length
    ) -> Result<Value<M, R>, Error> {
        match &mut self.inner {
            ConstructedEnum::Definite(inner) => {
                inner.read_value(ident, start)
            }
            ConstructedEnum::Indefinite(inner) => {
                inner.read_value(ident, start)
            }
        }.map_err(|err| Error::content(err, start))
    }

    /// Checks that the source is still fine.
    fn check_source_status(&mut self) -> Result<(), Error> {
        match &mut self.inner {
            ConstructedEnum::Definite(inner) => inner.source.check_status(),
            ConstructedEnum::Indefinite(inner) => inner.source.check_status(),
        }.map_err(|err| Error::from_io(err, self.pos()))
    }
}

/// # Decoding the complete constructed value
impl<'a, M: Mode, R: io::Read + 'a> Constructed<'a, M, R> {
    /// Decodes the constructed value as a single nested value.
    ///
    /// TODO: explain!
    pub fn process_nested<F>(
        self,
        mut op: F,
    ) -> Result<(), Error>
    where
        F: FnMut(NestedItem<M, R>) -> Result<(), Error>,
    {
        let mut iter = NestedIter::new(self);
        while let Some(item) = iter.next_item()? {
            op(item)?;
        }
        Ok(())
    }
}

/// # Decoding contained values
///
/// The following methods, all prefixed by `decode_` process values by
/// returning owned objects to the caller. These objects need to be dropped
/// before progressing to the next value. Because of this, the `process_`
/// methods using closures may be more convenient for processing sequences
/// of values.
impl<'a, M: Mode, R: io::Read + 'a> Constructed<'a, M, R> {
    /// Starts decoding the next mandatory value.
    ///
    /// Returns an error if there are no more values available.
    pub fn next_value(&mut self) -> Result<Value<M, R>, Error> {
        let (ident, start) = self.read_ident()?;
        self.read_value(ident, start)
    }

    /// Starts decoding an optional next value.
    ///
    /// If there are no more values, returns `Ok(None)`. Otherwise returns
    /// the content of the value.
    pub fn next_opt(
        &mut self
    ) -> Result<Option<Value<M, R>>, Error> {
        let Some((ident, start)) = self.read_opt_ident()? else {
            return Ok(None)
        };
        self.read_value(ident, start).map(Some)
    }

    /// Starts decoding a mandatory next value with a given tag.
    ///
    /// Returns an error if there is no next value or if there is a next value
    /// with a tag other than `expected`.
    pub fn next_with(
        &mut self, expected: Tag,
    ) -> Result<Value<M, R>, Error> {
        let (ident, start) = self.read_ident()?;
        if ident.tag() != expected {
            return Err(Error::content(
                format!("expected value with tag {expected}"),
                start
            ))
        }
        self.read_value(ident, start)
    }

    /// Starts decoding an optional next value with a given tag.
    ///
    /// Returns the value if it has the tag `expected`.
    ///
    /// Returns `Ok(None)` if the next value has a different tag or if the
    /// end of the content has been reached.
    pub fn next_opt_with(
        &mut self, expected: Tag,
    ) -> Result<Option<Value<M, R>>, Error> {
        let Some((ident, start)) = self.read_opt_ident()? else {
            return Ok(None)
        };
        if ident.tag() != expected {
            self.keep_ident(ident, start);
            return Ok(None)
        }
        self.read_value(ident, start).map(Some)
    }

    /// Starts decoding a mandatory next constructed value.
    ///
    /// If the next value is not a constructed value or if there is no
    /// next value, returns an error.
    pub fn next_constructed(
        &mut self
    ) -> Result<Constructed<M, R>, Error> {
        let (ident, start) = self.read_ident()?;
        if !ident.is_constructed() {
            return Err(Error::content(
                "expected constructed value", start
            ))
        }
        self.read_value(ident, start)?.into_constructed()
    }

    /// Starts decoding an optional next constructed value.
    ///
    /// Returns an error if the next value is not constructed.
    ///
    /// Returns `Ok(None)` if the end of the content has been reached.
    pub fn next_opt_constructed(
        &mut self,
    ) -> Result<Option<Constructed<M, R>>, Error>
    {
        let Some((ident, start)) = self.read_opt_ident()? else {
            return Ok(None)
        };
        if !ident.is_constructed() {
            return Err(Error::content(
                "expected constructed value", start
            ))
        }
        Ok(Some(self.read_value(ident, start)?.into_constructed()?))
    }

    /// Starts decoding a mandatory next constructed value with a given tag.
    ///
    /// Returns an error if the next value is not constructed, if it has a
    /// different tag, or if the end of the content has been reached.
    pub fn next_constructed_with(
        &mut self,
        expected: Tag,
    ) -> Result<Constructed<M, R>, Error> {
        let (ident, start) = self.read_ident()?;
        if ident.tag() != expected {
            return Err(Error::content(
                format!("expected value with tag {expected}"),
                start
            ))
        }
        if !ident.is_constructed() {
            return Err(Error::content(
                "expected constructed value", start
            ))
        }
        self.read_value(ident, start)?.into_constructed()
    }

    /// Starts decoding an optional next constructed value with a given tag.
    ///
    /// Returns `Ok(None)` if the next value has a different tag or if the
    /// end of the contents has been reached.
    ///
    /// Returns an error if next value has the right tag but is not
    /// constructed.
    pub fn next_opt_constructed_with(
        &mut self,
        expected: Tag,
    ) -> Result<Option<Constructed<M, R>>, Error> {
        let Some((ident, start)) = self.read_opt_ident()? else {
            return Ok(None)
        };
        if ident.tag() != expected {
            self.keep_ident(ident, start);
            return Ok(None)
        }
        if !ident.is_constructed() {
            return Err(Error::content(
                "expected constructed value", start
            ))
        }
        Ok(Some(self.read_value(ident, start)?.into_constructed()?))
    }

    /// Starts decoding the next mandatory primitive value.
    ///
    /// If the next value is not primitive or if the end of value has been
    /// reached a error is returned.
    pub fn next_primitive(
        &mut self
    ) -> Result<Primitive<M, R>, Error> {
        let (ident, start) = self.read_ident()?;
        if ident.is_constructed() {
            return Err(Error::content(
                "expected primitive value", start
            ))
        }
        self.read_value(ident, start)?.into_primitive()
    }

    /// Starts decoding an optional primitive value.
    ///
    /// If the end of value has been reached, `Ok(None)` is returned.
    /// If the next value is not primitive, an error is returned.
    pub fn next_opt_primitive(
        &mut self
    ) -> Result<Option<Primitive<M, R>>, Error> {
        let Some((ident, start)) = self.read_opt_ident()? else {
            return Ok(None)
        };
        if ident.is_constructed() {
            return Err(Error::content(
                "expected primitive value", start
            ))
        }
        Ok(Some(self.read_value(ident, start)?.into_primitive()?))
    }

    /// Start decoding a mandatory next primitive value with the given tag.
    ///
    /// Returns an error if there is no next value, if the next value is not
    /// a primitive, if it doesn’t have the expected tag.
    pub fn next_primitive_with(
        &mut self, expected: Tag
    ) -> Result<Primitive<M, R>, Error> {
        let (ident, start) = self.read_ident()?;
        if ident.tag() != expected {
            return Err(Error::content(
                format!("expected value with tag {expected}"),
                start
            ))
        }
        if ident.is_constructed() {
            return Err(Error::content(
                "expected primitive value", start
            ))
        }
        self.read_value(ident, start)?.into_primitive()
    }

    /// Starts decoding an optional next primitive value with the given tag.
    ///
    /// If the end of this value has been reached or if the value’s tag
    /// doesn’t match, the method returns `Ok(None)`. If the value is not
    /// primitive, the method returns an error.
    pub fn next_opt_primitive_with(
        &mut self, expected: Tag
    ) -> Result<Option<Primitive<M, R>>, Error> {
        let Some((ident, start)) = self.read_opt_ident()? else {
            return Ok(None)
        };
        if ident.tag() != expected {
            self.keep_ident(ident, start);
            return Ok(None)
        }
        if ident.is_constructed() {
            return Err(Error::content(
                "expected primitive value", start
            ))
        }
        Ok(Some(self.read_value(ident, start)?.into_primitive()?))
    }
}

impl<'a, M: Mode, R: io::BufRead + 'a> Constructed<'a, M, R> {
    /// Skips the next value.
    ///
    /// The closure `op` determines whether the next value is valid. It will
    /// be called for every encountered value, which for nested constructed
    /// values can be multiple times. Each time it gets passed the tag,
    /// whether the value is constructed, and the depth starting at zero for
    /// the outermost value. It should return an error if the value cannot
    /// be accepted.
    ///
    /// The method will return `Ok(Some(()))` if it successfully skipped a
    /// value or an error if there were errors or `op` returned an error./
    pub fn skip_next<F: FnMut(Tag, bool, usize) -> Result<(), Error>>(
        &mut self, op: F
    ) -> Result<(), Error> {
        self.next_value()?.skip(op)
    }

    /// Skips over a next optional value.
    ///
    /// Returns `Ok(None)` if there are no more values. Otherwise, the
    /// closure `op` determines whether the next value is valid. It will
    /// be called for every encountered value, which for nested constructed
    /// values can be multiple times. Each time it gets passed the tag,
    /// whether the value is constructed, and the depth starting at zero for
    /// the outermost value. It should return an error if the value cannot
    /// be accepted.
    ///
    /// The method will return `Ok(Some(()))` if it successfully skipped a
    /// value or an error if there were errors or `op` returned an error.
    pub fn skip_opt_next<F: FnMut(Tag, bool, usize) -> Result<(), Error>>(
        &mut self, op: F
    ) -> Result<Option<()>, Error> {
        match self.next_opt()? {
            Some(value) => {
                value.skip(op)?;
                Ok(Some(()))
            }
            None => Ok(None)
        }
    }

    /// Skips over the next value no matter its content.
    pub fn skip_any_next(&mut self) -> Result<(), Error> {
        self.skip_next(|_, _, _| Ok(()))
    }

    /// Skips over an optional next value no matter its content.
    pub fn skip_any_opt_next(&mut self) -> Result<Option<()>, Error> {
        self.skip_opt_next(|_, _, _| Ok(()))
    }

    /// Skips over all remaining values.
    pub fn skip_all(&mut self) -> Result<(), Error> {
        while self.skip_any_opt_next()?.is_some() { }
        Ok(())
    }

    pub fn capture<F>(self, op: F) -> Result<Box<Captured<M>>, Error>
    where F: FnOnce(Constructed<M, CaptureSource<M, R>>) -> Result<(), Error> {
        match self.inner {
            ConstructedEnum::Definite(inner) => {
                Self::capture_definite(
                    self.tag, self.start, inner, self.stored_ident, op
                )
            }
            ConstructedEnum::Indefinite(inner) => {
                Self::capture_indefinite(
                    self.tag, self.start, inner, self.stored_ident, op
                )
            }
        }
    }

    fn capture_definite<F>(
        tag: Tag, start: Length, inner: DefiniteConstructed<'a, R>,
        stored_ident: Option<(Ident, Length)>,
        op: F
    ) -> Result<Box<Captured<M>>, Error>
    where F: FnOnce(Constructed<M, CaptureSource<M, R>>) -> Result<(), Error> {
        let mut target = Vec::new();
        encode::infallible(
            encode::write_header(
                &mut target, tag, true,
                inner.limit.saturating_sub(inner.source.pos())
            )
        );
        let mut source = inner.source.capture(target);
        op(
            Constructed {
                tag, start,
                inner: ConstructedEnum::Definite(
                    DefiniteConstructed {
                        source: &mut source,
                        limit: inner.limit,
                    }
                ),
                stored_ident,
                marker: PhantomData::<M>,
            }
        )?;
        source.into_reader()?.finalize()
    }

    fn capture_indefinite<F>(
        tag: Tag, start: Length, inner: IndefiniteConstructed<'a, R>,
        stored_ident: Option<(Ident, Length)>,
        op: F
    ) -> Result<Box<Captured<M>>, Error>
    where F: FnOnce(Constructed<M, CaptureSource<M, R>>) -> Result<(), Error> {
        let mut target = Vec::new();
        encode::infallible(
            encode::write_indefinite_header(&mut target, tag)
        );
        let mut source = inner.source.capture(target);
        op(
            Constructed {
                tag, start,
                inner: ConstructedEnum::Indefinite(
                    IndefiniteConstructed {
                        source: &mut source,
                        limit: inner.limit,
                        done: inner.done,
                    }
                ),
                stored_ident,
                marker: PhantomData::<M>,
            }
        )?;
        source.into_reader()?.finalize()
    }
}


/// # Processing values using closures
///
/// The following methods process values by passing them to a closure. This
/// may be convenient when processing a sequence of values. The methods also
/// check whether the value was fully processed before returning. Otherwise
/// an error would be delayed until the start of processing of the next value
/// which may be a bit confusing during debugging.
impl<'a, M: Mode, R: io::Read + 'a> Constructed<'a, M, R> {
    /// Process one value of content.
    ///
    /// The closure `op` receives the next value and must process it
    /// completely.
    ///
    /// Upon success, the method returns the closure’s return value. The
    /// method returns am error if there isn’t at least one more value
    /// available. It also returns an error if the closure returns one
    /// or if reading from the source fails.
    pub fn process_value<F, T>(&mut self, op: F) -> Result<T, Error>
    where F: FnOnce(Value<M, R>) -> Result<T, Error> {
        let (ident, start) = self.read_ident()?;
        let res = op(self.read_value(ident, start)?)?;
        self.check_source_status()?;
        Ok(res)
    }

    /// Processes an optional value.
    ///
    /// If there is at least one more value available, the closure `op` is
    /// given the value and must process it completely. If the closure
    /// succeeds, its return value is returned as ‘some’ result.
    ///
    /// If there are no more values available, the method returns `Ok(None)`.
    /// It returns an error if the closure returns one or if reading from
    /// the source fails.
    pub fn process_opt<F, T>(
        &mut self, op: F
    ) -> Result<Option<T>, Error>
    where F: FnOnce(Value<M, R>) -> Result<T, Error> {
        let Some((ident, start)) = self.read_opt_ident()? else {
            return Ok(None)
        };
        let res = op(self.read_value(ident, start)?)?;
        self.check_source_status()?;
        Ok(Some(res))
    }

    /// Processes a value if it has the given tag.
    ///
    /// The method expects that there is at least one more value and that it
    /// has the tag `expected`. If so, the value is given to the closure
    /// which has to process it completely. If the closure
    /// succeeds, its return value is returned by the method.
    ///
    /// The method will return a malformed error if it encounters any other
    /// tag or the end of the value. It will also return an error if the
    /// closure returns an error or doesn’t process the complete values, or
    /// if accessing the underlying source fails.
    pub fn process_value_with<F, T>(
        &mut self, expected: Tag, op: F
    ) -> Result<T, Error>
    where F: FnOnce(Value<M, R>) -> Result<T, Error> {
        let (ident, start) = self.read_ident()?;
        if ident.tag() != expected {
            return Err(Error::content(
                format!("expected value with tag {expected}"),
                start
            ))
        }
        let res = op(self.read_value(ident, start)?)?;
        self.check_source_status()?;
        Ok(res)
    }

    /// Optionally processes an value if it has the given tag.
    ///
    /// If the next value has the tag `expected`, it is being given to the
    /// closure which has to process it completely. If the closure
    /// succeeds, its return value is returned by the method.
    ///
    /// If the next value has a different tag or if the end of the value has
    /// been reached, the method returns `Ok(None)`.
    ///
    /// It will return an error if the closure fails or doesn’t process the
    /// complete value, or if accessing the underlying source fails.
    pub fn process_opt_with<F, T>(
        &mut self, expected: Tag, op: F
    ) -> Result<Option<T>, Error>
    where F: FnOnce(Value<M, R>) -> Result<T, Error> {
        let Some((ident, start)) = self.read_opt_ident()? else {
            return Ok(None)
        };
        if ident.tag() != expected {
            self.keep_ident(ident, start);
            return Ok(None)
        }
        let res = op(self.read_value(ident, start)?)?;
        self.check_source_status()?;
        Ok(Some(res))
    }

    /// Processes a constructed value.
    /// 
    /// Expects that there is at least one more value and that it is a
    /// constructed value. If so, the constructed value is given to the
    /// closure for processing. If the closure succeeds, its return value
    /// is returned.
    ///
    /// If the next value is not a constructed value or there is no next
    /// value or if the closure doesn’t process the next value completely,
    /// an error is returned. An error is also returned if the closure
    /// returns one or if accessing the underlying source fails.
    pub fn process_constructed<F, T>(&mut self, op: F) -> Result<T, Error>
    where F: FnOnce(Constructed<M, R>) -> Result<T, Error> {
        let (ident, start) = self.read_ident()?;
        if !ident.is_constructed() {
            return Err(Error::content(
                "expected constructed value", start
            ))
        }
        let res = op(self.read_value(ident, start)?.into_constructed()?)?;
        self.check_source_status()?;
        Ok(res)
    }

    /// Processes an optional constructed value.
    ///
    /// Expects that if there is at least one more value, the next value is
    /// a constructed value. If so, the constructed value is given to the
    /// closure for processing. If the closure succeeds, its return value
    /// is returned as ‘some.’
    ///
    /// If the end of the value has been reached, the method returns
    /// `Ok(None)`.
    ///
    /// If the next value is not a constructed value or if the closure
    /// doesn’t process the next value completely, a malformed error is
    /// returned. An error is also returned if the closure returns one or
    /// if accessing the underlying source fails.
    pub fn process_opt_constructed<F, T>(
        &mut self, op: F
    ) -> Result<Option<T>, Error>
    where F: FnOnce(Constructed<M, R>) -> Result<T, Error> {
        let Some((ident, start)) = self.read_opt_ident()? else {
            return Ok(None)
        };
        if !ident.is_constructed() {
            return Err(Error::content(
                "expected constructed value", start
            ))
        }
        let res = op(self.read_value(ident, start)?.into_constructed()?)?;
        self.check_source_status()?;
        Ok(Some(res))
    }

    /// Processes a constructed value with a required tag.
    ///
    /// Expects there to be at least one more value, that the next value has
    /// the given tag and that it is a constructed value. If so, the
    /// constructed value is given to the closure for processing. If the
    /// closure succeeds, its return value is returned.
    ///
    /// If the next value is not constructed or has a different tag, if
    /// the end of the value has been reached, or if the closure does not
    /// process the contained value’s content completely, a malformed error
    /// is returned. An error is also returned if the closure returns one or
    /// if accessing the underlying source fails.
    pub fn process_constructed_with<F, T>(
        &mut self, expected: Tag, op: F
    ) -> Result<T, Error>
    where F: FnOnce(Constructed<M, R>) -> Result<T, Error> {
        let (ident, start) = self.read_ident()?;
        if ident.tag() != expected {
            return Err(Error::content(
                format!("expected value with tag {expected}"),
                start
            ))
        }
        if !ident.is_constructed() {
            return Err(Error::content(
                "expected constructed value", start
            ))
        }
        let res = op(self.read_value(ident, start)?.into_constructed()?)?;
        self.check_source_status()?;
        Ok(res)
    }

    /// Optionally processes a constructed value if it has a given tag.
    ///
    /// If there is at least one more value and the next value has a tag
    /// matching `expected`, expects that value to be a constructed value.
    /// If so, passes the constructed value to the closure for processing.
    /// If the closure succeeds, its return value is returned as ‘some.’
    ///
    /// If the next value does not have the expected tag or the end of this
    /// value has been reached, the method returns `Ok(None)`. If the next
    /// value is not constructed it returns an error.
    ///
    /// An error is also returned if the closure does not process the
    /// value fully, returns en error or if accessing the underlying source
    /// fails.
    pub fn process_opt_constructed_with<F, T>(
        &mut self, expected: Tag, op: F
    ) -> Result<Option<T>, Error>
    where F: FnOnce(Constructed<M, R>) -> Result<T, Error> {
        let Some((ident, start)) = self.read_opt_ident()? else {
            return Ok(None)
        };
        if ident.tag() != expected {
            self.keep_ident(ident, start);
            return Ok(None)
        }
        if !ident.is_constructed() {
            return Err(Error::content(
                "expected constructed value", start
            ))
        }
        let res = op(self.read_value(ident, start)?.into_constructed()?)?;
        self.check_source_status()?;
        Ok(Some(res))
    }

    /// Processes a primitive value.
    ///
    /// Expects there to be at least one more value and the next value to be
    /// a primitive value. If so, passes the primitive value to the closure
    /// for processing. If the closure succeeds, returns its return value.
    ///
    /// If the next value is not primitive, if the end of value has been
    /// reached, or if the closure fails to process the next value’s content
    /// fully, an error is returned. An error is also returned if
    /// the closure returns one or if accessing the underlying source fails.
    pub fn process_primitive<F, T>(&mut self, op: F) -> Result<T, Error>
    where F: FnOnce(Primitive<M, R>) -> Result<T, Error> {
        let (ident, start) = self.read_ident()?;
        if ident.is_constructed() {
            return Err(Error::content(
                "expected primitive value", start
            ))
        }
        let res = op(self.read_value(ident, start)?.into_primitive()?)?;
        self.check_source_status()?;
        Ok(res)
    }

    /// Optionally processes a primitive value.
    ///
    /// Expects that if there is at least one more value the next value is a
    /// primitive value. If so, passes the primitive value to the closure
    /// for processing. If the closure succeeds, returns its return value 
    /// as ‘some.’
    ///
    /// If the end of value has been reached, `Ok(None)` is returned.
    ///
    /// If the next value is not primitive, if the closure fails to process
    /// the next value’s content fully, the closure returns an error, or if
    /// accessing the underlying source fails, an error is returned.
    pub fn process_opt_primitive<F, T>(
        &mut self, op: F
    ) -> Result<Option<T>, Error>
    where F: FnOnce(Primitive<M, R>) -> Result<T, Error> {
        let Some((ident, start)) = self.read_opt_ident()? else {
            return Ok(None)
        };
        if ident.is_constructed() {
            return Err(Error::content(
                "expected primitive value", start
            ))
        }
        let res = op(self.read_value(ident, start)?.into_primitive()?)?;
        self.check_source_status()?;
        Ok(Some(res))
    }

    /// Processes a primitive value with a required tag.
    ///
    /// Expects there to be at least one more value, that the next value has
    /// the given tag and that it is a primitive value. If so, the
    /// primitive value is given to the closure for processing. If the
    /// closure succeeds, its return value is returned.
    ///
    /// If the next value is not primitive or has a different tag, if
    /// the end of the value has been reached, or if the closure does not
    /// process the contained value’s content completely, a malformed error
    /// is returned. An error is also returned if the closure returns one or
    /// if accessing the underlying source fails.
    pub fn process_primitive_with<F, T>(
        &mut self, expected: Tag, op: F
    ) -> Result<T, Error>
    where F: FnOnce(Primitive<M, R>) -> Result<T, Error> {
        let (ident, start) = self.read_ident()?;
        if ident.tag() != expected {
            return Err(Error::content(
                format!("expected value with tag {expected}"),
                start
            ))
        }
        if ident.is_constructed() {
            return Err(Error::content(
                "expected primitive value", start
            ))
        }
        let res = op(self.read_value(ident, start)?.into_primitive()?)?;
        self.check_source_status()?;
        Ok(res)
    }

    /// Optionally processes a primitive value if it has a given tag.
    ///
    /// If there is at least one more value and the next value has a tag
    /// matching `expected`, expects that value to be a primitive value.
    /// If so, passes the primitive value to the closure for processing.
    /// If the closure succeeds, its return value is returned as ‘some.’
    ///
    /// If the next value does not have the expected tag or the end of this
    /// value has been reached, the method returns `Ok(None)`. If the next
    /// value is not primitive it returns an error.
    ///
    /// An error is also returned if the closure does not process the
    /// value fully, returns en error or if accessing the underlying source
    /// fails.
    pub fn process_opt_primitive_with<F, T>(
        &mut self, expected: Tag, op: F
    ) -> Result<Option<T>, Error>
    where F: FnOnce(Primitive<M, R>) -> Result<T, Error> {
        let Some((ident, start)) = self.read_opt_ident()? else {
            return Ok(None)
        };
        if ident.tag() != expected {
            self.keep_ident(ident, start);
            return Ok(None)
        }
        if ident.is_constructed() {
            return Err(Error::content(
                "expected primitive value", start
            ))
        }
        let res = op(self.read_value(ident, start)?.into_primitive()?)?;
        self.check_source_status()?;
        Ok(Some(res))
    }
}


/// # Processing Standard Values
///
/// These methods provide short-cuts for processing fundamental values in
/// their standard form. That is, the values use their regular tag and
/// encoding.
impl<'a, M: Mode, R: io::Read + 'a> Constructed<'a, M, R> {
    /// Skips over a mandatory INTEGER if it has the given value.
    ///
    /// If the next value is an integer but of a different value, returns
    /// a malformed error.
    pub fn skip_u8_if(&mut self, expected: u8) -> Result<(), Error> {
        self.process_primitive_with(Tag::INTEGER, |prim| {
            let start = prim.start();
            let got = u8::from_primitive(prim)?;
            if got != expected {
                Err(Error::content(
                    format!("expected integer {expected}"),
                    start
                ))
            }
            else {
                Ok(())
            }
        })
    }

    /// Skips over an optional INTEGER if it has the given value.
    ///
    /// Returns `Ok(Some(()))` if the next value was an integer with the
    /// expected value.
    /// Returns `Ok(None)` if the end of the constructed value was reached or
    /// if the next value did not have a tag of INTEGER.
    /// Returns an error if the next value was an integer of a different value
    /// or an integer with an illegal encoding.
    pub fn skip_opt_u8_if(
        &mut self, expected: u8
    ) -> Result<Option<()>, Error> {
        self.process_opt_primitive_with(Tag::INTEGER, |prim| {
            let start = prim.start();
            let got = u8::from_primitive(prim)?;
            if got != expected {
                Err(Error::content(
                    format!("expected integer {expected}"),
                    start
                ))
            }
            else {
                Ok(())
            }
        })
    }

    /// Processes a mandatory SEQUENCE value.
    ///
    /// This is a shortcut for
    /// `self.process_constructed_with(Tag::SEQUENCE, op)`.
    pub fn process_sequence<F, T>(
        &mut self, op: F,
    ) -> Result<T, Error>
    where F: FnOnce(Constructed<M, R>) -> Result<T, Error> {
        self.process_constructed_with(Tag::SEQUENCE, op)
    }

    /// Processes an optional SEQUENCE value.
    ///
    /// This is a shortcut for
    /// `self.process_opt_constructed_with(Tag::SEQUENCE, op)`.
    pub fn process_opt_sequence<F, T>(
        &mut self, op: F,
    ) -> Result<Option<T>, Error>
    where F: FnOnce(Constructed<M, R>) -> Result<T, Error> {
        self.process_opt_constructed_with(Tag::SEQUENCE, op)
    }

    /// Processes a mandatory SET value.
    ///
    /// This is a shortcut for
    /// `self.process_constructed_with(Tag::SET, op)`.
    pub fn process_set<F, T>(
        &mut self, op: F,
    ) -> Result<T, Error>
    where F: FnOnce(Constructed<M, R>) -> Result<T, Error> {
        self.process_constructed_with(Tag::SET, op)
    }

    /// Processes an optional SET value.
    ///
    /// This is a shortcut for
    /// `self.process_opt_constructed_with(Tag::SET^, op)`.
    pub fn process_opt_set<F, T>(
        &mut self, op: F,
    ) -> Result<Option<T>, Error>
    where F: FnOnce(Constructed<M, R>) -> Result<T, Error> {
        self.process_opt_constructed_with(Tag::SET, op)
    }
}


/// # Legacy methods
///
/// The following methods were used in previous versions of _bcder._ They
/// should be considered deprecated and are provided here for easier
/// transition.
impl<'a, M: Mode, R: io::Read + 'a> Constructed<'a, M, R> {
    /// Process one value of content.
    ///
    /// The closure `op` receives the tag and content of the next value
    /// and must process it completely, advancing to the content’s end.
    ///
    /// Upon success, the method returns the closure’s return value. The
    /// method returns a malformed error if there isn’t at least one more
    /// value available. It also returns an error if the closure returns one
    /// or if reading from the source fails.
    #[cfg_attr(
        feature = "mark-deprecated",
        deprecated(
            since = "0.8.0",
            note = "replaced by `process_value`"
        )
    )]
    pub fn take_value<F, T>(
        &mut self, op: F,
    ) -> Result<T, Error>
    where
        F: FnOnce(Tag, &mut Value<M, R>) -> Result<T, Error>,
    {
        let (ident, start) = self.read_ident()?;
        let res = op(ident.tag(), &mut self.read_value(ident, start)?)?;
        self.check_source_status()?;
        Ok(res)
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
    #[cfg_attr(
        feature = "mark-deprecated",
        deprecated(
            since = "0.8.0",
            note = "replaced by `process_opt`"
        )
    )]
    pub fn take_opt_value<F, T>(
        &mut self, op: F,
    ) -> Result<Option<T>, Error>
    where
        F: FnOnce(Tag, &mut Value<M, R>) -> Result<T, Error>,
    {
        let Some((ident, start)) = self.read_opt_ident()? else {
            return Ok(None)
        };
        let res = op(ident.tag(), &mut self.read_value(ident, start)?)?;
        self.check_source_status()?;
        Ok(Some(res))
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
    #[cfg_attr(
        feature = "mark-deprecated",
        deprecated(
            since = "0.8.0",
            note = "replaced by `process_value_with`"
        )
    )]
    pub fn take_value_if<F, T>(
        &mut self,
        expected: Tag,
        op: F
    ) -> Result<T, Error>
    where F: FnOnce(&mut Value<M, R>) -> Result<T, Error> {
        let (ident, start) = self.read_ident()?;
        if ident.tag() != expected {
            return Err(Error::content(
                format!("expected value with tag {expected}"),
                start
            ))
        }
        let res = op(&mut self.read_value(ident, start)?)?;
        self.check_source_status()?;
        Ok(res)
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
    #[cfg_attr(
        feature = "mark-deprecated",
        deprecated(
            since = "0.8.0",
            note = "replaced by `process_opt_with`"
        )
    )]
    pub fn take_opt_value_if<F, T>(
        &mut self,
        expected: Tag,
        op: F
    ) -> Result<Option<T>, Error>
    where F: FnOnce(&mut Value<M, R>) -> Result<T, Error> {
        let Some((ident, start)) = self.read_opt_ident()? else {
            return Ok(None)
        };
        if ident.tag() != expected {
            self.keep_ident(ident, start);
            return Ok(None)
        }
        let res = op(&mut self.read_value(ident, start)?)?;
        self.check_source_status()?;
        Ok(Some(res))
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
    #[cfg_attr(
        feature = "mark-deprecated",
        deprecated(
            since = "0.8.0",
            note = "replaced by `process_constructed`"
        )
    )]
    pub fn take_constructed<F, T>(&mut self, op: F) -> Result<T, Error>
    where
        F: FnOnce(Tag, &mut Constructed<M, R>) -> Result<T, Error>,
    {
        let (ident, start) = self.read_ident()?;
        if !ident.is_constructed() {
            return Err(Error::content(
                "expected constructed value", start
            ))
        }
        let res = op(
            ident.tag(),
            &mut self.read_value(ident, start)?.into_constructed()?
        )?;
        self.check_source_status()?;
        Ok(res)
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
    #[cfg_attr(
        feature = "mark-deprecated",
        deprecated(
            since = "0.8.0",
            note = "replaced by `process_opt_constructed`"
        )
    )]
    pub fn take_opt_constructed<F, T>(
        &mut self, op: F
    ) -> Result<Option<T>, Error>
    where
        F: FnOnce(Tag, &mut Constructed<M, R>) -> Result<T, Error>
    {
        let Some((ident, start)) = self.read_opt_ident()? else {
            return Ok(None)
        };
        if !ident.is_constructed() {
            return Err(Error::content(
                "expected constructed value", start
            ))
        }
        let res = op(
            ident.tag(),
            &mut self.read_value(ident, start)?.into_constructed()?
        )?;
        self.check_source_status()?;
        Ok(Some(res))
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
    #[cfg_attr(
        feature = "mark-deprecated",
        deprecated(
            since = "0.8.0",
            note = "replaced by `process_constructed_with`"
        )
    )]
    pub fn take_constructed_if<F, T>(
        &mut self, expected: Tag, op: F
    ) -> Result<T, Error>
    where
        F: FnOnce(&mut Constructed<M, R>) -> Result<T, Error>,
    {
        let (ident, start) = self.read_ident()?;
        if ident.tag() != expected {
            return Err(Error::content(
                format!("expected value with tag {expected}"),
                start
            ))
        }
        if !ident.is_constructed() {
            return Err(Error::content(
                "expected constructed value", start
            ))
        }
        let res = op(
            &mut self.read_value(ident, start)?.into_constructed()?
        )?;
        self.check_source_status()?;
        Ok(res)
    }

    /// Processes an optional constructed value if it has a given tag.
    ///
    /// If the next value is a constructed value with a tag equal to
    /// `expected`, its content is given to the closure `op` which has to
    /// process it completely. If the closure succeeds, its return value
    /// is returned.
    ///
    /// If the next value does not have the expected tag or the end of this
    /// value has been reached, the method returns `Ok(None)`. If the next
    /// value is not constructed it returns an error.
    ///
    /// An error is also returned if the closure does not process the
    /// value fully, returns en error or if accessing the underlying source
    /// fails.
    #[cfg_attr(
        feature = "mark-deprecated",
        deprecated(
            since = "0.8.0",
            note = "replaced by `process_opt_constructed_with`"
        )
    )]
    pub fn take_opt_constructed_if<F, T>(
        &mut self,
        expected: Tag,
        op: F,
    ) -> Result<Option<T>, Error>
    where
        F: FnOnce(&mut Constructed<M, R>) -> Result<T, Error>,
    {
        let Some((ident, start)) = self.read_opt_ident()? else {
            return Ok(None)
        };
        if ident.tag() != expected {
            self.keep_ident(ident, start);
            return Ok(None)
        }
        if !ident.is_constructed() {
            return Err(Error::content(
                "expected constructed value", start
            ))
        }
        let res = op(
            &mut self.read_value(ident, start)?.into_constructed()?
        )?;
        self.check_source_status()?;
        Ok(Some(res))
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
    #[cfg_attr(
        feature = "mark-deprecated",
        deprecated(
            since = "0.8.0",
            note = "replaced by `process_primitive`"
        )
    )]
    pub fn take_primitive<F, T>(&mut self, op: F) -> Result<T, Error>
    where
        F: FnOnce(Tag, &mut Primitive<M, R>) -> Result<T, Error>,
    {
        let (ident, start) = self.read_ident()?;
        if ident.is_constructed() {
            return Err(Error::content(
                "expected primitive value", start
            ))
        }
        let res = op(
            ident.tag(),
            &mut self.read_value(ident, start)?.into_primitive()?
        )?;
        self.check_source_status()?;
        Ok(res)
    }

    /// Processes an optional primitive value.
    ///
    /// If the next value is primitive, its tag and content are given to the
    /// closure `op` which has to process it fully. Upon success, the
    /// closure’s return value is returned.
    /// 
    /// If the end of value has been reached, `Ok(None)` is returned.
    /// If the next value is not primitive, if the closure fails to process
    /// the next value’s content fully, the closure returns an error, or if
    /// accessing the underlying source fails, an error is returned.
    #[cfg_attr(
        feature = "mark-deprecated",
        deprecated(
            since = "0.8.0",
            note = "replaced by `process_opt_primitive`"
        )
    )]
    pub fn take_opt_primitive<F, T>(
        &mut self, op: F,
    ) -> Result<Option<T>, Error>
    where
        F: FnOnce(Tag, &mut Primitive<M, R>) -> Result<T, Error>,
    {
        let Some((ident, start)) = self.read_opt_ident()? else {
            return Ok(None)
        };
        if ident.is_constructed() {
            return Err(Error::content(
                "expected primitive value", start
            ))
        }
        let res = op(
            ident.tag(),
            &mut self.read_value(ident, start)?.into_primitive()?
        )?;
        self.check_source_status()?;
        Ok(Some(res))
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
    #[cfg_attr(
        feature = "mark-deprecated",
        deprecated(
            since = "0.8.0",
            note = "replaced by `process_primitive_with`"
        )
    )]
    pub fn take_primitive_if<F, T>(
        &mut self, expected: Tag, op: F
    ) -> Result<T, Error>
    where F: FnOnce(&mut Primitive<M, R>) -> Result<T, Error> {
        let (ident, start) = self.read_ident()?;
        if ident.tag() != expected {
            return Err(Error::content(
                format!("expected value with tag {expected}"),
                start
            ))
        }
        if ident.is_constructed() {
            return Err(Error::content(
                "expected primitive value", start
            ))
        }
        let res = op(
            &mut self.read_value(ident, start)?.into_primitive()?
        )?;
        self.check_source_status()?;
        Ok(res)
    }

    /// Processes an optional primitive value of a given tag.
    ///
    /// If the next value is a primitive and its tag matches `expected`, its
    /// content is given to the closure `op` which has to process it
    /// completely or return an error, either of which is returned.
    ///
    /// If the end of this value has been reached or if the value’s tag
    /// doesn’t match, the method returns `Ok(None)`. If the value is not
    /// primitive, if the closure doesn’t process the next value’s content
    /// fully, of if access to the underlying source fails, the method
    /// returns an error.
    #[cfg_attr(
        feature = "mark-deprecated",
        deprecated(
            since = "0.8.0",
            note = "replaced by `process_opt_primitive_with`"
        )
    )]
    pub fn take_opt_primitive_if<F, T>(
        &mut self, expected: Tag, op: F
    ) -> Result<Option<T>, Error>
    where F: FnOnce(&mut Primitive<M, R>) -> Result<T, Error> {
        let Some((ident, start)) = self.read_opt_ident()? else {
            return Ok(None)
        };
        if ident.tag() != expected {
            self.keep_ident(ident, start);
            return Ok(None)
        }
        if ident.is_constructed() {
            return Err(Error::content(
                "expected primitive value", start
            ))
        }
        let res = op(
            &mut self.read_value(ident, start)?.into_primitive()?
        )?;
        self.check_source_status()?;
        Ok(Some(res))
    }

    /// Skips over an optional next value.
    #[cfg_attr(
        feature = "mark-deprecated",
        deprecated(
            since = "0.8.0",
            note = "renamed to `skip_opt_next`"
        )
    )]
    pub fn skip_opt<F>(
        &mut self, op: F
    ) -> Result<Option<()>, Error>
    where
        R: io::BufRead,
        F: FnMut(Tag, bool, usize) -> Result<(), Error>,
    {
        self.skip_opt_next(op)
    }

    /// Attempts to skip over the next value.
    ///
    /// If there is a next value, returns `Ok(Some(()))`, if the end of value
    /// has already been reached, returns `Ok(None)`.
    #[cfg_attr(
        feature = "mark-deprecated",
        deprecated(
            since = "0.8.0",
            note = "renamed to `skip_any_opt_next?"
        )
    )]
    pub fn skip_one(&mut self) -> Result<Option<()>, Error>
    where R: io::BufRead {
        self.skip_any_opt_next()
    }

    // XXX More:
    //
    // capture
    // capture_one
    // capture_all

    /// Processes and returns a mandatory boolean value.
    #[cfg_attr(
        feature = "mark-deprecated",
        deprecated(
            since = "0.8.0",
            note = "use `bool::decode_next` instead"
        )
    )]
    pub fn take_bool(&mut self) -> Result<bool, Error> {
        bool::decode_next(self)
    }

    /// Processes and returns an optional boolean value.
    #[cfg_attr(
        feature = "mark-deprecated",
        deprecated(
            since = "0.8.0",
            note = "use `bool::decode_opt_next` instead"
        )
    )]
    pub fn take_opt_bool(
        &mut self,
    ) -> Result<Option<bool>, Error> {
        bool::decode_opt_next(self)
    }

    /// Processes a mandatory NULL value.
    #[cfg_attr(
        feature = "mark-deprecated",
        deprecated(
            since = "0.8.0",
            note = "use `<()>::decode_next` instead"
        )
    )]
    pub fn take_null(&mut self) -> Result<(), Error> {
        <()>::decode_next(self)
    }

    /// Processes an optional NULL value.
    #[cfg_attr(
        feature = "mark-deprecated",
        deprecated(
            since = "0.8.0",
            note = "use `<()>::decode_opt_next` instead"
        )
    )]
    pub fn take_opt_null(&mut self) -> Result<Option<()>, Error> {
        <()>::decode_opt_next(self)
    }

    /// Processes a mandatory INTEGER value of the `u8` range.
    ///
    /// If the integer value is less than 0 or greater than 255, a malformed
    /// error is returned.
    #[cfg_attr(
        feature = "mark-deprecated",
        deprecated(
            since = "0.8.0",
            note = "use `u8::decode_next` instead"
        )
    )]
    pub fn take_u8(&mut self) -> Result<u8, Error> {
        u8::decode_next(self)
    }

    /// Processes an optional INTEGER value of the `u8` range.
    ///
    /// If the integer value is less than 0 or greater than 255, a malformed
    /// error is returned.
    #[cfg_attr(
        feature = "mark-deprecated",
        deprecated(
            since = "0.8.0",
            note = "use `u8::decode_opt_next` instead"
        )
    )]
    pub fn take_opt_u8(&mut self) -> Result<Option<u8>, Error> {
        u8::decode_opt_next(self)
    }

    /// Processes a mandatory INTEGER value of the `u16` range.
    ///
    /// If the integer value is less than 0 or greater than 65535, a
    /// malformed error is returned.
    #[cfg_attr(
        feature = "mark-deprecated",
        deprecated(
            since = "0.8.0",
            note = "use `u16::decode_next` instead"
        )
    )]
    pub fn take_u16(&mut self) -> Result<u16, Error> {
        u16::decode_next(self)
    }

    /// Processes an optional INTEGER value of the `u16` range.
    ///
    /// If the integer value is less than 0 or greater than 65535, a
    /// malformed error is returned.
    #[cfg_attr(
        feature = "mark-deprecated",
        deprecated(
            since = "0.8.0",
            note = "use `u16::decode_opt_next` instead"
        )
    )]
    pub fn take_opt_u16(&mut self) -> Result<Option<u16>, Error> {
        u16::decode_opt_next(self)
    }

    /// Processes a mandatory INTEGER value of the `u32` range.
    ///
    /// If the integer value is less than 0 or greater than 2^32-1, a
    /// malformed error is returned.
    #[cfg_attr(
        feature = "mark-deprecated",
        deprecated(
            since = "0.8.0",
            note = "use `u32::decode_next` instead"
        )
    )]
    pub fn take_u32(&mut self) -> Result<u32, Error> {
        u32::decode_next(self)
    }

    /// Processes an optional INTEGER value of the `u32` range.
    ///
    /// If the integer value is less than 0 or greater than 2^32-1, a
    /// malformed error is returned.
    #[cfg_attr(
        feature = "mark-deprecated",
        deprecated(
            since = "0.8.0",
            note = "use `u32::decode_opt_next` instead"
        )
    )]
    pub fn take_opt_u32(&mut self) -> Result<Option<u32>, Error> {
        u32::decode_opt_next(self)
    }

    /// Processes a mandatory INTEGER value of the `u64` range.
    ///
    /// If the integer value is less than 0 or greater than 2^64-1, a
    /// malformed error is returned.
    #[cfg_attr(
        feature = "mark-deprecated",
        deprecated(
            since = "0.8.0",
            note = "use `u64::decode_next` instead"
        )
    )]
    pub fn take_u64(&mut self) -> Result<u64, Error> {
        u64::decode_next(self)
    }

    /// Processes an optional INTEGER value of the `u64` range.
    ///
    /// If the integer value is less than 0 or greater than 2^64-1, a
    /// malformed error is returned.
    #[cfg_attr(
        feature = "mark-deprecated",
        deprecated(
            since = "0.8.0",
            note = "use `u64::decode_opt_next` instead"
        )
    )]
    pub fn take_opt_u64(&mut self) -> Result<Option<u64>, Error> {
        u64::decode_opt_next(self)
    }

    /// Processes a mandatory SEQUENCE value.
    #[cfg_attr(
        feature = "mark-deprecated",
        deprecated(
            since = "0.8.0",
            note = "replaced by `process_sequence`"
        )
    )]
    pub fn take_sequence<F, T>(&mut self, op: F) -> Result<T, Error>
    where F: FnOnce(&mut Constructed<M, R>) -> Result<T, Error> {
        self.process_sequence(|mut cons| op(&mut cons))
    }

    /// Processes an optional SEQUENCE value.
    #[cfg_attr(
        feature = "mark-deprecated",
        deprecated(
            since = "0.8.0",
            note = "replaced by `process_opt_sequence`"
        )
    )]
    pub fn take_opt_sequence<F, T>(
        &mut self, op: F
    ) -> Result<Option<T>, Error>
    where F: FnOnce(&mut Constructed<M, R>) -> Result<T, Error> {
        self.process_opt_sequence(|mut cons| op(&mut cons))
    }

    /// Processes a mandatory SET value.
    #[cfg_attr(
        feature = "mark-deprecated",
        deprecated(
            since = "0.8.0",
            note = "replaced by `process_set`"
        )
    )]
    pub fn take_set<F, T>(&mut self, op: F) -> Result<T, Error>
    where F: FnOnce(&mut Constructed<M, R>) -> Result<T, Error> {
        self.process_set(|mut cons| op(&mut cons))
    }

    /// Processes an optional SET value.
    #[cfg_attr(
        feature = "mark-deprecated",
        deprecated(
            since = "0.8.0",
            note = "replaced by `process_opt_set`"
        )
    )]
    pub fn take_opt_set<F, T>(
        &mut self, op: F
    ) -> Result<Option<T>, Error>
    where F: FnOnce(&mut Constructed<M, R>) -> Result<T, Error> {
        self.process_opt_set(|mut cons| op(&mut cons))
    }
}


//------------ ReadableConstructed--------------------------------------------

pub(super) struct ReadableConstructed<'a, M: Mode, R: io::Read + 'a> {
    pub cons: Constructed<'a, M, R>,
}

impl<'a, M: Mode, R: io::Read + 'a> ReadableConstructed<'a, M, R> {
    pub(super) fn read_opt_ident(
        &mut self
    ) -> Result<Option<(Ident, Length)>, Error> {
        self.cons.read_opt_ident()
    }

    pub(super) fn pos(&self) -> Length {
        self.cons.pos()
    }

    pub(super) fn source(&mut self) -> &mut Source<R> {
        match &mut self.cons.inner {
            ConstructedEnum::Definite(inner) => inner.source,
            ConstructedEnum::Indefinite(inner) => inner.source
        }
    }

    pub(super) fn limit(&self) -> Option<Length> {
        match &self.cons.inner {
            ConstructedEnum::Definite(inner) => Some(inner.limit),
            ConstructedEnum::Indefinite(inner) => inner.limit,
        }
    }
}

impl<'a, M: Mode, R: io::Read + 'a> From<Constructed<'a, M, R>>
for ReadableConstructed<'a, M, R> {
    fn from(cons: Constructed<'a, M, R>) -> Self {
        Self { cons }
    }
}


impl<'a, M: Mode, R: io::Read + 'a> io::Read
for ReadableConstructed<'a, M, R> {
    fn read(&mut self, buf: &mut [u8]) -> Result<usize, io::Error> {
        match &mut self.cons.inner {
            ConstructedEnum::Definite(inner) => inner.read(buf),
            ConstructedEnum::Indefinite(inner) => inner.read(buf),
        }
    }
}


//------------ DefiniteConstructed--------------------------------------------

/// The content of a constructed value with a definite length.
struct DefiniteConstructed<'a, R: 'a> {
    source: &'a mut Source<R>,
    limit: Length,
}

impl<'a, R: 'a> DefiniteConstructed<'a, R> {
    fn new<M: Mode>(
        source: &'a mut Source<R>, limit: Length,
    ) -> Result<Self, io::Error> {
        if M::ALLOW_DEFINITE_CONSTRUCTED {
            Ok(Self { source, limit })
        }
        else {
            Err(io::Error::new(io::ErrorKind::InvalidData,
                "definite length constructed in CER mode"
            ))
        }
    }

    fn remaining(&self) -> Length {
        self.limit - self.source.pos()
    }
}

impl<'a, R: io::Read + 'a> DefiniteConstructed<'a, R> {
    fn read_ident(&mut self) -> Result<Option<Ident>, io::Error> {
         Ident::read_opt(self)
    }

    fn read_value<M: Mode>(
        &mut self, ident: Ident, start: Length
    ) -> Result<Value<M, R>, io::Error> {
        match LengthOctets::read::<M>(&mut self.source)?.definite() {
            Some(Length::ZERO) if ident == Ident::END_OF_CONTENTS => {
                Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    "end-of-contents in definite length value"
                ))
            }
            Some(length) => {
                let limit = self.source.pos() + length;
                if limit > self.limit {
                    return Err(io::Error::new(
                        io::ErrorKind::InvalidData,
                        "nested value too long"
                    ))
                }
                if ident.is_constructed() {
                    Ok(Value::Constructed(
                        Constructed::new(
                            ident.tag(), start,
                            ConstructedEnum::Definite(
                                DefiniteConstructed::new::<M>(
                                    self.source, limit
                                )?
                            )
                        )
                    ))
                }
                else {
                    Ok(Value::Primitive(Primitive::new(
                        self.source, limit, ident.tag(), start
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
                Ok(Value::Constructed(
                    Constructed::new(
                        ident.tag(), start,
                        ConstructedEnum::Indefinite(
                            IndefiniteConstructed::new::<M>(
                                self.source, Some(self.limit)
                            )?
                        ),
                    )
                ))
            }
        }
    }
}

impl<'a, R: 'a> Drop for DefiniteConstructed<'a, R> {
    fn drop(&mut self) {
        if self.source.pos() != self.limit {
            self.source.set_err(SourceError::InvalidData(
                "trailing data"
            ))
        }
    }
}

impl<'a, R: io::Read + 'a> io::Read for DefiniteConstructed<'a, R> {
    fn read(&mut self, buf: &mut [u8]) -> Result<usize, io::Error> {
        let len = cmp::min(
            buf.len(),
            self.remaining().to_usize_saturating(),
        );

        // Safety: len is capped to buf.len().
        #[allow(clippy::indexing_slicing)]
        self.source.read(&mut buf[..len])
    }
}


//------------ IndefiniteConstructed -----------------------------------------

/// The content of a constructed value with a definite length.
struct IndefiniteConstructed<'a, R: io::Read + 'a> {
    source: &'a mut Source<R>,
    limit: Option<Length>,
    done: bool,
}

impl<'a, R: io::Read + 'a> IndefiniteConstructed<'a, R> {
    fn new<M: Mode>(
        source: &'a mut Source<R>, limit: Option<Length>,
    ) -> Result<Self, io::Error> {
        if M::ALLOW_DEFINITE_CONSTRUCTED {
            Ok(Self {
                source, limit,
                done: false,
            })
        }
        else {
            Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "indefinite length constructed in DER mode"
            ))
        }
    }

    fn remaining(&self) -> Option<Length> {
        self.limit.map(|limit| limit - self.source.pos())
    }
}

impl<'a, R: io::Read + 'a> IndefiniteConstructed<'a, R> {
    fn read_ident<M: Mode>(&mut self) -> Result<Option<Ident>, io::Error> {
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
                self.done = true;
                Ok(None)
            }
        }
        else {
            Ok(Some(ident))
        }
    }

    fn read_value<M: Mode>(
        &mut self, ident: Ident, start: Length
    ) -> Result<Value<M, R>, io::Error> {
        match LengthOctets::read::<M>(&mut self.source)?.definite() {
            Some(length) => {
                let limit = self.source.pos() + length;
                if let Some(parent_limit) = self.limit {
                    if limit > parent_limit {
                        return Err(io::Error::new(
                            io::ErrorKind::InvalidData,
                            "nested value too long"
                        ))
                    }
                }
                if ident.is_constructed() {
                    Ok(Value::Constructed(
                        Constructed::new(
                            ident.tag(), start,
                            ConstructedEnum::Definite(
                                DefiniteConstructed::new::<M>(
                                    self.source, limit
                                )?
                            ),
                        )
                    ))
                }
                else {
                    Ok(Value::Primitive(Primitive::new(
                        self.source, limit, ident.tag(), start
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
                Ok(Value::Constructed(
                    Constructed::new(
                        ident.tag(),
                        start,
                        ConstructedEnum::Indefinite(
                            IndefiniteConstructed::new::<M>(
                                self.source, self.limit
                            )?
                        ),
                    )
                ))
            }
        }
    }

    fn read_end_of_contents(&mut self) -> Result<(), SourceError> {
        let mut octets = [0u8; 2];
        self.read_exact(&mut octets)?;
        if octets != [0, 0] {
            return Err(SourceError::InvalidData("trailing data"))
        }
        Ok(())
    }
}

impl<'a, R: io::Read + 'a> Drop for IndefiniteConstructed<'a, R> {
    fn drop(&mut self) {
        if self.done {
            return
        }
        if let Err(err) = self.read_end_of_contents() {
            self.source.set_err(err)
        }
    }
}

impl<'a, R: io::Read + 'a> io::Read for IndefiniteConstructed<'a, R> {
    fn read(&mut self, buf: &mut [u8]) -> Result<usize, io::Error> {
        if self.done {
            let msg = "attempted read past end of value";
            self.source.set_err(SourceError::Bug(msg));
            return Err(io::Error::other(msg))
        }
        let len = cmp::min(
            buf.len(),
            self.remaining().unwrap_or(Length::MAX).to_usize_saturating()
        );

        // Safety: len is capped to buf.len()
        #[allow(clippy::indexing_slicing)]
        self.source.read(&mut buf[..len])
    }
}

