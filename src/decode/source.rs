//! The source for decoding data.
//!
//! This is an internal module. Its public types are re-exported by the
//! parent.

use std::{error, fmt, mem, ops};
use std::cmp::min;
use std::convert::Infallible;
use bytes::Bytes;
use super::error::{ContentError, DecodeError};


//------------ Source --------------------------------------------------------

/// A view into a sequence of octets.
///
/// Sources form that foundation of decoding. They provide the raw octets to
/// decoders.
///
/// A source can only progress forward over time. It provides the ability to
/// access the next few bytes as a slice or a [`Bytes`] value, and advance
/// forward.
///
/// _Please note:_ This trait may change as we gain more experience with
/// decoding in different circumstances. If you implement it for your own
/// types, we would appreciate feedback what worked well and what didn’t.
pub trait Source {
    /// The error produced when the source failed to read more data.
    type Error: error::Error;

    /// Returns the current logical postion within the sequence of data.
    fn pos(&self) -> Pos;

    /// Request at least `len` bytes to be available.
    ///
    /// The method returns the number of bytes that are actually available.
    /// This may only be smaller than `len` if the source ends with less
    /// bytes available. It may be larger than `len` but less than the total
    /// number of bytes still left in the source.
    ///
    /// The method can be called multiple times without advancing in between.
    /// If in this case `len` is larger than when last called, the source
    /// should try and make the additional data available.
    ///
    /// The method should only return an error if the source somehow fails
    /// to get more data such as an IO error or reset connection.
    fn request(&mut self, len: usize) -> Result<usize, Self::Error>;

    /// Returns a bytes slice with the available data.
    ///
    /// The slice will be at least as long as the value returned by the last
    /// successful [`request`] call. It may be longer if more data is
    /// available.
    ///
    /// [`request`]: #tymethod.request
    fn slice(&self) -> &[u8];

    /// Produces a `Bytes` value from part of the data.
    ///
    /// The method returns a [`Bytes`] value of the range `start..end` from
    /// the beginning of the current view of the source. The size of the
    /// current view is whatever the last call to [`request`][Self::request]
    /// returned.
    ///
    /// If either index is out of this range, returns `None`.
    fn bytes(&self, start: usize, end: usize) -> Option<Bytes>;

    /// Advance the source by `len` bytes.
    ///
    /// The method advances the start of the view provided by the source by
    /// `len` bytes. This value must not be greater than the value returned
    /// by the last successful call to [`request`][Self::request].
    ///
    /// If `len` is greater than allowed, the source should enter an error
    /// state where `request` always returns 0 and the current view is an
    /// empty slice. This way, faulty code will likely cause “unexpected end
    /// of data” errors which should be caughty by tests or, worst case,
    /// result in data be rejected.
    fn advance(&mut self, len: usize);

    /// Skip over the next `len` bytes.
    ///
    /// The method attempts to advance the source by `len` bytes or by
    /// however many bytes are still available if this number is smaller,
    /// without making these bytes available.
    ///
    /// Returns the number of bytes skipped over. This value may only differ
    /// from len if the remainder of the source contains less than `len`
    /// bytes.
    ///
    /// The default implementation uses `request` and `advance`. However, for
    /// some sources it may be significantly cheaper to provide a specialised
    /// implementation.
    fn skip(&mut self, len: usize) -> Result<usize, Self::Error> {
        let res = min(self.request(len)?, len);
        self.advance(res);
        Ok(res)
    }


    //--- Advanced access

    /// Takes a single octet from the source.
    ///
    /// If there aren’t any more octets available from the source, returns
    /// a content error.
    fn take_u8(&mut self) -> Result<u8, DecodeError<Self::Error>> {
        if self.request(1)? < 1 {
            return Err(self.content_err("unexpected end of data"))
        }
        let res = *self.slice().first().ok_or_else(|| {
            self.content_err("unexpected end of data")
        })?;
        self.advance(1);
        Ok(res)
    }

    /// Takes an optional octet from the source.
    ///
    /// If there aren’t any more octets available from the source, returns
    /// `Ok(None)`.
    fn take_opt_u8(
        &mut self
    ) -> Result<Option<u8>, DecodeError<Self::Error>> {
        if self.request(1)? < 1 {
            return Ok(None)
        }
        let res = *self.slice().first().ok_or_else(|| {
            self.content_err("unexpected end of data")
        })?;
        self.advance(1);
        Ok(Some(res))
    }

    /// Returns a content error at the current position of the source.
    fn content_err(
        &self, err: impl Into<ContentError>
    ) -> DecodeError<Self::Error> {
        DecodeError::content(err.into(), self.pos())
    }
}

impl<T: Source> Source for &'_ mut T {
    type Error = T::Error;

    fn request(&mut self, len: usize) -> Result<usize, Self::Error> {
        Source::request(*self, len)
    }
    
    fn advance(&mut self, len: usize) {
        Source::advance(*self, len)
    }

    fn slice(&self) -> &[u8] {
        Source::slice(*self)
    }

    fn bytes(&self, start: usize, end: usize) -> Option<Bytes> {
        Source::bytes(*self, start, end)
    }

    fn pos(&self) -> Pos {
        Source::pos(*self)
    }
}


//------------ IntoSource ----------------------------------------------------

/// A type that can be converted into a source.
pub trait IntoSource {
    type Source: Source;

    fn into_source(self) -> Self::Source;
}

impl<T: Source> IntoSource for T {
    type Source = Self;

    fn into_source(self) -> Self::Source {
        self
    }
}


//------------ Pos -----------------------------------------------------------

/// The logical position within a source.
///
/// Values of this type can only be used for diagnostics. They can not be used
/// to determine how far a source has been advanced since it was created. This
/// is why we used a newtype.
#[derive(Clone, Copy, Debug, Default)]
pub struct Pos(usize);

impl From<usize> for Pos {
    fn from(pos: usize) -> Pos {
        Pos(pos)
    }
}

impl ops::Add for Pos {
    type Output = Self;

    fn add(self, rhs: Self) -> Self {
        Pos(self.0 + rhs.0)
    }
}

impl fmt::Display for Pos {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.0.fmt(f)
    }
}


//------------ BytesSource ---------------------------------------------------

/// A source for a bytes value.
#[derive(Clone, Debug)]
pub struct BytesSource {
    /// The bytes.
    ///
    /// This value will be advanced whenever `Self::advance` is called.
    data: Bytes,

    /// The current read position in the original data.
    ///
    /// This is the position relative to the original bytes value and _not_
    /// the current value in `self.data`.
    pos: usize,

    /// The offset for the reported position.
    ///
    /// This is the value reported by `Source::pos` when `self.pos` is zero.
    /// This is 0, unles the value was created with `Self::with_offset`.
    offset: Pos,
}

impl BytesSource {
    /// Creates a new bytes source from a bytes values.
    pub fn new(data: Bytes) -> Self {
        BytesSource { data, pos: 0, offset: 0.into() }
    }

    /// Creates a new bytes source with an explicit offset.
    ///
    /// When this function is used to create a bytes source, `Source::pos`
    /// will report a value increates by `offset`.
    pub fn with_offset(data: Bytes, offset: Pos) -> Self {
        BytesSource { data, pos: 0, offset }
    }

    /// Returns the remaining length of data.
    pub fn len(&self) -> usize {
        self.data.len()
    }

    /// Returns whether there is any data remaining.
    pub fn is_empty(&self) -> bool {
        self.data.is_empty()
    }

    /// Splits the first `len` bytes off the source and returns them.
    ///
    /// # Panics
    ///
    /// This method panics of `len` is larger than `self.len()`.
    pub fn split_to(&mut self, len: usize) -> Bytes {
        let res = self.data.split_to(len);
        self.pos += len;
        res
    }

    /// Converts the source into the remaining bytes.
    pub fn into_bytes(self) -> Bytes {
        self.data
    }
}

impl Source for BytesSource {
    type Error = Infallible;

    fn pos(&self) -> Pos {
        self.offset + self.pos.into()
    }

    fn request(&mut self, _len: usize) -> Result<usize, Self::Error> {
        Ok(self.data.len())
    }

    fn slice(&self) -> &[u8] {
        self.data.as_ref()
    }

    fn bytes(&self, start: usize, end: usize) -> Option<Bytes> {
        if start > self.data.len() || end > self.data.len() {
            None
        }
        else {
            Some(self.data.slice(start..end))
        }
    }

    fn advance(&mut self, len: usize) {
        let len = min(len, self.data.len());
        bytes::Buf::advance(&mut self.data, len);
        self.pos += len;
    }
}

impl IntoSource for Bytes {
    type Source = BytesSource;

    fn into_source(self) -> Self::Source {
        BytesSource::new(self)
    }
}


//------------ SliceSource ---------------------------------------------------

#[derive(Clone, Copy, Debug)]
pub struct SliceSource<'a> {
    data: &'a [u8],
    pos: usize
}

impl<'a> SliceSource<'a> {
    /// Creates a new bytes source from a slice.
    pub fn new(data: &'a [u8]) -> Self {
        SliceSource { data, pos: 0 }
    }

    /// Returns the remaining length of data.
    pub fn len(&self) -> usize {
        self.data.len()
    }

    /// Returns whether there is any data remaining.
    pub fn is_empty(&self) -> bool {
        self.data.is_empty()
    }

    /// Splits the first `len` bytes off the source and returns them.
    ///
    /// # Panics
    ///
    /// This method panics of `len` is larger than `self.len()`.
    pub fn split_to(&mut self, len: usize) -> &'a [u8] {
        let (left, right) = self.data.split_at(len);
        self.data = right;
        self.pos += len;
        left
    }
}

impl Source for SliceSource<'_> {
    type Error = Infallible;

    fn pos(&self) -> Pos {
        self.pos.into()
    }

    fn request(&mut self, _len: usize) -> Result<usize, Self::Error> {
        Ok(self.data.len())
    }

    fn advance(&mut self, len: usize) {
        match self.data.get(len..) {
            Some(slice) => {
                self.data = slice;
                self.pos += len;
            }
            None => {
                self.pos += self.data.len();
                self.data = b"";
            }
        }
    }

    fn slice(&self) -> &[u8] {
        self.data
    }

    fn bytes(&self, start: usize, end: usize) -> Option<Bytes> {
        self.data.get(start..end).map(Bytes::copy_from_slice)
    }
}

impl<'a> IntoSource for &'a [u8] {
    type Source = SliceSource<'a>;

    fn into_source(self) -> Self::Source {
        SliceSource::new(self)
    }
}


//------------ LimitedSource -------------------------------------------------

/// A source that can be limited to a certain number of octets.
///
/// This type wraps another source and allows access to be limited to a
/// certain number of octets. It will never provide access to more than
/// that number of octets. Any attempt to advance over more octets will
/// fail with a malformed error.
///
/// The limit is, however, independent of the underlying source. It can
/// be larger than the number of octets actually available in the source.
///
/// The limit can be changed or even removed at any time.
#[derive(Clone, Debug)]
pub struct LimitedSource<S> {
    /// The source this value wraps.
    source: S,

    /// The current limit.
    ///
    /// If `limit` is `None`, there is no limit. If there is a limit, it
    /// will be decreased by calls to `advance` accordingly. I.e., this is
    /// the current limit, not the original limit.
    limit: Option<usize>,
}

/// # General Management
///
impl<S> LimitedSource<S> {
    /// Creates a new limited source for the given source.
    ///
    /// The return limited source will have no limit just yet.
    pub fn new(source: S) -> Self {
        LimitedSource {
            source,
            limit: None
        }
    }

    /// Unwraps the value and returns the source it was created from.
    pub fn unwrap(self) -> S {
        self.source
    }

    /// Returns the current limit.
    ///
    /// Returns `None` if there is no limit. Otherwise, the number returned
    /// is the number of remaining octets before the limit is reached. This
    /// does not necessarily mean that that many octets are actually
    /// available in the underlying source.
    pub fn limit(&self) -> Option<usize> {
        self.limit
    }

    /// Sets a more strict limit.
    ///
    /// The method will panic (!) if you are trying to set a new limit that
    /// is larger than the current limit or if you are trying to remove
    /// the limit by passing `None` if there currently is a limit set.
    ///
    /// Returns the old limit.
    pub fn limit_further(&mut self, limit: Option<usize>) -> Option<usize> {
        if let Some(cur) = self.limit {
            match limit {
                Some(limit) => assert!(limit <= cur),
                None => panic!("relimiting to unlimited"),
            }
        }
        mem::replace(&mut self.limit, limit)
    }

    /// Unconditionally sets a new limit.
    ///
    /// If you pass `None`, the limit will be removed.
    pub fn set_limit(&mut self, limit: Option<usize>) {
        self.limit = limit
    }
}

/// # Advanced Access
///
impl<S: Source> LimitedSource<S> {
    /// Skip over all remaining octets until the current limit is reached.
    ///
    /// If there currently is no limit, returns an error. Otherwise it
    /// will simply advance to the end of the limit which may be something
    /// the underlying source doesn’t like and thus produce an error.
    pub fn skip_all(&mut self) -> Result<(), DecodeError<S::Error>> {
        let Some(limit) = self.limit else {
            return Err(self.content_err("tried skipping over unlimited data"))
        };
        if self.request(limit)? < limit {
            return Err(self.content_err("unexpected end of data"))
        }
        self.advance(limit);
        Ok(())
    }

    /// Returns a bytes value containing all octets until the current limit.
    ///
    /// If there currently is no limit, returns an error. Otherwise it
    /// tries to acquire a bytes value for the octets from the current
    /// position to the end of the limit and advance to the end of the limit.
    ///
    /// This will result in a source error if the underlying source returns
    /// an error. It will result in a content error if the underlying source
    /// ends before the limit is reached.
    pub fn take_all(&mut self) -> Result<Bytes, DecodeError<S::Error>> {
        let Some(limit) = self.limit else {
            return Err(self.content_err("tried skipping over unlimited data"))
        };
        if self.request(limit)? < limit {
            return Err(self.content_err("unexpected end of data"))
        }
        let Some(res) = self.bytes(0, limit) else {
            return Err(self.content_err("unexpected end of data"))
        };
        self.advance(limit);
        Ok(res)
    }

    /// Checks whether the end of the limit has been reached.
    ///
    /// If a limit is currently set, the method will return a malformed
    /// error if it is larger than zero, i.e., if there are octets left to
    /// advance over before reaching the limit.
    ///
    /// If there is no limit set, the method will try to access one single
    /// octet and return a malformed error if that is actually possible, i.e.,
    /// if there are octets left in the underlying source.
    ///
    /// Any source errors are passed through. If there the data is not
    /// exhausted as described above, a content error is created.
    pub fn exhausted(&mut self) -> Result<(), DecodeError<S::Error>> {
        match self.limit {
            Some(0) => Ok(()),
            Some(_limit) => Err(self.content_err("trailing data")),
            None => {
                if self.source.request(1)? == 0 {
                    Ok(())
                }
                else {
                    Err(self.content_err("trailing data"))
                }
            }
        }
    }
}

impl<S: Source> Source for LimitedSource<S> {
    type Error = S::Error;

    fn pos(&self) -> Pos {
        self.source.pos()
    }

    fn request(&mut self, len: usize) -> Result<usize, Self::Error> {
        if let Some(limit) = self.limit {
            Ok(min(limit, self.source.request(min(limit, len))?))
        }
        else {
            self.source.request(len)
        }
    }

    fn advance(&mut self, mut len: usize) {
        if let Some(limit) = self.limit {
            len = min(len, limit);
            self.limit = Some(limit - len);
        }
        self.source.advance(len)
    }

    fn slice(&self) -> &[u8] {
        let res = self.source.slice();
        match self.limit {
            Some(limit) => res.get(..limit).unwrap_or(res),
            None => res,
        }
    }

    fn bytes(&self, mut start: usize, mut end: usize) -> Option<Bytes> {
        if let Some(limit) = self.limit {
            start = min(start, limit);
            end = min(end, limit);
        }
        self.source.bytes(start, end)
    }
}


//------------ CaptureSource -------------------------------------------------

// XXX This type is problematic with the revised `advance` semantics. We
//     should probably stop using it.

/// A source that captures what has been advanced over.
///
/// A capture source wraps a mutable reference to some other source and
/// provides the usual source access. However, instead of dropping octets
/// that have been advanced over, it keeps them around and allows taking
/// them out as a bytes value.
///
/// This type is used by [`Constructed::capture`].
///
/// [`Constructed::capture`]: struct.Constructed.html#method.capture
pub struct CaptureSource<'a, S: 'a> {
    /// The wrapped real source.
    source: &'a mut S,

    /// The number of bytes the source has promised to have for us.
    len: usize,

    /// The position in the source our view starts at.
    pos: usize,
}

impl<'a, S: Source> CaptureSource<'a, S> {
    /// Creates a new capture source using a reference to some other source.
    pub fn new(source: &'a mut S) -> Self {
        CaptureSource {
            source,
            len: 0,
            pos: 0,
        }
    }

    /// Converts the capture source into the captured bytes.
    pub fn into_bytes(self) -> Option<Bytes> {
        let res = self.source.bytes(0, self.pos);
        self.skip();
        res
    }

    /// Drops the captured bytes.
    ///
    /// Advances the underlying source to the end of the captured bytes.
    pub fn skip(self) {
        self.source.advance(self.pos)
    }
}

impl<'a, S: Source + 'a> Source for CaptureSource<'a, S> {
    type Error = S::Error;

    fn pos(&self) -> Pos {
        self.source.pos() + self.pos.into()
    }

    fn request(&mut self, len: usize) -> Result<usize, Self::Error> {
        self.len = self.source.request(self.pos + len)?;
        Ok(self.len - self.pos)
    }

    fn slice(&self) -> &[u8] {
        self.source.slice().get(self.pos..).unwrap_or(b"")
    }

    fn bytes(&self, start: usize, end: usize) -> Option<Bytes> {
        let start = start + self.pos;
        let end = end + self.pos;
        assert!(
            self.len >= start,
            "start past the end of data"
        );
        assert!(
            self.len >= end,
            "end past the end of data"
        );
        self.source.bytes(start, end)
    }

    fn advance(&mut self, len: usize) {
        self.pos += len;
    }
}


//============ Tests =========================================================

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn take_u8() {
        let mut source = b"123".into_source();
        assert_eq!(source.take_u8().unwrap(), b'1');
        assert_eq!(source.take_u8().unwrap(), b'2');
        assert_eq!(source.take_u8().unwrap(), b'3');
        assert!(source.take_u8().is_err())
    }

    #[test]
    fn take_opt_u8() {
        let mut source = b"123".into_source();
        assert_eq!(source.take_opt_u8().unwrap(), Some(b'1'));
        assert_eq!(source.take_opt_u8().unwrap(), Some(b'2'));
        assert_eq!(source.take_opt_u8().unwrap(), Some(b'3'));
        assert_eq!(source.take_opt_u8().unwrap(), None);
    }

    #[test]
    fn bytes_impl() {
        let mut bytes = Bytes::from_static(b"1234567890").into_source();
        assert!(bytes.request(4).unwrap() >= 4);
        assert!(&Source::slice(&bytes)[..4] == b"1234");
        assert_eq!(bytes.bytes(2, 4), Some(Bytes::from_static(b"34")));
        Source::advance(&mut bytes, 4);
        assert!(bytes.request(4).unwrap() >= 4);
        assert!(&Source::slice(&bytes)[..4] == b"5678");
        Source::advance(&mut bytes, 4);
        assert_eq!(bytes.request(4).unwrap(), 2);
        assert!(&Source::slice(&bytes) == b"90");
        bytes.advance(2);
        assert_eq!(bytes.request(4).unwrap(), 0);
    }

    #[test]
    fn slice_impl() {
        let mut bytes = b"1234567890".into_source();
        assert!(bytes.request(4).unwrap() >= 4);
        assert!(&bytes.slice()[..4] == b"1234");
        assert_eq!(bytes.bytes(2, 4), Some(Bytes::from_static(b"34")));
        bytes.advance(4);
        assert!(bytes.request(4).unwrap() >= 4);
        assert!(&bytes.slice()[..4] == b"5678");
        bytes.advance(4);
        assert_eq!(bytes.request(4).unwrap(), 2);
        assert!(&bytes.slice() == b"90");
        bytes.advance(2);
        assert_eq!(bytes.request(4).unwrap(), 0);
    }

    #[test]
    fn limited_source() {
        let mut the_source = LimitedSource::new(
            b"12345678".into_source()
        );
        the_source.set_limit(Some(4));

        let mut source = the_source.clone();
        assert!(source.exhausted().is_err());
        assert_eq!(source.request(6).unwrap(), 4);
        source.advance(2);
        assert!(source.exhausted().is_err());
        assert_eq!(source.request(6).unwrap(), 2);
        source.advance(2);
        source.exhausted().unwrap();
        assert_eq!(source.request(6).unwrap(), 0);

        let mut source = the_source.clone();
        source.skip_all().unwrap();
        let source = source.unwrap();
        assert_eq!(source.slice(), b"5678");

        let mut source = the_source.clone();
        assert_eq!(source.take_all().unwrap(), Bytes::from_static(b"1234"));
        source.exhausted().unwrap();
        let source = source.unwrap();
        assert_eq!(source.slice(), b"5678");
    }

    /*
    #[test]
    #[should_panic]
    fn limited_source_far_advance() {
        let mut source = LimitedSource::new(
            b"12345678".into_source()
        );
        source.set_limit(Some(4));
        assert_eq!(source.request(6).unwrap(), 4);
        source.advance(4);
        assert_eq!(source.request(6).unwrap(), 0);
        source.advance(6); // panics
    }
    */

    #[test]
    #[should_panic]
    fn limit_further() {
        let mut source = LimitedSource::new(b"12345".into_source());
        source.set_limit(Some(4));
        source.limit_further(Some(5)); // panics
    }

    #[test]
    fn capture_source() {
        let mut source = b"1234567890".into_source();
        {
            let mut capture = CaptureSource::new(&mut source);
            assert_eq!(capture.request(4).unwrap(), 10);
            capture.advance(4);
            assert_eq!(
                capture.into_bytes(),
                Some(Bytes::from_static(b"1234"))
            );
        }
        assert_eq!(source.data, b"567890");

        let mut source = b"1234567890".into_source();
        {
            let mut capture = CaptureSource::new(&mut source);
            assert_eq!(capture.request(4).unwrap(), 10);
            capture.advance(4);
            capture.skip();
        }
        assert_eq!(source.data, b"567890");
    }
}

