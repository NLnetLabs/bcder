//! The source for decoding data.
//!
//! This is an internal module. It’s public types are re-exported by the
//! parent.

use std::mem;
use std::cmp::min;
use bytes::Bytes;
use super::error::Error;


//------------ Source --------------------------------------------------------

/// A view into a sequence of octets.
///
/// Sources form that foundation of decoding. They provide the raw octets to
/// decoders.
///
/// A source can only progress forward over time. It provides the ability to
/// access the next few bytes as a slice, advance forward, or advance forward
/// returning a Bytes value of the data it advanced over.
///
/// _Please note:_ This trait may change as we gain more experience with
/// decoding in different circumstances. If you implement it for your own
/// types, we would appreciate feedback what worked well and what didn’t.
pub trait Source {
    /// The error produced by the source.
    ///
    /// The type used here needs to wrap [`ber::decode::Error`] and extends it
    /// by whatever happens if acquiring additional data fails. If `Source`
    /// is implemented for types where this acqusition cannot fail,
    /// `ber::decode::Error` should be used here.
    ///
    /// [`ber::decode::Error`]: enum.Error.html
    type Err: From<Error>;

    /// Request at least `len` bytes to be available.
    ///
    /// The method returns the number of bytes that are actually available.
    /// This may only be smaller than `len` if the source ends with less
    /// bytes available.
    ///
    /// The method should only return an error if the source somehow fails
    /// to get more data such as an IO error or reset connection.
    fn request(&mut self, len: usize) -> Result<usize, Self::Err>;

    /// Advance the source by `len` bytes.
    ///
    /// The method advances the start of the view provided by the source by
    /// `len` bytes. Advancing beyond the end of a source is an error.
    /// Implementations should return their equivalient of
    /// [`Error::Malformed`].
    ///
    /// The value of `len` may be larger than the last length previously
    /// request via [`request`].
    ///
    /// [`Error::Malformed`]: enum.Error.html#variant.Malformed
    /// [`request`]: #tymethod.request
    fn advance(&mut self, len: usize) -> Result<(), Self::Err>;

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
    /// the beginning of the current view of the source. Both indexes must
    /// not be greater than the value returned by the last successful call
    /// to [`request`].
    ///
    /// # Panics
    ///
    /// The method panics if `start` or `end` are larger than the last
    /// successful call to [`request`].
    ///
    /// [`Bytes`]: ../../bytes/struct.Bytes.html
    /// [`request`]: #tymethod.request
    fn bytes(&self, start: usize, end: usize) -> Bytes;


    //--- Advanced access

    /// Takes a single octet from the source.
    ///
    /// If there aren’t any more octets available from the source, returns
    /// a malformed error.
    fn take_u8(&mut self) -> Result<u8, Self::Err> {
        if self.request(1)? < 1 {
            xerr!(return Err(Error::Malformed.into()))
        }
        let res = self.slice()[0];
        self.advance(1)?;
        Ok(res)
    }

    /// Takes an optional octet from the source.
    ///
    /// If there aren’t any more octets available from the source, returns
    /// `Ok(None)`.
    fn take_opt_u8(&mut self) -> Result<Option<u8>, Self::Err> {
        if self.request(1)? < 1 {
            return Ok(None)
        }
        let res = self.slice()[0];
        self.advance(1)?;
        Ok(Some(res))
    }
}

impl Source for Bytes {
    type Err = Error;

    fn request(&mut self, _len: usize) -> Result<usize, Self::Err> {
        Ok(self.len())
    }

    fn advance(&mut self, len: usize) -> Result<(), Self::Err> {
        if len > self.len() {
            Err(Error::Malformed)
        }
        else {
            bytes::Buf::advance(self, len);
            Ok(())
        }
    }

    fn slice(&self) -> &[u8] {
        self.as_ref()
    }

    fn bytes(&self, start: usize, end: usize) -> Bytes {
        self.slice(start..end)
    }
}

impl<'a> Source for &'a [u8] {
    type Err = Error;

    fn request(&mut self, _len: usize) -> Result<usize, Self::Err> {
        Ok(self.len())
    }

    fn advance(&mut self, len: usize) -> Result<(), Self::Err> {
        if len > self.len() {
            Err(Error::Malformed)
        }
        else {
            *self = &self[len..];
            Ok(())
        }
    }

    fn slice(&self) -> &[u8] {
        self
    }

    fn bytes(&self, start: usize, end: usize) -> Bytes {
        Bytes::copy_from_slice(&self[start..end])
    }
}

impl<'a, T: Source> Source for &'a mut T {
    type Err = T::Err;

    fn request(&mut self, len: usize) -> Result<usize, Self::Err> {
        Source::request(*self, len)
    }
    
    fn advance(&mut self, len: usize) -> Result<(), Self::Err> {
        Source::advance(*self, len)
    }

    fn slice(&self) -> &[u8] {
        Source::slice(*self)
    }

    fn bytes(&self, start: usize, end: usize) -> Bytes {
        Source::bytes(*self, start, end)
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
    /// If there currently is no limit, the method will panic. Otherwise it
    /// will simply advance to the end of the limit which may be something
    /// the underlying source doesn’t like and thus produce an error.
    pub fn skip_all(&mut self) -> Result<(), S::Err> {
        let limit = self.limit.unwrap();
        self.advance(limit)
    }

    /// Returns a bytes value containing all octets until the current limit.
    ///
    /// If there currently is no limit, the method will panic. Otherwise it
    /// tries to acquire a bytes value for the octets from the current
    /// position to the end of the limit and advance to the end of the limit.
    /// This may result in an error by the underlying source.
    pub fn take_all(&mut self) -> Result<Bytes, S::Err> {
        let limit = self.limit.unwrap();
        if self.request(limit)? < limit {
            return Err(Error::Malformed.into())
        }
        let res = self.bytes(0, limit);
        self.advance(limit)?;
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
    pub fn exhausted(&mut self) -> Result<(), S::Err> {
        match self.limit {
            Some(0) => Ok(()),
            Some(_limit) => {
                xerr!(Err(Error::Malformed.into()))
            }
            None => {
                if self.source.request(1)? == 0 {
                    Ok(())
                }
                else {
                    xerr!(Err(Error::Malformed.into()))
                }
            }
        }
    }
}

impl<S: Source> Source for LimitedSource<S> {
    type Err = S::Err;

    fn request(&mut self, len: usize) -> Result<usize, Self::Err> {
        if let Some(limit) = self.limit {
            Ok(min(limit, self.source.request(min(limit, len))?))
        }
        else {
            self.source.request(len)
        }
    }

    fn advance(&mut self, len: usize) -> Result<(), Self::Err> {
        if let Some(limit) = self.limit {
            if len > limit {
                xerr!(return Err(Error::Malformed.into()))
            }
            self.limit = Some(limit - len);
        }
        self.source.advance(len)
    }

    fn slice(&self) -> &[u8] {
        let res = self.source.slice();
        if let Some(limit) = self.limit {
            if res.len() > limit {
                return &res[..limit]
            }
        }
        res
    }

    fn bytes(&self, start: usize, end: usize) -> Bytes {
        if let Some(limit) = self.limit {
            assert!(start <= limit);
            assert!(end <= limit);
        }
        self.source.bytes(start, end)
    }
}


//------------ CaptureSource -------------------------------------------------

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
    source: &'a mut S,
    pos: usize,
}

impl<'a, S: Source> CaptureSource<'a, S> {
    /// Creates a new capture source using a reference to some other source.
    pub fn new(source: &'a mut S) -> Self {
        CaptureSource {
            source,
            pos: 0
        }
    }

    /// Converts the capture source into the captured bytes.
    pub fn into_bytes(self) -> Bytes {
        let res = self.source.bytes(0, self.pos);
        self.skip();
        res
    }

    /// Drops the captured bytes.
    ///
    /// Advances the underlying source to the end of the captured bytes.
    pub fn skip(self) {
        if self.source.advance(self.pos).is_err() {
            panic!("failed to advance capture source");
        }
    }
}

impl<'a, S: Source + 'a> Source for CaptureSource<'a, S> {
    type Err = S::Err;

    fn request(&mut self, len: usize) -> Result<usize, Self::Err> {
        self.source.request(self.pos + len).map(|res| res - self.pos)
    }

    fn advance(&mut self, len: usize) -> Result<(), Self::Err> {
        if self.request(len)? < len {
            return Err(Error::Malformed.into())
        }
        self.pos += len;
        Ok(())
    }

    fn slice(&self) -> &[u8] {
        &self.source.slice()[self.pos..]
    }

    fn bytes(&self, start: usize, end: usize) -> Bytes {
        self.source.bytes(start + self.pos, end + self.pos)
    }
}


//============ Tests =========================================================

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn take_u8() {
        let mut source = &b"123"[..];
        assert_eq!(source.take_u8(), Ok(b'1'));
        assert_eq!(source.take_u8(), Ok(b'2'));
        assert_eq!(source.take_u8(), Ok(b'3'));
        assert_eq!(source.take_u8(), Err(Error::Malformed));
    }

    #[test]
    fn take_opt_u8() {
        let mut source = &b"123"[..];
        assert_eq!(source.take_opt_u8(), Ok(Some(b'1')));
        assert_eq!(source.take_opt_u8(), Ok(Some(b'2')));
        assert_eq!(source.take_opt_u8(), Ok(Some(b'3')));
        assert_eq!(source.take_opt_u8(), Ok(None));
    }

    #[test]
    fn bytes_impl() {
        let mut bytes = Bytes::from_static(b"1234567890");
        assert!(bytes.request(4).unwrap() >= 4);
        assert!(&Source::slice(&bytes)[..4] == b"1234");
        assert_eq!(bytes.bytes(2, 4), Bytes::from_static(b"34"));
        Source::advance(&mut bytes, 4).unwrap();
        assert!(bytes.request(4).unwrap() >= 4);
        assert!(&Source::slice(&bytes)[..4] == b"5678");
        Source::advance(&mut bytes, 4).unwrap();
        assert_eq!(bytes.request(4).unwrap(), 2);
        assert!(&Source::slice(&bytes)[..] == b"90");
        assert_eq!(
            Source::advance(&mut bytes, 4).unwrap_err(),
            Error::Malformed
        );
    }

    #[test]
    fn slice_impl() {
        let mut bytes = &b"1234567890"[..];
        assert!(bytes.request(4).unwrap() >= 4);
        assert!(&Source::slice(&bytes)[..4] == b"1234");
        assert_eq!(bytes.bytes(2, 4), Bytes::from_static(b"34"));
        Source::advance(&mut bytes, 4).unwrap();
        assert!(bytes.request(4).unwrap() >= 4);
        assert!(&Source::slice(&bytes)[..4] == b"5678");
        Source::advance(&mut bytes, 4).unwrap();
        assert_eq!(bytes.request(4).unwrap(), 2);
        assert!(&Source::slice(&bytes)[..] == b"90");
        assert_eq!(
            Source::advance(&mut bytes, 4).unwrap_err(),
            Error::Malformed
        );
    }

    #[test]
    fn limited_source() {
        let mut the_source = LimitedSource::new(&b"12345678"[..]);
        the_source.set_limit(Some(4));

        let mut source = the_source.clone();
        assert_eq!(source.exhausted(), Err(Error::Malformed));
        assert_eq!(source.request(6).unwrap(), 4);
        source.advance(2).unwrap();
        assert_eq!(source.exhausted(), Err(Error::Malformed));
        assert_eq!(source.request(6).unwrap(), 2);
        source.advance(2).unwrap();
        source.exhausted().unwrap();
        assert_eq!(source.request(6).unwrap(), 0);
        source.advance(0).unwrap();
        assert_eq!(source.advance(2).unwrap_err(), Error::Malformed);

        let mut source = the_source.clone();
        assert_eq!(source.advance(5).unwrap_err(), Error::Malformed);

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

    #[test]
    #[should_panic]
    fn limit_further() {
        let mut source = LimitedSource::new(&b"12345");
        source.set_limit(Some(4));
        source.limit_further(Some(5));
    }

    #[test]
    fn capture_source() {
        let mut source = &b"1234567890"[..];
        {
            let mut capture = CaptureSource::new(&mut source);
            capture.advance(4).unwrap();
            assert_eq!(capture.into_bytes(), Bytes::from_static(b"1234"));
        }
        assert_eq!(source, b"567890");

        let mut source = &b"1234567890"[..];
        {
            let mut capture = CaptureSource::new(&mut source);
            capture.advance(4).unwrap();
            capture.skip();
        }
        assert_eq!(source, b"567890");
    }
}
