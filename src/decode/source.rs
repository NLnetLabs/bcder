/// 

use std::{error, fmt, io, ops};
use std::convert::Infallible;
use super::error::{ContentError, DecodeError};


//------------ Source --------------------------------------------------------

pub trait Source {
    type Fragment<'f>: Fragment<'f> where Self: 'f;
    type Error: error::Error;


    //--- Required methods

    fn pos(&self) -> Pos;

    fn request<'f>(
        &'f mut self, len: usize
    ) -> Result<Self::Fragment<'f>, Self::Error>;


    //--- Provided methods

    fn request_exact<'f>(
        &'f mut self, len: usize
    ) -> Result<Self::Fragment<'f>, DecodeError<Self::Error>> {
        let pos = self.pos();
        let frag = self.request(len)?;
        if frag.slice().len() < len {
            Err(DecodeError::content("unexpected end of data", pos))
        }
        else {
            Ok(frag)
        }
    }

    /// Takes a single octet from the source.
    ///
    /// If there aren’t any more octets available from the source, returns
    /// a content error.
    fn take_u8(&mut self) -> Result<u8, DecodeError<Self::Error>> {
        let pos = self.pos();
        let frag = self.request(1)?;
        match frag.slice().first().copied() {
            Some(value) => {
                frag.consume();
                Ok(value)
            }
            None => {
                Err(DecodeError::content("unexpected end of data", pos))
            }
        }
    }

    /// Takes an optional octet from the source.
    ///
    /// If there aren’t any more octets available from the source, returns
    /// `Ok(None)`.
    fn take_opt_u8(&mut self) -> Result<Option<u8>, Self::Error> {
        let frag = self.request(1)?;
        match frag.slice().first().copied() {
            Some(value) => {
                frag.consume();
                Ok(Some(value))
            }
            None => {
                Ok(None)
            }
        }
    }

    /// Returns the n-th octet if that many octets are available.
    ///
    /// Does not consume any fragments.
    fn peek_opt_nth(
        &mut self, n: usize
    ) -> Result<Option<u8>, DecodeError<Self::Error>> {
        let frag = self.request(n.saturating_add(1))?;
        let res = frag.slice().get(n).copied();
        Ok(res)
    }

    /// Returns the n-th octet if that many octets are available.
    ///
    /// Does not consume any fragments.
    fn peek_nth(&mut self, n: usize) -> Result<u8, DecodeError<Self::Error>> {
        let pos = self.pos();
        self.peek_opt_nth(n)?.ok_or_else(|| {
            DecodeError::content("unexpected end of data", pos)
        })
    }

    /// Returns a content error at the current position of the source.
    fn content_err(
        &self, err: impl Into<ContentError>
    ) -> DecodeError<Self::Error> {
        DecodeError::content(err.into(), self.pos())
    }
}


//------------ Fragment ------------------------------------------------------

pub trait Fragment<'f> {
    fn slice(&self) -> &[u8];

    fn consume(self);
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


//------------ SliceSource ---------------------------------------------------

#[derive(Clone, Copy, Debug)]
pub struct SliceSource<'s> {
    data: &'s [u8],
    pos: usize,
}

impl<'s> SliceSource<'s> {
    pub fn new(data: &'s [u8]) -> Self {
        Self { data, pos: 0 }
    }

    pub fn remaining(&self) -> &[u8] {
        self.data
    }
}

impl<'s> Source for SliceSource<'s> {
    type Error = Infallible;
    type Fragment<'f> = SliceFragment<'s, 'f> where Self: 'f;

    fn pos(&self) -> Pos {
        self.pos.into()
    }

    fn request<'f>(
        &'f mut self, len: usize
    ) -> Result<Self::Fragment<'f>, Self::Error> {
        let (head, tail) = match self.data.split_at_checked(len) {
            Some(some) => some,
            None => (self.data, b"".as_ref())
        };
        Ok(SliceFragment { slice: self, head, tail })
    }
}

impl<'a> IntoSource for &'a [u8] {
    type Source = SliceSource<'a>;

    fn into_source(self) -> Self::Source {
        SliceSource::new(self)
    }
}


//------------ SliceFragment -------------------------------------------------

pub struct SliceFragment<'s, 'f> {
    slice: &'f mut SliceSource<'s>,
    head: &'f [u8],
    tail: &'s [u8],
}

impl<'s, 'f> Fragment<'f> for SliceFragment<'s, 'f> {
    fn slice(&self) -> &[u8] {
        self.head
    }

    fn consume(self) {
        self.slice.data = self.tail;
        self.slice.pos += self.head.len();
    }
}


//------------ ReaderSource --------------------------------------------------

pub struct ReaderSource<R> {
    reader: R,
    buf: Vec<u8>,
    pos: usize,
}

impl<R: io::Read> Source for ReaderSource<R> {
    type Fragment<'f> = ReaderFragment<'f> where Self: 'f;
    type Error = io::Error;

    fn pos(&self) -> Pos {
        self.pos.into()
    }

    fn request<'f>(
        &'f mut self, len: usize
    ) -> Result<Self::Fragment<'f>, Self::Error> {
        let cur_len = self.buf.len();
        if cur_len < len {
            self.buf.resize(len, 0);
            self.reader.read_exact(&mut self.buf[cur_len..])?;
        }
        Ok(ReaderFragment { buf: &mut self.buf, pos: &mut self.pos, len })
    }
}


//------------ ReaderFragment ------------------------------------------------

pub struct ReaderFragment<'f> {
    buf: &'f mut Vec<u8>,
    pos: &'f mut usize,
    len: usize,
}

impl<'f> Fragment<'f> for ReaderFragment<'f> {
    fn slice(&self) -> &[u8] {
        &self.buf[..self.len]
    }

    fn consume(self) {
        self.buf.copy_within(self.len.., 0);
        self.buf.truncate(self.buf.len() - self.len);
        *self.pos += self.len;
    }
}


//------------ MaybeLimitedSource --------------------------------------------

pub struct MaybeLimitedSource<'a, S> {
    source: &'a mut S,
    limit: Option<usize>,
}

impl<'a, S> MaybeLimitedSource<'a, S> {
    pub fn new(source: &'a mut S, limit: Option<usize>) -> Self {
        Self { source, limit }
    }

    pub fn source_mut(&mut self) -> &mut S {
        self.source
    }

    pub fn limit(&self) -> Option<usize> {
        self.limit
    }
}

impl<'a, S: Source> Source for MaybeLimitedSource<'a, S> {
    type Fragment<'f> = MaybeLimitedFragment<'f, S> where Self: 'f, S: 'f;
    type Error = S::Error;

    fn pos(&self) -> Pos {
        self.source.pos()
    }

    fn request<'f>(
        &'f mut self, mut len: usize
    ) -> Result<MaybeLimitedFragment<'f, S>, Self::Error> {
        if let Some(limit) = self.limit {
            len = std::cmp::min(len, limit);
        }
        Ok(MaybeLimitedFragment {
            fragment: self.source.request(len)?,
            limit: &mut self.limit,
            len
        })
    }
}


//------------ MaybeLimitedFragment ------------------------------------------

pub struct MaybeLimitedFragment<'f, S: Source + 'f> {
    fragment: S::Fragment<'f>,
    limit: &'f mut Option<usize>,
    len: usize,
}

impl<'f, S: Source + 'f> Fragment<'f> for MaybeLimitedFragment<'f, S> {
    fn slice(&self) -> &[u8] {
        self.fragment.slice()
    }

    fn consume(self) {
        self.fragment.consume();
        if let Some(limit) = self.limit {
            *limit -= self.len
        }
    }
}


//------------ LimitedSource -------------------------------------------------

pub struct LimitedSource<'a, S> {
    source: &'a mut S,
    limit: usize,
}

impl<'a, S> LimitedSource<'a, S> {
    pub fn new(source: &'a mut S, limit: usize) -> Self {
        Self { source, limit }
    }

    pub fn source_mut(&mut self) -> &mut S {
        self.source
    }

    pub fn limit(&self) -> usize {
        self.limit
    }
}

impl<'a, S: Source> LimitedSource<'a, S> {
    pub fn request_all<'f>(
        &'f mut self
    ) -> Result<LimitedFragment<'f, S>, DecodeError<S::Error>>
    where S: 'f {
        self.request_exact(self.limit)
    }

    pub fn is_exhausted(&self) -> bool {
        self.limit == 0
    }
}

impl<'a, S: Source> Source for LimitedSource<'a, S> {
    type Fragment<'f> = LimitedFragment<'f, S> where Self: 'f, S: 'f;
    type Error = S::Error;

    fn pos(&self) -> Pos {
        self.source.pos()
    }

    fn request<'f>(
        &'f mut self, len: usize
    ) -> Result<LimitedFragment<'f, S>, Self::Error> {
        let len = std::cmp::min(len, self.limit);
        Ok(LimitedFragment {
            fragment: self.source.request(len)?,
            limit: &mut self.limit,
            len
        })
    }
}


//------------ LimitedFragment -----------------------------------------------

pub struct LimitedFragment<'f, S: Source + 'f> {
    fragment: S::Fragment<'f>,
    limit: &'f mut usize,
    len: usize,
}

impl<'f, S: Source + 'f> Fragment<'f> for LimitedFragment<'f, S> {
    fn slice(&self) -> &[u8] {
        self.fragment.slice()
    }

    fn consume(self) {
        self.fragment.consume();
        *self.limit -= self.len
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

