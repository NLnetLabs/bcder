/// 

use std::{error, fmt, io, ops};
use std::convert::Infallible;
use super::error::{ContentError, DecodeError};


//------------ Source and Fragment -------------------------------------------

/// A type encoded data can be read from.
///
/// Sources form that foundation of decoding. They provide the raw octets to
/// decoders by progressing over chunks of data.
///
/// Reading happens by requesting a certain amount of data through the
/// [`request`][Self::request] method. The data will returned in the form
/// of a [`Fragment`] which allows access to the data and also to consume
/// the data which will progress the source beyond it. If the fragment is
/// simply dropped, the next `request` will return the same data again.
///
/// The fragment’s data is available as a byte slice via its
/// [`slice`][Fragment::slice] method. It returns the slice with the shortest
/// possible lifetime (equal to that of the `&self` argument). This is enough
/// for cases where the content of the slice is converted into a static type.
///
/// However, sources can offer the slice with a longer lifetime but how
/// long depends on whether they have all data already available or only
/// hold a portion in a temporary buffer. In the former case, the slice can
/// have the same lifetime as the source itself while im the latter case, the
/// lifetime is only that of the fragment.
///
/// The trait [`BorrowedFragment`] allows the source to define this lifetime
/// and a user to connect its own lifetimes by placing an additional bound on
/// `Source::Fragment` in a where clause. Because this is a bit unwieldy and
/// unnecessary in many cases, we split this into a separate trait.
///
/// If a decode function doesn’t want to keep the slice, it can be defined
/// simply as:
///
/// ```rust
/// # struct Foo;
/// use bcder::decode::{DecodeError, Source};
///
/// fn take_foo<S: Source>(
///     source: &mut S
/// ) -> Result<Foo, DecodeError<S::Error>> {
///     todo!()
/// }
/// ```
///
/// If, however, you want to keep the slice, the trait bounds become a little
/// more involved:
///
/// ```rust
/// # struct Foo<'a>(&'a [u8]);
/// use bcder::decode::{BorrowedFragment, DecodeError, Source};
///
/// fn take_foo<'a, S>(
///     source: &mut S
/// ) -> Result<Foo<'a>, DecodeError<S::Error>>
/// where
///     S: Source,
///     for<'f> <S as Source>::Fragment<'f>: BorrowedFragment<'a, 'f>
/// {
///     todo!()
/// }
/// ```
///
/// Because of this possible difference in lifetimes, fragments do not deref
/// into `[u8]` but rather you have to request the intended version of the
/// slice explicitely by either calling [`slice`][Fragment::slice] or
/// [`borrowed_slice`][BorrowedFragment::borrowed_slice].
pub trait Source {
    /// The fragment type returned.
    type Fragment<'f>: Fragment<'f> where Self: 'f;

    /// The error produced when the source failed to read more data.
    ///
    /// If the source cannot fail, e.g., because it already has all the 
    /// data available, it will set this error to `Infallible`.
    type Error: error::Error;


    //--- Required methods

    /// Returns the current read position within the source.
    ///
    /// The position is increased every time a fragment is consumed.
    fn pos(&self) -> Pos;

    /// Request a fragment of data of `len` bytes.
    ///
    /// The method returns a fragment of data if it can either make `len`
    /// bytes available or if it ends short of the length. In other words,
    /// the slice of the returned fragment maybe shorter than `len`.
    ///
    /// The methd only returns an error if the source fails to get more
    /// data such as reading from a file failing or a connection being
    /// reset.
    fn request<'f>(
        &'f mut self, len: usize
    ) -> Result<Self::Fragment<'f>, Self::Error>;


    //--- Provided methods

    /// Requests a fragment of exactly `len` bytes.
    ///
    /// On success, the slice of the returned fragment will be exactly `len`
    /// bytes long.
    ///
    /// If the source stop short of the required length or if it fails to
    /// get more data if ncecessary, an error is returned.
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
    /// If there are at least `n` bytes available, returns `Ok(Some(_))`
    /// with the nth byte’s value. If the source ends before that byte,
    /// returns `Ok(None)`. If getting more data fails, returns an error.
    ///
    /// The method does not consume any data.
    fn peek_opt_nth(
        &mut self, n: usize
    ) -> Result<Option<u8>, Self::Error> {
        let frag = self.request(n.saturating_add(1))?;
        let res = frag.slice().get(n).copied();
        Ok(res)
    }

    /// Returns the n-th octet.
    ///
    /// If there are fewer than `n` bytes available or if the source ends
    /// before the `n`th byte, returns an error.
    ///
    /// The method does not consume any data.
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

/// A fragment of data requested from a source.
///
/// A fragment lets you access the data through the [`slice`][Self::slice]
/// method.
///
/// When you are done with processing the fragment, you can ask the source
/// to consume the entire fragment through the [`consume`][Self::consume]
/// method.
///
/// For more details on reading data, see the documentation of the [`Source`]
/// trait.
pub trait Fragment<'f> {
    /// Returns a slice with the data of the fragment.
    ///
    /// This slice will only life for the lifetime of `&self`. If you need
    /// a longer lifetime, require the fragment to implement
    /// [`BorrowedFragment`] and call
    /// [`borrow_slice`][BorrowedFragment:.borrow_slice] on it.
    fn slice(&self) -> &[u8];

    /// Consumes the fragment.
    ///
    /// This causes the underlying source to advance beyond this fragment.
    /// The next requested fragment will start right after it.
    fn consume(self);
}

/// A fragment of data with an eplicit lifetime.
///
/// This trait allows a [`Source`] to provide a [`Fragment`] with an extended
/// lifetime of the returned slice, typically the lifetime of the source
/// itself.
///
/// For more details on reading data, see the documentation of the [`Source`]
/// trait.
pub trait BorrowedFragment<'a, 'f> {
    /// Returns a slice with the data of the fragment.
    fn borrow_slice(&self) -> &'a [u8];
}


//------------ IntoSource ----------------------------------------------------

/// A type that can be converted into a source.
pub trait IntoSource {
    /// The type of source the type is converted into.
    type Source: Source;

    /// Creates a source from a value.
    fn into_source(self) -> Self::Source;
}

impl<T: Source> IntoSource for T {
    type Source = Self;

    fn into_source(self) -> Self::Source {
        self
    }
}


//------------ SliceSource ---------------------------------------------------

/// A source atop a byte slice.
///
/// This is a very thin layer atop a byte slice that implements the [`Source`]
/// trait. See there for further information.
///
/// The source’s fragment implements [`BorrowedFragment`] with a lifetime
/// equal to that of the underlying byte slice and thus allows you to borrow
/// data from it for the same lifetime while decoding data.
#[derive(Clone, Copy, Debug)]
pub struct SliceSource<'s> {
    /// The remaining slice.
    ///
    /// When consuming a fragment, this value is replaces with the remaining
    /// data.
    data: &'s [u8],

    /// The position of the start of `self.data` in the original slice.
    pos: usize,
}

impl<'s> SliceSource<'s> {
    /// Creates a new slice source from the given slice.
    pub fn new(data: &'s [u8]) -> Self {
        Self { data, pos: 0 }
    }

    /// Returns a reference to the remaining data.
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

/// The fragment of a [`SliceSource`].
///
/// See the documentation of [`Fragment`] and [`BorrowedFragment`] for more
/// information.
pub struct SliceFragment<'s, 'f> {
    /// The slice source this fragment was crated for.
    slice: &'f mut SliceSource<'s>,

    /// The data of the fragment.
    head: &'s [u8],

    /// The data remaining if this fragment is consumed.
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

impl<'s, 'f> BorrowedFragment<'s, 'f> for SliceFragment<'s, 'f> {
    fn borrow_slice(&self) -> &'s [u8] {
        self.head
    }
}


//------------ ReaderSource --------------------------------------------------

/// A source atop something that implements `io::Read`.
///
/// The source reads data from the reader whenever needed.
///
/// > This is currently a naive implementation only buffering the smallest
/// > amount possible. It should probably be improved to proactively buffer
/// > more data akin of what `BufReader` is doing. With the current
/// > implementation, you probably benefit from wrapping a raw reader in a
/// > `BufReader` to improve performance.
pub struct ReaderSource<R> {
    /// The underlying reader.
    reader: R,

    /// A buffer of things we have read from the reader.
    ///
    /// For lifetime reasons, `Fragment::consume` cannot manipulate the
    /// buffer. Instead, we let it change `self.start` indicating how much
    /// data in the buffer it has consumed and clean up the buffer whenever
    /// `Source::request` is called the next time.
    ///
    /// This approach has the added benefit that all the slice indexing
    /// necessary to manipulate the buffer happens exclusively in the
    /// `Source::request` impl which makes it easier to vet.
    buf: Vec<u8>,

    /// The index of the current position within `self.buf`.
    start: usize,

    /// The current position from the start of the source.
    pos: usize,
}

impl<R: io::Read> Source for ReaderSource<R> {
    type Fragment<'f> = ReaderFragment<'f> where Self: 'f;
    type Error = io::Error;

    fn pos(&self) -> Pos {
        self.pos.into()
    }

    #[allow(clippy::slicing_indexing)]
    fn request<'f>(
        &'f mut self, len: usize
    ) -> Result<Self::Fragment<'f>, Self::Error> {
        // If we don’t have enough buffer, we’ve got some read’n to do.
        if self.start + len < self.buf.len() {
            // Don’t bother moving data around if it is already where it
            // needs to be or if the necessary data fits.
            if self.start != 0 && self.start + len > self.buf.capacity() {
                // Move what’s left to the start of the buffer.
                let trunc = self.buf.len() - self.start;
                self.buf.copy_within(self.start.., 0);
                self.buf.truncate(trunc);
                self.start = 0;
            }
            // Now read what we need to read. This works like std’s
            // io::Read::read_exact except that we don’t error out if we end
            // short.
            let mut read_start = self.buf.len();
            self.buf.resize(self.start + len, 0);
            while read_start < self.buf.len() {
                match self.reader.read(&mut self.buf[read_start..]) {
                    Ok(0) => break,
                    Ok(n) => {
                        read_start += n;
                    }
                    Err(ref e) if e.kind() == io::ErrorKind::Interrupted => { }
                    Err(e) => return Err(e),
                }
            }
        }

        let slice = &mut self.buf[self.start..self.start + len];

        Ok(ReaderFragment {
            slice, start: &mut self.start, pos: &mut self.pos,
        })
    }
}


//------------ ReaderFragment ------------------------------------------------

/// The [`Fragment`] of [`ReaderSource`].
///
/// The fragment provides its slice at most with the lifetime of itself.
pub struct ReaderFragment<'f> {
    /// The slice of data provided by the fragment.
    slice: &'f [u8],

    /// The start position in the source’s buffer.
    ///
    /// This value is increased by the slice length if the fragment is
    /// consumed.
    start: &'f mut usize,

    /// The current position of the source.
    ///
    /// This value is increased by the slice length if the fragment is
    /// consumed.
    pos: &'f mut usize,
}

impl<'f> Fragment<'f> for ReaderFragment<'f> {
    fn slice(&self) -> &[u8] {
        self.slice
    }

    fn consume(self) {
        *self.start += self.slice.len();
        *self.pos += self.slice.len();
    }
}

impl<'f> BorrowedFragment<'f, 'f> for ReaderFragment<'f> {
    fn borrow_slice(&self) -> &'f [u8] {
        self.slice
    }
}


//------------ MaybeLimitedSource --------------------------------------------

/// A source that wraps another source possibly limiting the length.
///
/// This type wraps a mutable reference to some other source and optionally
/// limits the amount of data that allows to read.
///
/// Alternatively, [`LimitedSource`] provides a version that always has a
/// limit.
///
/// The type is primarly used by [`Constructed`][crate::decode::Constructed].
pub struct MaybeLimitedSource<'a, S> {
    source: &'a mut S,
    limit: Option<usize>,
}

impl<'a, S> MaybeLimitedSource<'a, S> {
    /// Creates a new value from a source and an optional limit.
    pub fn new(source: &'a mut S, limit: Option<usize>) -> Self {
        Self { source, limit }
    }

    /// Returns the wrapped reference to the source.
    pub fn source_mut(&mut self) -> &mut S {
        self.source
    }

    /// Returns the remaining limit of the source if it has one.
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
        })
    }
}


//------------ MaybeLimitedFragment ------------------------------------------

/// A fragment of a [`MaybeLimitedSource`].
pub struct MaybeLimitedFragment<'f, S: Source + 'f> {
    /// The fragment received from the underlying sourcce.
    fragment: S::Fragment<'f>,

    /// The optional limit of the source.
    limit: &'f mut Option<usize>,
}

impl<'f, S: Source + 'f> Fragment<'f> for MaybeLimitedFragment<'f, S> {
    fn slice(&self) -> &[u8] {
        self.fragment.slice()
    }

    fn consume(self) {
        let len = self.fragment.slice().len();
        self.fragment.consume();
        if let Some(limit) = self.limit {
            *limit -= len
        }
    }
}

impl<'s, 'f, S> BorrowedFragment<'s, 'f> for MaybeLimitedFragment<'f, S>
where
    S: Source + 'f,
    <S as Source>::Fragment<'f>: BorrowedFragment<'s, 'f>,
{
    fn borrow_slice(&self) -> &'s [u8] {
        self.fragment.borrow_slice()
    }
}


//------------ LimitedSource -------------------------------------------------

/// A source that wraps another source possibly limiting the length.
///
/// This type wraps a mutable reference to some other source and optionally
/// limits the amount of data that allows to read.
///
/// Alternatively, [`LimitedSource`] provides a version that always has a
/// limit.
///
/// The type is primarly used by [`Constructed`][crate::decode::Constructed].
pub struct LimitedSource<'a, S> {
    source: &'a mut S,
    limit: usize,
}

impl<'a, S> LimitedSource<'a, S> {
    /// Creates a new value from a source and a limit.
    pub fn new(source: &'a mut S, limit: usize) -> Self {
        Self { source, limit }
    }

    /// Returns the wrapped mutable reference to the underlying source.
    pub fn source_mut(&mut self) -> &mut S {
        self.source
    }

    /// Returns the remaining limit of the source.
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

impl<'s, 'f, S> BorrowedFragment<'s, 'f> for LimitedFragment<'f, S>
where
    S: Source + 'f,
    <S as Source>::Fragment<'f>: BorrowedFragment<'s, 'f>
{
    fn borrow_slice(&self) -> &'s [u8] {
        self.fragment.borrow_slice()
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


//============ Tests =========================================================

#[cfg(test)]
mod test {
    use crate::decode::content::Constructed;
    use crate::mode::Der;
    use crate::tag::Tag;
    use super::*;

    // This is less a test and more a demonstration for the concept of the
    // BorrowedFragment for now.

    fn take_borrowed_octet_string<'a, S>(
        cons: &mut Constructed<Der, S>
    ) -> Result<&'a [u8], DecodeError<S::Error>>
    where
        S: Source,
        for<'f> <S as Source>::Fragment<'f>: BorrowedFragment<'a, 'f>
    {
        cons.take_value_if(Tag::OCTET_STRING, |content| {
            let prim = content.as_primitive()?;
            let frag = prim.request_all()?;
            let res = frag.borrow_slice();
            frag.consume();
            Ok(res)
        })
    }

    #[test]
    fn borrowed_source() {
        fn foo(_: &'static [u8]) { }

        foo(
            Constructed::<Der, _>::decode(
                b"23123123".into_source(),
                |cons| take_borrowed_octet_string(cons)
            ).unwrap()
        );
    }
}

