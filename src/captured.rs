//! Captured BER-encoded data.
//!
//! This is a private module. Its public items are re-exported by the parent.

use std::{fmt, io, ops};
use bytes::{Bytes, BytesMut};
use crate::{decode, encode};
use crate::mode::Mode;


//------------ Captured ------------------------------------------------------

/// A wrapper for BER encoded data.
///
/// This types keeps a sequence of BER-encoded data in a [`Bytes`] value. It
/// allows for delayed processing of this data and therefore zero-allocation
/// handling of sequences and similar types by implementing iterators and
/// helper types that work directly on the the still-encoded data.
///
/// You usually acquire a value of this type trough the [`capture`] family of
/// methods on constructed BER content. Alternatively, you can also construct
/// a new value via the [`CapturedBuilder`].
/// 
/// Once you have a captured value, you can use the [`decode`] method to
/// decode the entire captured value or [`decode_partial`] to decode some
/// values at the start of the captured value. The latter manipulates the
/// captured content by moving past the captured values and is therefore
/// perfect for an iterator.
///
/// The value also remembers what [`Mode`] the original data was decoded in
/// and will automatically use this encoding in those methods.
///
/// [`Bytes`]: ../../bytes/struct.Bytes.html
/// [`capture`]: ../decode/struct.Constructed.html 
/// [`from_values`]: #method.from_values
/// [`empty`]: #method.empty
/// [`decode`]: #method.decode
/// [`decode_partial`]: #method.decode
/// [`Mode`]: ../enum.Mode.html
#[derive(Clone)]
pub struct Captured {
    bytes: Bytes,
    mode: Mode,
}

impl Captured {
    /// Creates a new captured value from bytes and a mode.
    ///
    /// Because we can’t guarantee that the bytes are properly encoded, we
    /// keep this function crate public. The type, however, doesn’t rely on
    /// content being properly encoded so this method isn’t unsafe.
    pub(crate) fn new(bytes: Bytes, mode: Mode) -> Self {
        Captured { bytes, mode }
    }

    /// Creates a captured value by encoding data.
    ///
    /// The function takes a value encoder, encodes it into a bytes value
    /// with the given mode, and returns the resulting data as a captured
    /// value.
    pub fn from_values<V: encode::Values>(mode: Mode, values: V) -> Self {
        let mut builder = Self::builder(mode);
        builder.extend(values);
        builder.freeze()
    }

    /// Creates a new empty captured value in the given mode.
    pub fn empty(mode: Mode) -> Self {
        Captured {
            bytes: Bytes::new(),
            mode
        }
    }

    /// Creates a builder for a captured value in the given mode.
    pub fn builder(mode: Mode) -> CapturedBuilder {
        CapturedBuilder::new(mode)
    }

    /// Converts the captured values into a builder in order to add new values.
    ///
    /// Because the captured values might be shared, this requires copying the
    /// underlying data.
    pub fn into_builder(self) -> CapturedBuilder {
        self.into()
    }

    /// Decodes the full content using the provided function argument.
    ///
    /// The method consumes the value. If you want to keep it around, simply
    /// clone it first. Since bytes values are cheap to clone, this is
    /// relatively cheap.
    pub fn decode<F, T>(self, op: F) -> Result<T, decode::Error>
    where
        F: FnOnce(
            &mut decode::Constructed<Bytes>
        ) -> Result<T, decode::Error>
    {
        self.mode.decode(self.bytes, op)
    }

    /// Decodes the beginning of the content of the captured value.
    ///
    /// The method calls `op` to parse a number of values from the beginning
    /// of the value and then advances the content of the captured value until
    /// after the end of these decoded values.
    pub fn decode_partial<F, T>(&mut self, op: F) -> Result<T, decode::Error>
    where
        F: FnOnce(
            &mut decode::Constructed<&mut Bytes>
        ) -> Result<T, decode::Error>
    {
        self.mode.decode(&mut self.bytes, op)
    }

    /// Trades the value for a bytes value with the raw data.
    pub fn into_bytes(self) -> Bytes {
        self.bytes
    }

    /// Returns a bytes slice with the raw data of the captured value.
    pub fn as_slice(&self) -> &[u8] {
        self.bytes.as_ref()
    }
}


//--- Deref and AsRef

impl ops::Deref for Captured {
    type Target = Bytes;

    fn deref(&self) -> &Bytes {
        &self.bytes
    }
}

impl AsRef<Bytes> for Captured {
    fn as_ref(&self) -> &Bytes {
        &self.bytes
    }
}

impl AsRef<[u8]> for Captured {
    fn as_ref(&self) -> &[u8] {
        self.bytes.as_ref()
    }
}


//--- encode::Values

#[allow(clippy::if_then_panic)] // Don’t follow suggestion for code clarity.
impl encode::Values for Captured {
    fn encoded_len(&self, mode: Mode) -> usize {
        if self.mode != mode && mode != Mode::Ber {
            panic!("Trying to encode a captured value with incompatible mode");
        }
        self.bytes.len()
    }

    fn write_encoded<W: io::Write>(
        &self,
        mode: Mode,
        target: &mut W
    ) -> Result<(), io::Error> {
        if self.mode != mode && mode != Mode::Ber {
            panic!("Trying to encode a captured value with incompatible mode");
        }
        target.write_all(self.bytes.as_ref())
    }
}


//--- Debug

impl fmt::Debug for Captured {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "[ ")?;
        for (i, &v) in self.bytes.iter().enumerate() {
            write!(f, "{:02x} ", v)?;
            if i % 4 == 3 {
                write!(f, " ")?;
            }
        }
        write!(f, "]")
    }
}


//------------ CapturedBuilder -----------------------------------------------

pub struct CapturedBuilder {
    bytes: BytesMut,
    mode: Mode,
}

impl CapturedBuilder {
    pub fn new(mode: Mode) -> Self {
        CapturedBuilder {
            bytes: BytesMut::new(),
            mode
        }
    }

    pub fn with_capacity(capacity: usize, mode: Mode) -> Self {
        CapturedBuilder {
            bytes: BytesMut::with_capacity(capacity),
            mode
        }
    }

    /// Extends the captured value by encoding the given values.
    ///
    /// The function encodes the given values in the captured value’s own mode
    /// and places the encoded content at the end of the captured value.
    pub fn extend<V: encode::Values>(&mut self, values: V) {
        values.write_encoded(
            self.mode,
            &mut CapturedWriter(&mut self.bytes)
        ).unwrap()
    }

    pub fn freeze(self) -> Captured {
        Captured::new(self.bytes.freeze(), self.mode)
    }
}

impl From<Captured> for CapturedBuilder {
    fn from(src: Captured) -> Self {
        CapturedBuilder {
            bytes: src.bytes.as_ref().into(),
            mode: src.mode
        }
    }
}


//------------ CapturedWriter ------------------------------------------------

struct CapturedWriter<'a>(&'a mut BytesMut);

impl<'a> io::Write for CapturedWriter<'a> {
    fn write(&mut self, buf: &[u8]) -> Result<usize, io::Error> {
        self.0.extend_from_slice(buf);
        Ok(buf.len())
    }

    fn flush(&mut self) -> Result<(), io::Error> {
        Ok(())
    }
}

