//! Captured BER-encoded data.

use std::{fmt, io, ops};
use bytes::Bytes;
use super::{decode, encode};
use super::mode::Mode;


//------------ Captured ------------------------------------------------------

#[derive(Clone, Eq, PartialEq)]
pub struct Captured {
    bytes: Bytes,
    mode: Mode,
}

impl Captured {
    pub(crate) fn new(bytes: Bytes, mode: Mode) -> Self {
        Captured { bytes, mode }
    }

    pub fn from_values<V: encode::Values>(mode: Mode, values: V) -> Self {
        let mut res = Self::new(Bytes::new(), mode);
        res.extend(values);
        res
    }

    pub fn empty() -> Self {
        Captured {
            bytes: Bytes::new(),
            mode: Mode::Ber
        }
    }

    pub fn into_bytes(self) -> Bytes {
        self.bytes
    }

    pub fn as_slice(&self) -> &[u8] {
        self.bytes.as_ref()
    }

    pub fn decode<F, T>(self, op: F) -> Result<T, decode::Error>
    where
        F: FnOnce(
            &mut decode::Constructed<Bytes>
        ) -> Result<T, decode::Error>
    {
        self.mode.decode(self.bytes, op)
    }

    pub fn decode_partial<F, T>(&mut self, op: F) -> Result<T, decode::Error>
    where
        F: FnOnce(
            &mut decode::Constructed<&mut Bytes>
        ) -> Result<T, decode::Error>
    {
        self.mode.decode(&mut self.bytes, op)
    }

    pub fn extend<V: encode::Values>(&mut self, values: V) {
        values.write_encoded(
            self.mode,
            &mut CapturedWriter(&mut self.bytes)
        ).unwrap()
    }
}


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


//------------ CapturedWriter ------------------------------------------------

struct CapturedWriter<'a>(&'a mut Bytes);

impl<'a> io::Write for CapturedWriter<'a> {
    fn write(&mut self, buf: &[u8]) -> Result<usize, io::Error> {
        self.0.extend_from_slice(buf);
        Ok(buf.len())
    }

    fn flush(&mut self) -> Result<(), io::Error> {
        Ok(())
    }
}
