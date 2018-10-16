//! Unbounded integers.
//!
//! In ASN.1 integers are unbounded and, consequently, BER encodes integer in
//! a variable length way.  While the [decode] and [encode] modules allow
//! working with Rust’s native integer types, in some cases variable length
//! integers are necessary. This module provides two types, [`Integer`] and
//! [`Unsigned`] for signed and unsigned unbounded integers. While the
//! second type isn’t strictly necessary, unsigned unbounded integers appear
//! often enough in ASN.1 definitions to warrant a separate such type.
//!
//! [decode]: ../decode/index.html
//! [encode]: ../encode/index.html
//! [`Integer`]: struct.Integer.html
//! [`Unsigned`]: struct.Unsigned.html

use std::{cmp, hash, io};
use bytes::Bytes;
use super::decode;
use super::decode::Source;
use super::tag::Tag;
use super::encode::PrimitiveContent;
use super::Mode;


//------------ Macros for built-in integers ----------------------------------
//
// These are only for decoding. Encoding via the PrimitiveContent can be found
// in the `encode::primitive` module.

macro_rules! decode_signed {
    ( $prim:ident, $type:ident, $len:expr) => {{
        // Because the value is encoded in two’s complement, we need to fill
        // in missing left octets by 0x00 for positive numbers and 0xFF for
        // negative numbers. We achieve this by starting out with either all
        // bits zero (i.e., 0) or ones (i.e., -1) and then shifting in
        // present octets from the right.
        Self::check_head($prim)?;
        let first = $prim.take_u8()?;
        let mut res = if first & 0x80 == 0 { 0 }
                      else { (-1 << 8) | $type::from(first) };
        for _ in 1..$len {
            if $prim.remaining() == 0 {
                break
            }
            res = (res << 8) | ($type::from($prim.take_u8()?));
        }
        Ok(res)
    }}
}

macro_rules! decode_unsigned {
    ( $prim:ident, $type:ident, $len:expr) => {{
        // This is kind of like signed decoding except that we can’t allow
        // the sign bit to be set. In addition, because of the sign bit, the
        // encoding requires an extra empty left-most octet if the native
        // unsigned value has the most significant bit set.
        Self::check_head($prim)?;
        if $prim.remaining() > $len {
            if $prim.take_u8()? != 0 {
                xerr!(return Err(decode::Malformed.into()));
            }
        }
        let mut res = 0;
        for _ in 0..$len {
            if $prim.remaining() == 0 {
                break
            }
            else {
                res = (res << 8) | ($type::from($prim.take_u8()?));
            }
        }
        Ok(res)
    }}
}

macro_rules! from_impl {
    ( $from:ident, $to:ident) => {
        impl From<$from> for $to {
            fn from(val: $from) -> $to {
                unsafe {
                    $to::from_bytes_unchecked(val.to_encoded_bytes(Mode::Der))
                }
            }
        }
    }
}


//------------ Integer -------------------------------------------------------

/// A BER encoded integer.
///
/// As integers are variable length in BER, this type is just a simple wrapper
/// atop the underlying `Bytes` value containing the raw content. A value of
/// this type is a signed integer. If a value is defined as an unsigned
/// integer, i.e., as `INTEGER (0..MAX)`, you should use the sibling type
/// [`Unsigned`] instead.
///
/// In addition to these two generic types, the content decoders also provide
/// methods to parse integers into native integer types such as `i8`. If the
/// range of such a type is obviously enough, you might want to consider
/// using these methods instead.
///
/// # BER Encoding
///
/// In BER, an INTEGER is encoded as a primitive value with the content octets
/// providing a variable-length, big-endian, two‘s complement byte sequence of
/// that integer. Thus, the most-significant bit of the first octet serves as
/// the sign bit.
///
/// [`Unsigned`]: struct.Unsigned.html
#[derive(Clone, Debug)]
pub struct Integer(Bytes);

impl Integer {
    unsafe fn from_bytes_unchecked(bytes: Bytes) -> Self {
        Integer(bytes)
    }

    /// Takes a single signed integer from the beginning of an encoded value.
    ///
    /// This requires the next value in `cons` to be a primitive value with
    /// a correctly encoded signed integer.
    pub fn take_from<S: decode::Source>(
        cons: &mut decode::Constructed<S>
    ) -> Result<Self, S::Err> {
        cons.take_primitive_if(Tag::INTEGER, Self::from_primitive)
    }

    /// Constructs a signed integer from the content of a primitive value.
    pub fn from_primitive<S: decode::Source>(
        prim: &mut decode::Primitive<S>
    ) -> Result<Self, S::Err> {
        let res = prim.take_all()?;
        match (res.get(0), res.get(1).map(|x| x & 0x80 != 0)) {
            (Some(0), Some(false)) => {
                xerr!(return Err(decode::Error::Malformed.into()))
            }
            (Some(0xFF), Some(true)) => {
                xerr!(return Err(decode::Error::Malformed.into()))
            }
            (None, _) => {
                xerr!(return Err(decode::Error::Malformed.into()))
            }
            _ => { }
        }
        Ok(Integer(res))
    }

    /// Constructs an `i8` from the content of a primitive value.
    pub fn i8_from_primitive<S: decode::Source>(
        prim: &mut decode::Primitive<S>
    ) -> Result<i8, S::Err> {
        Self::check_head(prim)?;
        prim.take_u8().map(|x| x as i8)
    }

    /// Constructs an `i16` from the content of a primitive value.
    pub fn i16_from_primitive<S: decode::Source>(
        prim: &mut decode::Primitive<S>
    ) -> Result<i16, S::Err> {
        decode_signed!(prim, i16, 2)
    }

    /// Constructs an `i32` from the content of a primitive value.
    pub fn i32_from_primitive<S: decode::Source>(
        prim: &mut decode::Primitive<S>
    ) -> Result<i32, S::Err> {
        decode_signed!(prim, i32, 4)
    }

    /// Constructs an `i64` from the content of a primitive value.
    pub fn i64_from_primitive<S: decode::Source>(
        prim: &mut decode::Primitive<S>
    ) -> Result<i64, S::Err> {
        decode_signed!(prim, i64, 8)
    }

    /// Constructs an `i128` from the content of a primitive value.
    pub fn i128_from_primitive<S: decode::Source>(
        prim: &mut decode::Primitive<S>
    ) -> Result<i128, S::Err> {
        decode_signed!(prim, i128, 16)
    }

    /// Checks that an integer is started correctly.
    ///
    /// Specifically, checks that there is at least one octet and that the
    /// first nine bits of a multi-octet integer are not all the same.
    ///
    /// The latter ensures that an integer is encoded in the smallest possible
    /// number of octets. If we insist on this rule, we can use the content
    /// octets as the value for large integers and use simply compare slices
    /// for comparision.
    fn check_head<S: decode::Source>(
        prim: &mut decode::Primitive<S>
    ) -> Result<(), S::Err> {
        if prim.request(2)? == 0 {
            xerr!(return Err(decode::Error::Malformed.into()))
        }
        let slice = prim.slice();
        match (slice.get(0), slice.get(1).map(|x| x & 0x80 != 0)) {
            (Some(0), Some(false)) => {
                xerr!(Err(decode::Error::Malformed.into()))
            }
            (Some(0xFF), Some(true)) => {
                xerr!(Err(decode::Error::Malformed.into()))
            }
            _ => Ok(())
        }
    }

    /// Trades the integer into a bytes value with the raw content octets.
    pub fn into_bytes(self) -> Bytes {
        self.0
    }

    /// Returns a bytes slice with the raw content.
    pub fn as_slice(&self) -> &[u8] {
        self.0.as_ref()
    }

    /// Returns whether the number is zero.
    pub fn is_zero(&self) -> bool {
        self.0[0] == 0
    }

    /// Returns whether the integer is positive.
    ///
    /// Also returns `false` if the number is zero.
    pub fn is_positive(&self) -> bool {
        self.0[0] & 0x81 == 0x01 // XXX I think this is right ...
    }

    /// Returns whether the integer is negative.
    ///
    /// Also returns `false` if the number is zero.
    pub fn is_negative(&self) -> bool {
        self.0[0] & 0x80 == 0x80
    }
}


//--- From

from_impl!(i8, Integer);
from_impl!(i16, Integer);
from_impl!(i32, Integer);
from_impl!(i64, Integer);
from_impl!(i128, Integer);
from_impl!(u8, Integer);
from_impl!(u16, Integer);
from_impl!(u32, Integer);
from_impl!(u64, Integer);
from_impl!(u128, Integer);


//--- AsRef

impl AsRef<Bytes> for Integer {
    fn as_ref(&self) -> &Bytes {
        &self.0
    }
}

impl AsRef<[u8]> for Integer {
    fn as_ref(&self) -> &[u8] {
        self.0.as_ref()
    }
}


//--- PartialEq and Eq

impl PartialEq for Integer {
    fn eq(&self, other: &Self) -> bool {
        self.0.eq(&other.0)
    }
}

impl PartialEq<Unsigned> for Integer {
    fn eq(&self, other: &Unsigned) -> bool {
        self.eq(&other.0)
    }
}

impl Eq for Integer { }


// XXX TODO impl for native types


//--- PartialOrd and Ord

impl PartialOrd for Integer {
    fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Integer {
    fn cmp(&self, other: &Self) -> cmp::Ordering {
        match (self.is_positive(), other.is_positive()) {
            (false, false) => { // i.e., both > 0
                if self.0.len() > other.0.len() {
                    cmp::Ordering::Greater
                }
                else if self.0.len() < other.0.len() {
                    cmp::Ordering::Less
                }
                else {
                    for (&l, &r) in self.0.iter().zip(other.0.iter()) {
                        if l > r {
                            return cmp::Ordering::Greater
                        }
                        else {
                            return cmp::Ordering::Less
                        }
                    }
                    cmp::Ordering::Equal
                }
            }
            (true, true) => { // i.e., both <= 0
                if self.0.len() > other.0.len() {
                    cmp::Ordering::Less
                }
                else if self.0.len() < other.0.len() {
                    cmp::Ordering::Greater
                }
                else {
                    for (&l, &r) in self.0.iter().zip(other.0.iter()) {
                        if l > r {
                            return cmp::Ordering::Less
                        }
                        else {
                            return cmp::Ordering::Greater
                        }
                    }
                    cmp::Ordering::Equal
                }

            }
            (false, true) => cmp::Ordering::Less,
            (true, false) => cmp::Ordering::Greater,
        }
    }
}


//--- Hash

impl hash::Hash for Integer {
    fn hash<H: hash::Hasher>(&self, h: &mut H) {
        self.0.hash(h)
    }
}


//--- encode::PrimitiveContent

impl PrimitiveContent for Integer {
    const TAG: Tag = Tag::INTEGER;

    fn encoded_len(&self, _mode: Mode) -> usize {
        self.0.len()
    }

    fn write_encoded<W: io::Write>(
        &self,
        _mode: Mode,
        target: &mut W
    ) -> Result<(), io::Error> {
        target.write_all(self.0.as_ref())
    }
}


//------------ Unsigned ------------------------------------------------------

/// A BER encoded unsigned integer.
///
/// As integers are variable length in BER, this type is just a simple wrapper
/// atop the underlying `Bytes` value containing the raw content. It
/// guarantees that the wrapped integer is greater or equal to 0. This equals
/// an integer defined as `INTEGER (0..MAX)` in ASN.1.
///
/// If you need a integer without any restrictions, you can use `Integer`. If
/// you have even stricter range restrictions, you can also use the methods
/// provided on the content types to decode into Rust’s primitive integer
/// types such as `u16`.
///
/// # BER Encoding
///
/// In BER, an INTEGER is encoded as a primitive value with the content octets
/// providing a variable-length, big-endian, two‘s complement byte sequence of
/// that integer. Thus, the most-significant bit of the first octet serves as
/// the sign bit and, for an unsigned integer, has to be unset.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Unsigned(Integer);

/// # Decoding and Encoding
///
impl Unsigned {
    unsafe fn from_bytes_unchecked(bytes: Bytes) -> Self {
        Unsigned(Integer::from_bytes_unchecked(bytes))
    }

    pub fn take_from<S: decode::Source>(
        cons: &mut decode::Constructed<S>
    ) -> Result<Self, S::Err> {
        cons.take_primitive_if(Tag::INTEGER, Self::from_primitive)
    }

    pub fn from_primitive<S: decode::Source>(
        prim: &mut decode::Primitive<S>
    ) -> Result<Self, S::Err> {
        Self::check_head(prim)?;
        Integer::from_primitive(prim).map(Unsigned)
    }

    pub fn u8_from_primitive<S: decode::Source>(
        prim: &mut decode::Primitive<S>
    ) -> Result<u8, S::Err> {
        Self::check_head(prim)?;
        match prim.remaining() {
            1 => prim.take_u8(), // sign bit has been checked above.
            2 => {
                // First byte must be 0x00, second is the result.
                if prim.take_u8()? != 0 {
                    xerr!(Err(decode::Malformed.into()))
                }
                else {
                    prim.take_u8()
                }
            }
            _ => xerr!(Err(decode::Malformed.into()))
        }
    }

    pub fn u16_from_primitive<S: decode::Source>(
        prim: &mut decode::Primitive<S>
    ) -> Result<u16, S::Err> {
        Self::check_head(prim)?;
        match prim.remaining() {
            1 => Ok(prim.take_u8()?.into()),
            2 => {
                Ok(
                    u16::from(prim.take_u8()?) << 8 |
                    u16::from(prim.take_u8()?)
                )
            }
            3 => {
                if prim.take_u8()? != 0 {
                    xerr!(return Err(decode::Malformed.into()));
                }
                let res = {
                    u16::from(prim.take_u8()?) << 8 |
                    u16::from(prim.take_u8()?)
                };
                if res < 0x8000 {
                    // This could have been in fewer bytes.
                    Err(decode::Malformed.into())
                }
                else {
                    Ok(res)
                }
            }
            _ => xerr!(Err(decode::Malformed.into()))
        }
    }

    pub fn u32_from_primitive<S: decode::Source>(
        prim: &mut decode::Primitive<S>
    ) -> Result<u32, S::Err> {
        decode_unsigned!(prim, u32, 4)
    }

    pub fn u64_from_primitive<S: decode::Source>(
        prim: &mut decode::Primitive<S>
    ) -> Result<u64, S::Err> {
        decode_unsigned!(prim, u64, 8)
    }

    pub fn u128_from_primitive<S: decode::Source>(
        prim: &mut decode::Primitive<S>
    ) -> Result<u128, S::Err> {
        decode_unsigned!(prim, u128, 16)
    }

    /// Checks that an unsigned integer is started correctly.
    ///
    /// This is the same as `Int::check_head` followed by a check that the
    /// sign bit is not set.
    fn check_head<S: decode::Source>(
        prim: &mut decode::Primitive<S>
    ) -> Result<(), S::Err> {
        Integer::check_head(prim)?;
        if prim.slice().get(0).unwrap() & 0x80 != 0 {
            xerr!(Err(decode::Error::Malformed.into()))
        }
        else {
            Ok(())
        }
    }
}


//--- From

from_impl!(u8, Unsigned);
from_impl!(u16, Unsigned);
from_impl!(u32, Unsigned);
from_impl!(u64, Unsigned);
from_impl!(u128, Unsigned);


//--- AsRef

impl AsRef<Integer> for Unsigned {
    fn as_ref(&self) -> &Integer {
        &self.0
    }
}

impl AsRef<Bytes> for Unsigned {
    fn as_ref(&self) -> &Bytes {
        self.0.as_ref()
    }
}

impl AsRef<[u8]> for Unsigned {
    fn as_ref(&self) -> &[u8] {
        self.0.as_ref()
    }
}


//--- endode::PrimitiveContent

impl PrimitiveContent for Unsigned {
    const TAG: Tag = Tag::INTEGER;

    fn encoded_len(&self, mode: Mode) -> usize {
        self.0.encoded_len(mode)
    }

    fn write_encoded<W: io::Write>(
        &self,
        mode: Mode,
        target: &mut W
    ) -> Result<(), io::Error> {
        self.0.write_encoded(mode, target)
    }
}


//============ Tests =========================================================

// XXX There should be more tests here. Especially for the Ord impl.

#[cfg(test)]
mod test {
    use super::*;
    use ::Mode;
    use ::decode::Primitive;

    #[test]
    fn decode_unsigned_builtins() {
        assert_eq!(
            Primitive::decode_slice(
                b"\x00".as_ref(), Mode::Der,
                |prim| Unsigned::u8_from_primitive(prim)
            ).unwrap(),
            0
        );
        assert_eq!(
            Primitive::decode_slice(
                b"\x7F".as_ref(), Mode::Der,
                |prim| Unsigned::u8_from_primitive(prim)
            ).unwrap(),
            0x7f
        );
        assert_eq!(
            Primitive::decode_slice(
                b"\x80".as_ref(), Mode::Der,
                |prim| Unsigned::u8_from_primitive(prim)
            ).unwrap_err(),
            decode::Malformed
        );
        assert_eq!(
            Primitive::decode_slice(
                b"\x00\x80".as_ref(), Mode::Der,
                |prim| Unsigned::u8_from_primitive(prim)
            ).unwrap(),
            0x80
        );

        assert_eq!(
            Primitive::decode_slice(
                b"\x00".as_ref(), Mode::Der,
                |prim| Unsigned::u16_from_primitive(prim)
            ).unwrap(),
            0
        );
        assert_eq!(
            Primitive::decode_slice(
                b"\x12\x34".as_ref(), Mode::Der,
                |prim| Unsigned::u16_from_primitive(prim)
            ).unwrap(),
            0x1234
        );
        assert_eq!(
            Primitive::decode_slice(
                b"\x00\xA2\x34".as_ref(), Mode::Der,
                |prim| Unsigned::u16_from_primitive(prim)
            ).unwrap(),
            0xA234
        );
        assert_eq!(
            Primitive::decode_slice(
                b"\xA2\x34".as_ref(), Mode::Der,
                |prim| Unsigned::u16_from_primitive(prim)
            ).unwrap_err(),
            decode::Malformed
        );
        assert_eq!(
            Primitive::decode_slice(
                b"\x00\x12\x34".as_ref(), Mode::Der,
                |prim| Unsigned::u16_from_primitive(prim)
            ).unwrap_err(),
            decode::Malformed
        );

        assert_eq!(
            Primitive::decode_slice(
                b"\x12".as_ref(), Mode::Der,
                |prim| Unsigned::u32_from_primitive(prim)
            ).unwrap(),
            0x12
        );
        assert_eq!(
            Primitive::decode_slice(
                b"\x12\x34".as_ref(), Mode::Der,
                |prim| Unsigned::u32_from_primitive(prim)
            ).unwrap(),
            0x1234
        );
        assert_eq!(
            Primitive::decode_slice(
                b"\x12\x34\x56".as_ref(), Mode::Der,
                |prim| Unsigned::u32_from_primitive(prim)
            ).unwrap(),
            0x123456
        );
        assert_eq!(
            Primitive::decode_slice(
                b"\x12\x34\x56\x78".as_ref(), Mode::Der,
                |prim| Unsigned::u32_from_primitive(prim)
            ).unwrap(),
            0x12345678
        );
        assert_eq!(
            Primitive::decode_slice(
                b"\x00\xA2\x34\x56\x78".as_ref(), Mode::Der,
                |prim| Unsigned::u32_from_primitive(prim)
            ).unwrap(),
            0xA2345678
        );
        assert_eq!(
            Primitive::decode_slice(
                b"\x00\x12\x34\x56\x78".as_ref(), Mode::Der,
                |prim| Unsigned::u32_from_primitive(prim)
            ).unwrap_err(),
            decode::Malformed
        );
        assert_eq!(
            Primitive::decode_slice(
                b"\xa2\x34\x56\x78".as_ref(), Mode::Der,
                |prim| Unsigned::u32_from_primitive(prim)
            ).unwrap_err(),
            decode::Malformed
        );

        assert_eq!(
            Primitive::decode_slice(
                b"\x12".as_ref(), Mode::Der,
                |prim| Unsigned::u64_from_primitive(prim)
            ).unwrap(),
            0x12
        );
        assert_eq!(
            Primitive::decode_slice(
                b"\x12\x34\x56\x78\x12\x34\x56\x78".as_ref(), Mode::Der,
                |prim| Unsigned::u64_from_primitive(prim)
            ).unwrap(),
            0x1234567812345678
        );
        assert_eq!(
            Primitive::decode_slice(
                b"\0\xa2\x34\x56\x78\x12\x34\x56\x78".as_ref(), Mode::Der,
                |prim| Unsigned::u64_from_primitive(prim)
            ).unwrap(),
            0xa234567812345678
        );
        assert_eq!(
            Primitive::decode_slice(
                b"\0\x12\x34\x56\x78\x12\x34\x56\x78".as_ref(), Mode::Der,
                |prim| Unsigned::u64_from_primitive(prim)
            ).unwrap_err(),
            decode::Malformed
        );
        assert_eq!(
            Primitive::decode_slice(
                b"\x30\x12\x34\x56\x78\x12\x34\x56\x78".as_ref(), Mode::Der,
                |prim| Unsigned::u64_from_primitive(prim)
            ).unwrap_err(),
            decode::Malformed
        );

        assert_eq!(
            Primitive::decode_slice(
                b"\x12".as_ref(), Mode::Der,
                |prim| Unsigned::u64_from_primitive(prim)
            ).unwrap(),
            0x12
        );
        assert_eq!(
            Primitive::decode_slice(
                b"\x12\x34\x56\x78\x12\x34\x56\x78\
                \x12\x34\x56\x78\x12\x34\x56\x78".as_ref(), Mode::Der,
                |prim| Unsigned::u128_from_primitive(prim)
            ).unwrap(),
            0x12345678123456781234567812345678
        );
        assert_eq!(
            Primitive::decode_slice(
                b"\0\xa2\x34\x56\x78\x12\x34\x56\x78\
                \x12\x34\x56\x78\x12\x34\x56\x78".as_ref(), Mode::Der,
                |prim| Unsigned::u128_from_primitive(prim)
            ).unwrap(),
            0xa2345678123456781234567812345678
        );
        assert_eq!(
            Primitive::decode_slice(
                b"\0\x12\x34\x56\x78\x12\x34\x56\x78
                \x12\x34\x56\x78\x12\x34\x56\x78".as_ref(), Mode::Der,
                |prim| Unsigned::u128_from_primitive(prim)
            ).unwrap_err(),
            decode::Malformed
        );
        assert_eq!(
            Primitive::decode_slice(
                b"\x30\x12\x34\x56\x78\x12\x34\x56\x78
                \x12\x34\x56\x78\x12\x34\x56\x78".as_ref(), Mode::Der,
                |prim| Unsigned::u128_from_primitive(prim)
            ).unwrap_err(),
            decode::Malformed
        );
    }

    #[test]
    fn decode_signed_builtins() {
        assert_eq!(
            Primitive::decode_slice(
                b"\x00".as_ref(), Mode::Der,
                |prim| Integer::i8_from_primitive(prim)
            ).unwrap(),
            0
        );
        assert_eq!(
            Primitive::decode_slice(
                b"\xFF".as_ref(), Mode::Der,
                |prim| Integer::i8_from_primitive(prim)
            ).unwrap(),
            -1
        );
        assert_eq!(
            Primitive::decode_slice(
                b"\x00\xFF".as_ref(), Mode::Der,
                |prim| Integer::i8_from_primitive(prim)
            ).unwrap_err(),
            decode::Malformed
        );
        assert_eq!(
            Primitive::decode_slice(
                b"\x40\xFF".as_ref(), Mode::Der,
                |prim| Integer::i8_from_primitive(prim)
            ).unwrap_err(),
            decode::Malformed
        );

        assert_eq!(
            Primitive::decode_slice(
                b"\x00".as_ref(), Mode::Der,
                |prim| Integer::i16_from_primitive(prim)
            ).unwrap(),
            0
        );
        assert_eq!(
            Primitive::decode_slice(
                b"\xFF".as_ref(), Mode::Der,
                |prim| Integer::i16_from_primitive(prim)
            ).unwrap(),
            -1 
        );
        assert_eq!(
            Primitive::decode_slice(
                b"\x80\xFF".as_ref(), Mode::Der,
                |prim| Integer::i16_from_primitive(prim)
            ).unwrap(),
            -32513
        );
        assert_eq!(
            Primitive::decode_slice(
                b"\x80\xFF\x32".as_ref(), Mode::Der,
                |prim| Integer::i16_from_primitive(prim)
            ).unwrap_err(),
            decode::Malformed
        );
        assert_eq!(
            Primitive::decode_slice(
                b"\x00\xFF\x32".as_ref(), Mode::Der,
                |prim| Integer::i16_from_primitive(prim)
            ).unwrap_err(),
            decode::Malformed
        );

        assert_eq!(
            Primitive::decode_slice(
                b"\x00".as_ref(), Mode::Der,
                |prim| Integer::i32_from_primitive(prim)
            ).unwrap(),
            0
        );
        assert_eq!(
            Primitive::decode_slice(
                b"\xff".as_ref(), Mode::Der,
                |prim| Integer::i32_from_primitive(prim)
            ).unwrap(),
            -1
        );
        assert_eq!(
            Primitive::decode_slice(
                b"\x80\xFF".as_ref(), Mode::Der,
                |prim| Integer::i32_from_primitive(prim)
            ).unwrap(),
            -32513
        );
    }
}
