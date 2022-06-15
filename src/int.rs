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

use std::{cmp, error, fmt, hash, io, mem};
use std::convert::TryFrom;
use bytes::Bytes;
use crate::decode;
use crate::decode::{Error as _, Source};
use crate::encode::PrimitiveContent;
use crate::mode::Mode;
use crate::tag::Tag;


//------------ Macros for built-in integers ----------------------------------
//
// These are only for decoding. Encoding via the PrimitiveContent can be found
// in the `encode::primitive` module.

macro_rules! slice_to_builtin {
    // Decodes an integer contained in the slice $slice into the builtin
    // signed integer type $type. Produces an Ok(value) if this works or
    // an Err($err) if it doesn’t.
    ( signed, $slice:expr, $type:ident, $err:expr) => {{
        const LEN: usize = mem::size_of::<$type>();
        if $slice.len() > LEN {
            Err($err)
        }
        else {
            // Start with all zeros if positive or all 0xFF if negative
            // number. There’s always at least one octet.
            let mut res = if $slice[0] & 0x80 == 0 { [0; LEN] }
            else { [0xFF; LEN] };

            // Copy over all available octets.
            res[LEN - $slice.len()..].copy_from_slice($slice);
            Ok($type::from_be_bytes(res))
        }
    }};

    // Ditto for unsigned builtin integer types.
    ( unsigned, $slice:expr, $type:ident, $err:expr) => {{
        // This is like signed above except that we can simply error
        // out if the sign bit is set.
        const LEN: usize = mem::size_of::<$type>();
        if $slice[0] & 0x80 != 0 {
            Err($err)
        }
        else {
            let val = if $slice[0] == 0 { &$slice[1..] }
                      else { $slice };
            if val.len() == 0 {
                Ok(0)
            }
            else if val.len() > LEN {
                Err($err)
            }
            else {
                let mut res =  [0; LEN];
                res[LEN - val.len()..].copy_from_slice(val);
                Ok($type::from_be_bytes(res))
            }
        }
    }};
}

macro_rules! decode_builtin {
    ( $flavor:ident, $prim:expr, $type:ident) => {{
        Self::check_head($prim)?;
        let res = {
            let slice = $prim.slice_all()?;
            slice_to_builtin!(
                $flavor, slice, $type,
                $crate::decode::Error::malformed("invalid integer")
            )?
        };
        $prim.skip_all()?;
        Ok(res)
    }}
}

macro_rules! from_builtin {
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

macro_rules! builtin_from {
    ($flavor:ident, $from:ident, $to:ident) => {
        impl<'a> TryFrom<&'a $from> for $to {
            type Error = OverflowError;

            fn try_from(val: &'a $from) -> Result<$to, Self::Error> {
                let val = val.as_slice();
                slice_to_builtin!($flavor, val, $to, OverflowError(()))
            }
        }

        impl TryFrom<$from> for $to {
            type Error = OverflowError;

            fn try_from(val: $from) -> Result<$to, Self::Error> {
                $to::try_from(&val)
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
    ) -> Result<Self, S::Error> {
        cons.take_primitive_if(Tag::INTEGER, Self::from_primitive)
    }

    /// Constructs a signed integer from the content of a primitive value.
    pub fn from_primitive<S: decode::Source>(
        prim: &mut decode::Primitive<S>
    ) -> Result<Self, S::Error> {
        let res = prim.take_all()?;
        match (res.get(0), res.get(1).map(|x| x & 0x80 != 0)) {
            (Some(0), Some(false)) => {
                return Err(S::Error::malformed("invalid integer"))
            }
            (Some(0xFF), Some(true)) => {
                return Err(S::Error::malformed("invalid integer"))
            }
            (None, _) => {
                return Err(S::Error::malformed("invalid integer"))
            }
            _ => { }
        }
        Ok(Integer(res))
    }

    /// Constructs an `i8` from the content of a primitive value.
    pub fn i8_from_primitive<S: decode::Source>(
        prim: &mut decode::Primitive<S>
    ) -> Result<i8, S::Error> {
        Self::check_head(prim)?;
        prim.take_u8().map(|x| x as i8)
    }

    /// Constructs an `i16` from the content of a primitive value.
    pub fn i16_from_primitive<S: decode::Source>(
        prim: &mut decode::Primitive<S>
    ) -> Result<i16, S::Error> {
        decode_builtin!(signed, prim, i16)
    }

    /// Constructs an `i32` from the content of a primitive value.
    pub fn i32_from_primitive<S: decode::Source>(
        prim: &mut decode::Primitive<S>
    ) -> Result<i32, S::Error> {
        decode_builtin!(signed, prim, i32)
    }

    /// Constructs an `i64` from the content of a primitive value.
    pub fn i64_from_primitive<S: decode::Source>(
        prim: &mut decode::Primitive<S>
    ) -> Result<i64, S::Error> {
        decode_builtin!(signed, prim, i64)
    }

    /// Constructs an `i128` from the content of a primitive value.
    pub fn i128_from_primitive<S: decode::Source>(
        prim: &mut decode::Primitive<S>
    ) -> Result<i128, S::Error> {
        decode_builtin!(signed, prim, i128)
    }

    /// Checks that an integer is started correctly.
    ///
    /// Specifically, checks that there is at least one octet and that the
    /// first nine bits of a multi-octet integer are not all the same.
    ///
    /// The latter ensures that an integer is encoded in the smallest possible
    /// number of octets. If we insist on this rule, we can use the content
    /// octets as the value for large integers and simply compare slices
    /// for equality comparision.
    fn check_head<S: decode::Source>(
        prim: &mut decode::Primitive<S>
    ) -> Result<(), S::Error> {
        if prim.request(2)? == 0 {
            return Err(S::Error::malformed("invalid integer"))
        }
        let slice = prim.slice();
        match (slice.get(0), slice.get(1).map(|x| x & 0x80 != 0)) {
            (Some(0), Some(false)) => {
                Err(S::Error::malformed("invalid integer"))
            }
            (Some(0xFF), Some(true)) => {
                Err(S::Error::malformed("invalid integer"))
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
        if self.0[0] == 0 && self.0.get(1).is_none() {
            return false
        }
        self.0[0] & 0x80 == 0x00
    }

    /// Returns whether the integer is negative.
    ///
    /// Also returns `false` if the number is zero.
    pub fn is_negative(&self) -> bool {
        self.0[0] & 0x80 == 0x80
    }
}


//--- From and TryFrom

from_builtin!(i8, Integer);
from_builtin!(i16, Integer);
from_builtin!(i32, Integer);
from_builtin!(i64, Integer);
from_builtin!(i128, Integer);
from_builtin!(u8, Integer);
from_builtin!(u16, Integer);
from_builtin!(u32, Integer);
from_builtin!(u64, Integer);
from_builtin!(u128, Integer);

builtin_from!(signed, Integer, i8);
builtin_from!(signed, Integer, i16);
builtin_from!(signed, Integer, i32);
builtin_from!(signed, Integer, i64);
builtin_from!(signed, Integer, i128);
builtin_from!(unsigned, Integer, u8);
builtin_from!(unsigned, Integer, u16);
builtin_from!(unsigned, Integer, u32);
builtin_from!(unsigned, Integer, u64);
builtin_from!(unsigned, Integer, u128);


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
            (true, true) => { // i.e., both > 0
                match self.0.len().cmp(&other.0.len()) {
                    cmp::Ordering::Equal => {
                        for (l, r) in self.0.iter().zip(other.0.iter()) {
                            match l.cmp(r) {
                                cmp::Ordering::Equal => { }
                                cmp => return cmp
                            }
                        }
                        cmp::Ordering::Equal
                    }
                    cmp => cmp
                }
            }
            (false, false) => { // i.e., both <= 0
                match self.0.len().cmp(&other.0.len()) {
                    cmp::Ordering::Equal => {
                        for (l, r) in self.0.iter().zip(other.0.iter()) {
                            match l.cmp(r) {
                                cmp::Ordering::Equal => { }
                                cmp => return cmp.reverse()
                            }
                        }
                        cmp::Ordering::Equal
                    }
                    cmp => cmp.reverse()
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

impl<'a> PrimitiveContent for &'a Integer {
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

    /// Constructs `Unsigned` by copying from a `&[u8]`.
    ///
    /// # Errors
    ///
    /// Will return a malformed error if the given slice is empty.
    pub fn from_slice(slice: &[u8]) -> Result<Self, InvalidInteger> {
        Self::from_bytes(Bytes::copy_from_slice(slice))
    }

    /// Constructs `Unsigned` from `Bytes`, copying only if needed.
    ///
    /// # Errors
    ///
    /// Will return a malformed error if the given slice is empty.
    pub fn from_bytes(bytes: Bytes) -> Result<Self, InvalidInteger> {
        if bytes.is_empty() {
            return Err(InvalidInteger(()))
        }

        // Skip any leading zero bytes.
        let num_leading_zero_bytes = bytes.as_ref().iter().take_while(|&&b| {
            b == 0x00
        }).count();
        let value = bytes.slice(num_leading_zero_bytes..);

        // Create a new Unsigned integer from the given value bytes, ensuring
        // that the most-significant bit is zero.
        let new_bytes = if value[0] & 0x80 == 0 {
            // Use the value bytes as-is.
            value
        } else if num_leading_zero_bytes > 0 {
            // Use the value bytes and one of the preceeding zero "sign" bytes.
            bytes.slice(num_leading_zero_bytes - 1..)
        } else {
            // Copy the bytes in order to prepend a zero "sign" byte.
            let mut v: Vec<u8> = Vec::with_capacity(value.len() + 1);
            v.push(0x00);
            v.extend(value.iter());
            Bytes::from(v)
        };

        unsafe { Ok(Unsigned::from_bytes_unchecked(new_bytes)) }
    }

    pub fn take_from<S: decode::Source>(
        cons: &mut decode::Constructed<S>
    ) -> Result<Self, S::Error> {
        cons.take_primitive_if(Tag::INTEGER, Self::from_primitive)
    }

    pub fn from_primitive<S: decode::Source>(
        prim: &mut decode::Primitive<S>
    ) -> Result<Self, S::Error> {
        Self::check_head(prim)?;
        Integer::from_primitive(prim).map(Unsigned)
    }

    pub fn u8_from_primitive<S: decode::Source>(
        prim: &mut decode::Primitive<S>
    ) -> Result<u8, S::Error> {
        Self::check_head(prim)?;
        match prim.remaining() {
            1 => prim.take_u8(), // sign bit has been checked above.
            2 => {
                // First byte must be 0x00, second is the result.
                if prim.take_u8()? != 0 {
                    Err(S::Error::malformed("invalid integer"))
                }
                else {
                    prim.take_u8()
                }
            }
            _ => Err(S::Error::malformed("invalid integer"))
        }
    }

    pub fn u16_from_primitive<S: decode::Source>(
        prim: &mut decode::Primitive<S>
    ) -> Result<u16, S::Error> {
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
                    return Err(S::Error::malformed("invalid integer"))
                }
                let res = {
                    u16::from(prim.take_u8()?) << 8 |
                    u16::from(prim.take_u8()?)
                };
                if res < 0x8000 {
                    // This could have been in fewer bytes.
                    Err(S::Error::malformed("invalid integer"))
                }
                else {
                    Ok(res)
                }
            }
            _ => Err(S::Error::malformed("invalid integer"))
        }
    }

    pub fn u32_from_primitive<S: decode::Source>(
        prim: &mut decode::Primitive<S>
    ) -> Result<u32, S::Error> {
        Self::check_head(prim)?;
        decode_builtin!(unsigned, prim, u32)
    }

    pub fn u64_from_primitive<S: decode::Source>(
        prim: &mut decode::Primitive<S>
    ) -> Result<u64, S::Error> {
        Self::check_head(prim)?;
        decode_builtin!(unsigned, prim, u64)
    }

    pub fn u128_from_primitive<S: decode::Source>(
        prim: &mut decode::Primitive<S>
    ) -> Result<u128, S::Error> {
        Self::check_head(prim)?;
        decode_builtin!(unsigned, prim, u128)
    }

    /// Checks that an unsigned integer is started correctly.
    ///
    /// This is the same as `Int::check_head` followed by a check that the
    /// sign bit is not set.
    fn check_head<S: decode::Source>(
        prim: &mut decode::Primitive<S>
    ) -> Result<(), S::Error> {
        Integer::check_head(prim)?;
        if prim.slice().get(0).unwrap() & 0x80 != 0 {
            Err(S::Error::malformed("invalid integer"))
        }
        else {
            Ok(())
        }
    }

    /// Trades the integer into a bytes value with the raw content octets.
    pub fn into_bytes(self) -> Bytes {
        self.0.into_bytes()
    }

    /// Returns a bytes slice with the raw content.
    pub fn as_slice(&self) -> &[u8] {
        self.0.as_slice()
    }

    /// Returns whether the number is zero.
    pub fn is_zero(&self) -> bool {
        self.0.is_zero()
    }
}


//--- From and TryFrom

from_builtin!(u8, Unsigned);
from_builtin!(u16, Unsigned);
from_builtin!(u32, Unsigned);
from_builtin!(u64, Unsigned);
from_builtin!(u128, Unsigned);

builtin_from!(signed, Unsigned, i8);
builtin_from!(signed, Unsigned, i16);
builtin_from!(signed, Unsigned, i32);
builtin_from!(signed, Unsigned, i64);
builtin_from!(signed, Unsigned, i128);
builtin_from!(unsigned, Unsigned, u8);
builtin_from!(unsigned, Unsigned, u16);
builtin_from!(unsigned, Unsigned, u32);
builtin_from!(unsigned, Unsigned, u64);
builtin_from!(unsigned, Unsigned, u128);


impl<'a> TryFrom<Bytes> for Unsigned {
    type Error = InvalidInteger;

    fn try_from(value: Bytes) -> Result<Self, Self::Error> {
        Unsigned::from_bytes(value)
    }
}

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

impl<'a> PrimitiveContent for &'a Unsigned {
    const TAG: Tag = Tag::INTEGER;

    fn encoded_len(&self, mode: Mode) -> usize {
        (&self.0).encoded_len(mode)
    }

    fn write_encoded<W: io::Write>(
        &self,
        mode: Mode,
        target: &mut W
    ) -> Result<(), io::Error> {
        (&self.0).write_encoded(mode, target)
    }
}


//------------ InvalidInteger ------------------------------------------------

/// A octets slice does not contain a validly encoded integer.
#[derive(Clone, Copy, Debug)]
pub struct InvalidInteger(());

impl fmt::Display for InvalidInteger {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "invalid integer")
    }
}

impl error::Error for InvalidInteger { }


//------------ OverflowError -------------------------------------------------

#[derive(Clone, Copy, Debug)]
pub struct OverflowError(());

impl fmt::Display for OverflowError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "integer out of range")
    }
}

impl error::Error for OverflowError { }


//============ Tests =========================================================

// XXX There should be more tests here. Especially for the Ord impl.

#[cfg(test)]
mod test {
    use super::*;
    use crate::Mode;
    use crate::decode::Primitive;

    fn test_der<T: PrimitiveContent>(value: T, expected: &[u8]) {
        assert_eq!(value.encoded_len(Mode::Der), expected.len());
        let mut target = Vec::new();
        value.write_encoded(Mode::Der, &mut target).unwrap();
        assert_eq!(target, expected);
    }

    #[test]
    fn is_positive_negative() {
        let neg = [-0xF74402, -0xF744, -0xF7];
        let pos = [0xF7, 0xF744, 0xF74402];

        for &i in &neg {
            assert!(!Integer::from(i).is_positive(), "{}", i);
            assert!(Integer::from(i).is_negative(), "{}", i);
        }
        for &i in &pos {
            assert!(Integer::from(i).is_positive(), "{}", i);
            assert!(!Integer::from(i).is_negative(), "{}", i);
        }
        assert!(!Integer::from(0).is_positive());
        assert!(!Integer::from(0).is_negative());
    }

    #[test]
    fn cmp() {
        let ints = [-0xF74402, -0xF744, -0xF7, 0, 0xF7, 0xF744, 0xF74402];
        for &left in &ints {
            for &right in &ints {
                assert_eq!(
                    Integer::from(left).cmp(&Integer::from(right)),
                    left.cmp(&right),
                    "comparision of {} and {} failed", left, right
                )
            }
        }
    }

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
        assert!(
            Primitive::decode_slice(
                b"\x80".as_ref(), Mode::Der,
                |prim| Unsigned::u8_from_primitive(prim)
            ).is_err()
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
        assert!(
            Primitive::decode_slice(
                b"\xA2\x34".as_ref(), Mode::Der,
                |prim| Unsigned::u16_from_primitive(prim)
            ).is_err()
        );
        assert!(
            Primitive::decode_slice(
                b"\x00\x12\x34".as_ref(), Mode::Der,
                |prim| Unsigned::u16_from_primitive(prim)
            ).is_err()
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
        assert!(
            Primitive::decode_slice(
                b"\x00\x12\x34\x56\x78".as_ref(), Mode::Der,
                |prim| Unsigned::u32_from_primitive(prim)
            ).is_err()
        );
        assert!(
            Primitive::decode_slice(
                b"\xa2\x34\x56\x78".as_ref(), Mode::Der,
                |prim| Unsigned::u32_from_primitive(prim)
            ).is_err()
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
        assert!(
            Primitive::decode_slice(
                b"\0\x12\x34\x56\x78\x12\x34\x56\x78".as_ref(), Mode::Der,
                |prim| Unsigned::u64_from_primitive(prim)
            ).is_err()
        );
        assert!(
            Primitive::decode_slice(
                b"\x30\x12\x34\x56\x78\x12\x34\x56\x78".as_ref(), Mode::Der,
                |prim| Unsigned::u64_from_primitive(prim)
            ).is_err()
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
        assert!(
            Primitive::decode_slice(
                b"\0\x12\x34\x56\x78\x12\x34\x56\x78
                \x12\x34\x56\x78\x12\x34\x56\x78".as_ref(), Mode::Der,
                |prim| Unsigned::u128_from_primitive(prim)
            ).is_err()
        );
        assert!(
            Primitive::decode_slice(
                b"\x30\x12\x34\x56\x78\x12\x34\x56\x78
                \x12\x34\x56\x78\x12\x34\x56\x78".as_ref(), Mode::Der,
                |prim| Unsigned::u128_from_primitive(prim)
            ).is_err()
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
        assert!(
            Primitive::decode_slice(
                b"\x00\xFF".as_ref(), Mode::Der,
                |prim| Integer::i8_from_primitive(prim)
            ).is_err()
        );
        assert!(
            Primitive::decode_slice(
                b"\x40\xFF".as_ref(), Mode::Der,
                |prim| Integer::i8_from_primitive(prim)
            ).is_err()
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
        assert!(
            Primitive::decode_slice(
                b"\x80\xFF\x32".as_ref(), Mode::Der,
                |prim| Integer::i16_from_primitive(prim)
            ).is_err()
        );
        assert!(
            Primitive::decode_slice(
                b"\x00\xFF\x32".as_ref(), Mode::Der,
                |prim| Integer::i16_from_primitive(prim)
            ).is_err()
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

    #[test]
    fn unsigned_builtin_from() {
        let int = Integer(b"\x00".as_ref().into());
        assert_eq!(u8::try_from(&int).unwrap(), 0);
        assert_eq!(u16::try_from(&int).unwrap(), 0);
        assert_eq!(u32::try_from(&int).unwrap(), 0);
        assert_eq!(u64::try_from(&int).unwrap(), 0);
        assert_eq!(u128::try_from(&int).unwrap(), 0);
        assert_eq!(i8::try_from(&int).unwrap(), 0);
        assert_eq!(i16::try_from(&int).unwrap(), 0);
        assert_eq!(i32::try_from(&int).unwrap(), 0);
        assert_eq!(i64::try_from(&int).unwrap(), 0);
        assert_eq!(i128::try_from(&int).unwrap(), 0);

        let int = Integer(b"\x7F".as_ref().into());
        assert_eq!(u8::try_from(&int).unwrap(), 0x7F);
        assert_eq!(u16::try_from(&int).unwrap(), 0x7F);
        assert_eq!(u32::try_from(&int).unwrap(), 0x7F);
        assert_eq!(u64::try_from(&int).unwrap(), 0x7F);
        assert_eq!(u128::try_from(&int).unwrap(), 0x7F);
        assert_eq!(i8::try_from(&int).unwrap(), 0x7F);
        assert_eq!(i16::try_from(&int).unwrap(), 0x7F);
        assert_eq!(i32::try_from(&int).unwrap(), 0x7F);
        assert_eq!(i64::try_from(&int).unwrap(), 0x7F);
        assert_eq!(i128::try_from(&int).unwrap(), 0x7F);

        let int = Integer(b"\x80".as_ref().into());
        assert!(u8::try_from(&int).is_err());
        assert!(u16::try_from(&int).is_err());
        assert!(u32::try_from(&int).is_err());
        assert!(u64::try_from(&int).is_err());
        assert!(u128::try_from(&int).is_err());
        assert_eq!(i8::try_from(&int).unwrap(), -128);
        assert_eq!(i16::try_from(&int).unwrap(), -128);
        assert_eq!(i32::try_from(&int).unwrap(), -128);
        assert_eq!(i64::try_from(&int).unwrap(), -128);
        assert_eq!(i128::try_from(&int).unwrap(), -128);

        let int = Integer(b"\x00\x80".as_ref().into());
        assert_eq!(u8::try_from(&int).unwrap(), 0x80);
        assert_eq!(u16::try_from(&int).unwrap(), 0x80);
        assert_eq!(u32::try_from(&int).unwrap(), 0x80);
        assert_eq!(u64::try_from(&int).unwrap(), 0x80);
        assert_eq!(u128::try_from(&int).unwrap(), 0x80);

        let int = Integer(b"\x12\x34".as_ref().into());
        assert!(u8::try_from(&int).is_err());
        assert_eq!(u16::try_from(&int).unwrap(), 0x1234);
        assert_eq!(u32::try_from(&int).unwrap(), 0x1234);
        assert_eq!(u64::try_from(&int).unwrap(), 0x1234);
        assert_eq!(u128::try_from(&int).unwrap(), 0x1234);
        assert!(i8::try_from(&int).is_err());
        assert_eq!(i16::try_from(&int).unwrap(), 0x1234);
        assert_eq!(i32::try_from(&int).unwrap(), 0x1234);
        assert_eq!(i64::try_from(&int).unwrap(), 0x1234);
        assert_eq!(i128::try_from(&int).unwrap(), 0x1234);

        let int = Integer(b"\xA2\x34".as_ref().into());
        assert!(u8::try_from(&int).is_err());
        assert!(u16::try_from(&int).is_err());
        assert!(u32::try_from(&int).is_err());
        assert!(u64::try_from(&int).is_err());
        assert!(u128::try_from(&int).is_err());
        assert!(i8::try_from(&int).is_err());
        assert_eq!(i16::try_from(&int).unwrap(), -24012);
        assert_eq!(i32::try_from(&int).unwrap(), -24012);
        assert_eq!(i64::try_from(&int).unwrap(), -24012);
        assert_eq!(i128::try_from(&int).unwrap(), -24012);

        let int = Integer(b"\x00\xA2\x34".as_ref().into());
        assert!(u8::try_from(&int).is_err());
        assert_eq!(u16::try_from(&int).unwrap(), 0xA234);
        assert_eq!(u32::try_from(&int).unwrap(), 0xA234);
        assert_eq!(u64::try_from(&int).unwrap(), 0xA234);
        assert_eq!(u128::try_from(&int).unwrap(), 0xA234);

        let int = Integer(b"\x12\x34\x56".as_ref().into());
        assert!(u8::try_from(&int).is_err());
        assert!(u16::try_from(&int).is_err());
        assert_eq!(u32::try_from(&int).unwrap(), 0x123456);
        assert_eq!(u64::try_from(&int).unwrap(), 0x123456);
        assert_eq!(u128::try_from(&int).unwrap(), 0x123456);
        assert!(i8::try_from(&int).is_err());
        assert!(i16::try_from(&int).is_err());
        assert_eq!(i32::try_from(&int).unwrap(), 0x123456);
        assert_eq!(i64::try_from(&int).unwrap(), 0x123456);
        assert_eq!(i128::try_from(&int).unwrap(), 0x123456);

        let int = Integer(b"\x12\x34\x56\x78".as_ref().into());
        assert!(u8::try_from(&int).is_err());
        assert!(u16::try_from(&int).is_err());
        assert_eq!(u32::try_from(&int).unwrap(), 0x12345678);
        assert_eq!(u64::try_from(&int).unwrap(), 0x12345678);
        assert_eq!(u128::try_from(&int).unwrap(), 0x12345678);
        assert!(i8::try_from(&int).is_err());
        assert!(i16::try_from(&int).is_err());
        assert_eq!(i32::try_from(&int).unwrap(), 0x12345678);
        assert_eq!(i64::try_from(&int).unwrap(), 0x12345678);
        assert_eq!(i128::try_from(&int).unwrap(), 0x12345678);

        let int = Integer(b"\xA2\x34\x56\x78".as_ref().into());
        assert!(u8::try_from(&int).is_err());
        assert!(u16::try_from(&int).is_err());
        assert!(u32::try_from(&int).is_err());
        assert!(u64::try_from(&int).is_err());
        assert!(u128::try_from(&int).is_err());
        assert!(i8::try_from(&int).is_err());
        assert!(i16::try_from(&int).is_err());
        assert_eq!(i32::try_from(&int).unwrap(), -1573628296);
        assert_eq!(i64::try_from(&int).unwrap(), -1573628296);
        assert_eq!(i128::try_from(&int).unwrap(), -1573628296);

        let int = Integer(b"\x00\xA2\x34\x56\x78".as_ref().into());
        assert!(u8::try_from(&int).is_err());
        assert!(u16::try_from(&int).is_err());
        assert_eq!(u32::try_from(&int).unwrap(), 0xA2345678);
        assert_eq!(u64::try_from(&int).unwrap(), 0xA2345678);
        assert_eq!(u128::try_from(&int).unwrap(), 0xA2345678);
    }
 
    #[test]
    fn encode_variable_length_unsigned_from_slice() {
        assert!(Unsigned::from_slice(&[]).is_err());
        test_der(&Unsigned::from_slice(&[0xFF]).unwrap(), b"\x00\xFF");
        test_der(&Unsigned::from_slice(&[0x00, 0xFF]).unwrap(), b"\x00\xFF");
        test_der(
            &Unsigned::from_slice(&[0x00, 0x00, 0xFF]).unwrap(),
            b"\x00\xFF"
        );
        test_der(
            &Unsigned::from_slice(
                &[0x00, 0x00, 0xDE, 0xAD, 0xBE, 0xEF]
            ).unwrap(),
            b"\x00\xDE\xAD\xBE\xEF"
        );
    }

    #[test]
    fn encode_variable_length_unsigned_from_bytes() {
        assert!(Unsigned::from_bytes(Bytes::new()).is_err());
        test_der(
            &Unsigned::from_bytes(Bytes::from(vec![0xFF])).unwrap(),
            b"\x00\xFF"
        );
        test_der(
            &Unsigned::from_bytes(Bytes::from(vec![0x00, 0xFF])).unwrap(),
            b"\x00\xFF"
        );
        test_der(
            &Unsigned::from_bytes(Bytes::from(
                vec![0x00, 0x00, 0xFF])
            ).unwrap(),
            b"\x00\xFF"
        );
        test_der(
            &Unsigned::from_bytes(Bytes::from(
                vec![0x00, 0x00, 0xDE, 0xAD, 0xBE, 0xEF]
            )).unwrap(),
            b"\x00\xDE\xAD\xBE\xEF"
        );
    }

    #[test]
    fn encode_variable_length_unsigned_try_from_bytes() {
        assert!(Unsigned::try_from(Bytes::new()).is_err());
        test_der(
            &Unsigned::try_from(Bytes::from(vec![0xFF])).unwrap(),
            b"\x00\xFF"
        );
        test_der(
            &Unsigned::try_from(Bytes::from(vec![0x00, 0xFF])).unwrap(),
            b"\x00\xFF"
        );
        test_der(
            &Unsigned::try_from(Bytes::from(vec![0x00, 0x00, 0xFF])).unwrap(),
            b"\x00\xFF"
        );
        test_der(
            &Unsigned::try_from(Bytes::from(
                    vec![0x00, 0x00, 0xDE, 0xAD, 0xBE, 0xEF]
            )).unwrap(),
            b"\x00\xDE\xAD\xBE\xEF"
        );
    }
}
