//! BER encoded integers.
//!
//! TODO: Add more useful things to these types.

use std::io;
use bytes::Bytes;
use super::decode;
use super::decode::Source;
use super::tag::Tag;
use super::encode::PrimitiveContent;
use super::Mode;


//------------ Macros for built-in integers ----------------------------------

macro_rules! signed_impl {
    ( $prim:ident, $type:ident, $len:expr) => {{
        Self::check_head($prim)?;
        let first = $prim.take_u8()?;
        if first & 0x80 != 0 {
            if $prim.remaining() == $len - 1 {
                // Full length. Simple shift the octets in.
                let mut res = $type::from(first);
                for _ in 1..$len {
                    res = (res << 8) | $type::from($prim.take_u8()?);
                }
                Ok(res)
            }
            else {
                // Short encoding. To calculate the two’s complement, we need
                // the value of the integer value of the sign bit and subtract
                // that from the integer value of all the other bits.
                let mut sign: $type = 0x80;
                let mut sum = $type::from(first & 0x7F);
                for _ in 1..$len - 1 {
                    if $prim.remaining() == 0 {
                        break
                    }
                    sign <<= 8;
                    sum = (sum << 8) | $type::from($prim.take_u8()?);
                }
                Ok(sum - sign)
            }
        }
        else {
            let mut res = $type::from(first);
            for _ in 1..$len {
                if $prim.remaining() == 0 {
                    break
                }
                else {
                    res = (res << 8) | ($type::from($prim.take_u8()?));
                }
            }
            Ok(res)
        }
    }}
}

macro_rules! unsigned_impl {
    ( $prim:ident, $type:ident, $len:expr) => {{
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


//------------ Integer -------------------------------------------------------

/// A BER encoded integer.
///
/// As integers are variable length in BER, this type is just a simple wrapper
/// atop the underlying `Bytes` value containing the raw content. A value of
/// this type is a signed integer. If a value is defined as an unsigned
/// integer, i.e., as `INTEGER (0..MAX)`, you should use the sibling type
/// `Unsigned` instead.
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
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Integer(Bytes);

impl Integer {
    pub fn take_from<S: decode::Source>(
        cons: &mut decode::Constructed<S>
    ) -> Result<Self, S::Err> {
        cons.take_primitive_if(Tag::INTEGER, Self::take_content_from)
    }

    pub fn take_content_from<S: decode::Source>(
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

    pub fn i8_from_primitive<S: decode::Source>(
        prim: &mut decode::Primitive<S>
    ) -> Result<i8, S::Err> {
        Self::check_head(prim)?;
        prim.take_u8().map(|x| x as i8)
    }

    pub fn i16_from_primitive<S: decode::Source>(
        prim: &mut decode::Primitive<S>
    ) -> Result<i16, S::Err> {
        signed_impl!(prim, i16, 2)
    }

    pub fn i32_from_primitive<S: decode::Source>(
        prim: &mut decode::Primitive<S>
    ) -> Result<i32, S::Err> {
        signed_impl!(prim, i32, 4)
    }

    pub fn i64_from_primitive<S: decode::Source>(
        prim: &mut decode::Primitive<S>
    ) -> Result<i64, S::Err> {
        signed_impl!(prim, i64, 8)
    }

    pub fn i128_from_primitive<S: decode::Source>(
        prim: &mut decode::Primitive<S>
    ) -> Result<i128, S::Err> {
        signed_impl!(prim, i128, 16)
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
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Unsigned(Bytes);

/// # Decoding and Encoding
impl Unsigned {
    pub fn take_from<S: decode::Source>(
        cons: &mut decode::Constructed<S>
    ) -> Result<Self, S::Err> {
        cons.take_primitive_if(Tag::INTEGER, Self::take_content_from)
    }

    pub fn take_content_from<S: decode::Source>(
        prim: &mut decode::Primitive<S>
    ) -> Result<Self, S::Err> {
        Self::check_head(prim)?;
        prim.take_all().map(Unsigned)
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
        unsigned_impl!(prim, u32, 4)
    }

    pub fn u64_from_primitive<S: decode::Source>(
        prim: &mut decode::Primitive<S>
    ) -> Result<u64, S::Err> {
        unsigned_impl!(prim, u64, 8)
    }

    pub fn u128_from_primitive<S: decode::Source>(
        prim: &mut decode::Primitive<S>
    ) -> Result<u128, S::Err> {
        unsigned_impl!(prim, u128, 16)
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

impl PrimitiveContent for Unsigned {
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

impl From<u32> for Unsigned {
    fn from(n: u32) -> Self {
        Unsigned(n.to_encoded_bytes(Mode::Der))
    }
}


//============ Tests =========================================================

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
