//! PrimitiveContent and related types.
//!
//! This is an internal module. Its public types are re-exported by the
//! parent.

use std::io;
use bytes::{BufMut, Bytes, BytesMut};
use crate::length::Length;
use crate::mode::Mode;
use crate::tag::Tag;
use super::values::Values;


//------------ PrimitiveContent ----------------------------------------------

/// A type that is encoded as a primitive value.
///
/// This trait should be implemented for types that use primitive encoding.
/// It defines, how the content octets of a single primitive value containing
/// a value of the type are to be created. As a consequence, these types
/// gain the [`encode`] and [`encode_as`] methods from their implementation
/// of this trait.
///
/// Note that the trait requires implementing types to be `Copy` to
/// avoid unnecessary lifetime parameters on the encoder type. For types that
/// aren’t `Copy`, `PrimitiveContent` should be implemented on a reference to
/// the type instead.
///
/// [`encode`]: #tymethod.encode
/// [`encode_as`]: #tymethod.encode_as
pub trait PrimitiveContent: Sized {
    /// The natural tag of an encoded value of this type.
    const TAG: Tag;

    /// Returns the length of the encoded content of this type.
    fn encoded_len(&self, mode: Mode) -> usize;

    /// Writes the encoded content to a writer.
    fn write_encoded<W: io::Write>(
        &self,
        mode: Mode,
        target: &mut W
    ) -> Result<(), io::Error>;

    /// Encodes the value to bytes (useful when you need to sign a structure)
    fn to_encoded_bytes(&self, mode: Mode) -> Bytes {
        let l = self.encoded_len(mode);
        let mut w = BytesMut::with_capacity(l).writer();
        self.write_encoded(mode, &mut w).unwrap();
        w.into_inner().freeze()
    }

    /// Returns a value encoder for this content using the natural tag.
    ///
    /// This is identical to `self.encode_as(Self::TAG)`
    fn encode(self) -> Primitive<Self> {
        self.encode_as(Self::TAG)
    }

    /// Returns a value encoder for this content using the given tag.
    ///
    /// The returned value is a content encoder that produces a single
    /// primitive BER encoded value. The tag for this value is explicitely
    /// given via the `tag` argument.
    fn encode_as(self, tag: Tag) -> Primitive<Self> {
        Primitive { tag, prim: self }
    }

    /// Returns a value encoder for a reference using the natural tag.
    fn encode_ref(&self) -> Primitive<&Self> {
        self.encode_ref_as(Self::TAG)
    }

    /// Returns a value encoder for a reference using the given tag.
    fn encode_ref_as(&self, tag: Tag) -> Primitive<&Self> {
        Primitive { tag, prim: self }
    }
}

//--- Blanket impls

impl<'a, T: PrimitiveContent> PrimitiveContent for &'a T {
    const TAG: Tag = T::TAG;

    fn encoded_len(&self, mode: Mode) -> usize {
        (*self).encoded_len(mode)
    }

    fn write_encoded<W: io::Write>(
        &self,
        mode: Mode,
        target: &mut W
    ) -> Result<(), io::Error> {
        (*self).write_encoded(mode, target)
    }
}


//--- impl for built-in types

impl PrimitiveContent for u8 {
    const TAG: Tag = Tag::INTEGER;

    fn encoded_len(&self, _: Mode) -> usize {
        if *self > 0x7F { 2 }
        else { 1 }
    }

    fn write_encoded<W: io::Write>(
        &self,
        _: Mode,
        target: &mut W
    ) -> Result<(), io::Error> {
        if *self > 0x7F {
            target.write_all(&[0])?;
        }
        target.write_all(&[*self])?;
        Ok(())
    }
}

macro_rules! unsigned_content {
    ( $type:ident, $len:expr) => {
        impl PrimitiveContent for $type {
            const TAG: Tag = Tag::INTEGER;

            fn encoded_len(&self, _: Mode) -> usize {
                if *self == 0 {
                    1
                }
                else {
                    let zeros = self.leading_zeros() as usize;
                    if zeros % 8 == 0 {
                        $len - (zeros >> 3) + 1
                    }
                    else {
                        $len - (zeros >> 3)
                    }
                }
            }

            fn write_encoded<W: io::Write>(
                &self,
                _: Mode,
                target: &mut W
            ) -> Result<(), io::Error> {
                if *self == 0 {
                    target.write_all(&[0x00])?;
                }
                else {
                    let mut val = self.swap_bytes();
                    let mut i = 0;
                    while i < $len {
                        if val as u8 != 0 {
                            break
                        }
                        val >>= 8;
                        i += 1
                    }
                    if val & 0x80 != 0 {
                        target.write_all(&[0x00])?;
                    }
                    while i < $len {
                        target.write_all(&[val as u8])?;
                        val >>= 8;
                        i += 1
                    }
                }
                Ok(())
            }
        }
    }
}

unsigned_content!(u16, 2);
unsigned_content!(u32, 4);
unsigned_content!(u64, 8);
unsigned_content!(u128, 16);


impl PrimitiveContent for i8 {
    const TAG: Tag = Tag::INTEGER;

    fn encoded_len(&self, _: Mode) -> usize {
        1
    }

    fn write_encoded<W: io::Write>(
        &self,
        _: Mode,
        target: &mut W
    ) -> Result<(), io::Error> {
        target.write_all(&[*self as u8])?;
        Ok(())
    }
}

macro_rules! signed_content {
    ($type:ident, $len:expr) => {
        impl PrimitiveContent for $type {
            const TAG: Tag = Tag::INTEGER;

            fn encoded_len(&self, _: Mode) -> usize {
                if *self == 0 || *self == -1 {
                    return 1
                }
                let zeros = if *self < 0 {
                    (!*self).leading_zeros() as usize
                }
                else {
                    self.leading_zeros() as usize
                };
                if zeros.trailing_zeros() >= 3 { // i.e., zeros % 8 == 1
                    $len + 1 - (zeros >> 3)
                }
                else {
                    $len - (zeros >> 3)
                }
            }

            fn write_encoded<W: io::Write>(
                &self,
                _: Mode,
                target: &mut W
            ) -> Result<(), io::Error> {
                if *self == 0 {
                    target.write_all(&[0x00])?;
                }
                else if *self == -1 {
                    target.write_all(&[0xFF])?;
                }
                else if *self < 0 {
                    let mut val = self.swap_bytes();
                    let mut i = 0;
                    // Skip over leading 0xFF.
                    while i < $len {
                        if val as u8 != 0xFF {
                            break
                        }
                        val >>= 8;
                        i += 1;
                    }
                    // If the first non-0xFF doesn’t have the left-most bit
                    // set, we need an 0xFF for the sign.
                    if val & 0x80 != 0x80 {
                        target.write_all(&[0xFF])?;
                    }
                    while i < $len {
                        target.write_all(&[val as u8])?;
                        val >>= 8;
                        i += 1
                    }
                }
                else {
                    let mut val = self.swap_bytes();
                    let mut i = 0;
                    // Skip over leading zero bytes.
                    while i < $len {
                        if val as u8 != 0x00 {
                            break
                        }
                        val >>= 8;
                        i += 1;
                    }
                    // If the first non-zero has the left-most bit
                    // set, we need an 0x00 for the sign.
                    if val & 0x80 == 0x80 {
                        target.write_all(&[0x00])?;
                    }
                    while i < $len {
                        target.write_all(&[val as u8])?;
                        val >>= 8;
                        i += 1
                    }
                }
                Ok(())
            }
        }
    }
}

signed_content!(i16, 2);
signed_content!(i32, 4);
signed_content!(i64, 8);
signed_content!(i128, 16);


impl PrimitiveContent for () {
    const TAG: Tag = Tag::NULL;

    fn encoded_len(&self, _: Mode) -> usize {
        0
    }

    fn write_encoded<W: io::Write>(
        &self,
        _: Mode,
        _: &mut W
    ) -> Result<(), io::Error> {
        Ok(())
    }
}

impl PrimitiveContent for bool {
    const TAG: Tag = Tag::BOOLEAN;

    fn encoded_len(&self, _: Mode) -> usize {
        1
    }

    fn write_encoded<W: io::Write>(
        &self,
        _: Mode,
        target: &mut W
    ) -> Result<(), io::Error> {
        if *self {
            target.write_all(&[0xff])
        }
        else {
            target.write_all(&[0])
        }
    }
}

impl<'a> PrimitiveContent for &'a [u8] {
    const TAG: Tag = Tag::OCTET_STRING;

    fn encoded_len(&self, _: Mode) -> usize {
        self.len()
    }

    fn write_encoded<W: io::Write>(
        &self,
        _: Mode,
        target: &mut W
    ) -> Result<(), io::Error> {
        target.write_all(self)
    }
}


//------------ Primitive -----------------------------------------------------

/// A value encoder for primitively encoded types.
///
/// This type is returned by [`PrimitiveContent::encode`] and
/// [`PrimitiveContent::encode_as`].
///
/// [`PrimitiveContent::encode`]: trait.PrimitiveContent.html#tymethod_encode
/// [`PrimitiveContent::encode_as`]: trait.PrimitiveContent.html#tymethod_encode_as
pub struct Primitive<P> {
    /// The tag for this value.
    tag: Tag,

    /// The primitive content.
    prim: P
}

impl<P: PrimitiveContent> Values for Primitive<P> {
    fn encoded_len(&self, mode: Mode) -> usize {
        let len = self.prim.encoded_len(mode);
        self.tag.encoded_len()
        + Length::Definite(len).encoded_len()
        + len
    }

    fn write_encoded<W: io::Write>(
        &self,
        mode: Mode,
        target: &mut W
    ) -> Result<(), io::Error> {
        self.tag.write_encoded(false, target)?;
        Length::Definite(self.prim.encoded_len(mode)).write_encoded(target)?;
        self.prim.write_encoded(mode, target)
    }
}


//============ Tests =========================================================

#[cfg(test)]
mod test {
    use super::*;

    fn test_der<T: PrimitiveContent>(value: T, expected: &[u8]) {
        assert_eq!(value.encoded_len(Mode::Der), expected.len());
        let mut target = Vec::new();
        value.write_encoded(Mode::Der, &mut target).unwrap();
        assert_eq!(target, expected);
    }

    #[test]
    fn encode_u32() {
        test_der(0u32, b"\0");
        test_der(0x12u32, b"\x12");
        test_der(0xf2u32, b"\0\xf2");
        test_der(0x1234u32, b"\x12\x34");
        test_der(0xf234u32, b"\0\xf2\x34");
        test_der(0x123400u32, b"\x12\x34\x00");
        test_der(0xf23400u32, b"\0\xf2\x34\x00");
        test_der(0x12345678u32, b"\x12\x34\x56\x78");
        test_der(0xA2345678u32, b"\x00\xA2\x34\x56\x78");
    }

    #[test]
    fn encode_i32() {
        test_der(0i32, b"\0");
        test_der(0x12i32, b"\x12");
        test_der(0xf2i32, b"\0\xf2");
        test_der(0x1234i32, b"\x12\x34");
        test_der(0xf234i32, b"\0\xf2\x34");
        test_der(0x123400i32, b"\x12\x34\x00");
        test_der(0xf23400i32, b"\0\xf2\x34\x00");
        test_der(0x12345678i32, b"\x12\x34\x56\x78");
        test_der(-1i32, b"\xFF");
        test_der(-0xF0i32, b"\xFF\x10");
        test_der(-0xF000i32, b"\xFF\x10\x00");
        test_der(-12000i32, b"\xD1\x20");
        test_der(-1200000i32, b"\xED\xB0\x80");
    }
}
