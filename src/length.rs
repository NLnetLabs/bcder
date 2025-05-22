//! The length octets.
//!
//! This is a private module. [`Length`] and [`LengthOverflow`] are being
//! re-exported by the parent. [`LengthOctets`] is used only internally be
//! the crate.

use std::{error, fmt, io, ops};
use std::cmp::Ordering;
use crate::mode::Mode;
use crate::decode::ReadExt;
use crate::encode::Target;


//------------ Length --------------------------------------------------------

/// A definite length.
///
/// This type is used to represent the length of primitive values and of
/// definite-length constructed values. Like the standard library’s IO
/// module, we are using a `u64` for such lengths since `usize` may not be too
/// small on some platforms. But since slice lengths are using `usize` and
/// conversion between `usize` and `u64` is somewhat complicated, this type
/// wraps a `u64` and provides means for converting.
///
/// # Conversions
///
/// Conversion of values of this type from and to `u64` are obviously always
/// fine. They can be done via the `From<_>` impls or the explicit
/// [`from_u64`][Self::from_u64] and [`to_u64`][Self::to_u64] methods.
///
/// While technically a `usize` could be bigger than a `u64`, there aren’t
/// any architectures that actually use a bigger `usize`, so conversions from
/// `usize` to `Length` are also infallible. They can be done via the
/// `From<_>` impl or the explicit [`from_usize`][Self::from_usize] method.
///
/// A conversion from a `Length` to a `usize` can fail on smaller platforms.
/// An attempt for such a conversion will result in an [`LengthOverflow`]
/// which should be treated as a case of “not implemented”. The conversion can
/// be done via the `TryFrom<_>` impl or the explicit [`try_to_usize`] method.
/// A saturating conversion – providing `usize::MAX` in case of an overflow –
/// is available via [`to_usize_saturating`][Self::to_usize_saturating].
///
/// # Arithmetic
///
/// The type provides support for some basic arithmetic operations. These are
/// both provided through dedicated methods as well as the operators.
///
/// However, unlike the built-in integers, the operators use the checked
/// variant and will panic in debug mode and use the saturating variant in
/// release mode.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
pub struct Length(u64);

/// # Constants
impl Length {
    /// The smallest value that can be represented by this type.
    pub const MIN: Self = Self::from_u64(u64::MIN);

    /// The smallest value that can be represented by this type.
    pub const MAX: Self = Self::from_u64(u64::MAX);

    /// The size of this type in bits.
    pub const BITS: u32 = u64::BITS;

    /// A length of zero.
    ///
    /// This is handy where you would normally use the literal `0`.
    pub const ZERO: Self = Self::from_u64(0);
}


impl Length {
    /// Creates a length from a `u64`.
    pub const fn from_u64(src: u64) -> Self {
        Self(src)
    }

    /// Converts the length into a `u64`.
    pub const fn to_u64(self) -> u64 {
        self.0
    }

    /// Creates a length from a `usize`.
    pub const fn from_usize(src: usize) -> Self {
        Self(src as u64)
    }

    /// Converts the length into a `usize`.
    ///
    /// This conversion can fail on some platforms.
    pub const fn try_to_usize(self) -> Result<usize, LengthOverflow> {
        if self.0 > (usize::MAX as u64) {
            Err(LengthOverflow(()))
        }
        else {
            Ok(self.0 as usize)
        }
    }

    /// Converts the length into a `usize`, saturating in case of overflow.
    ///
    /// If the length is larger than what fits into a `usize`, the method
    /// returns `usize::MAX`.
    pub const fn to_usize_saturating(self) -> usize {
        self.0 as usize
    }

    /// Returns whether the length is zero.
    pub const fn is_zero(self) -> bool {
        self.0 == 0
    }
}


/// # Arithmetic
impl Length {
    /// Checked addition.
    ///
    /// Returns `None` if overflow occured.
    pub const fn checked_add(self, other: Self) -> Option<Self> {
        match self.0.checked_add(other.0) {
            Some(res) => Some(Self(res)),
            None => None,
        }
    }

    /// Checked subtraction.
    ///
    /// Returns `None` if overflow occured.
    pub const fn checked_sub(self, other: Self) -> Option<Self> {
        match self.0.checked_sub(other.0) {
            Some(res) => Some(Self(res)),
            None => None,
        }
    }

    /// Checked multiplication.
    ///
    /// Returns `None` if overflow occured.
    pub const fn checked_mul(self, other: Self) -> Option<Self> {
        match self.0.checked_mul(other.0) {
            Some(res) => Some(Self(res)),
            None => None,
        }
    }

    /// Overflowing addition.
    ///
    /// Returns a tuple of the addition along with a boolean indicating
    /// whether an arithmetic overflow would occur. If an overflow would
    /// have occurred then the wrapped value is returned.
    pub const fn overflowing_add(self, other: Self) -> (Self, bool) {
        let (val, overflow) = self.0.overflowing_add(other.0);
        (Self(val), overflow)
    }

    /// Overflowing subtraction.
    ///
    /// Returns a tuple of the subtraction along with a boolean indicating
    /// whether an arithmetic overflow would occur. If an overflow would
    /// have occurred then the wrapped value is returned.
    pub const fn overflowing_sub(self, other: Self) -> (Self, bool) {
        let (val, overflow) = self.0.overflowing_sub(other.0);
        (Self(val), overflow)
    }

    /// Overflowing multiplication.
    ///
    /// Returns a tuple of the multiplication along with a boolean indicating
    /// whether an arithmetic overflow would occur. If an overflow would
    /// have occurred then the wrapped value is returned.
    pub const fn overflowing_mul(self, other: Self) -> (Self, bool) {
        let (val, overflow) = self.0.overflowing_mul(other.0);
        (Self(val), overflow)
    }

    /// Saturating addition.
    ///
    /// Saturates the numeric bounds instead of overflowing.
    pub const fn saturating_add(self, other: Self) -> Self {
        Self(self.0.saturating_add(other.0))
    }

    /// Saturating subtraction.
    ///
    /// Saturates the numeric bounds instead of overflowing.
    pub const fn saturating_sub(self, other: Self) -> Self {
        Self(self.0.saturating_sub(other.0))
    }

    /// Saturating multiplication.
    ///
    /// Saturates the numeric bounds instead of overflowing.
    pub const fn saturating_mul(self, other: Self) -> Self {
        Self(self.0.saturating_mul(other.0))
    }

    /// Wrapping addition.
    ///
    /// Wraps around the boundary of the type.
    pub const fn wrapping_add(self, other: Self) -> Self {
        Self(self.0.wrapping_add(other.0))
    }

    /// Wrapping subtraction.
    ///
    /// Wraps around the boundary of the type.
    pub const fn wrapping_sub(self, other: Self) -> Self {
        Self(self.0.wrapping_sub(other.0))
    }

    /// Wrapping multiplication.
    ///
    /// Wraps around the boundary of the type.
    pub const fn wrapping_mul(self, other: Self) -> Self {
        Self(self.0.wrapping_mul(other.0))
    }

    /// Strict addition.
    ///
    /// Panics if overflow occures.
    #[allow(clippy::expect_used)]
    pub const fn strict_add(self, other: Self) -> Self {
        Self(
            self.0.checked_add(
                other.0
            ).expect("attempt to add with overflow")
        )
    }

    /// Strict subtraction.
    ///
    /// Panics if overflow occures.
    #[allow(clippy::expect_used)]
    pub const fn strict_sub(self, other: Self) -> Self {
        Self(
            self.0.checked_sub(
                other.0
            ).expect("attempt to subtract with overflow")
        )
    }

    /// Strict multiplication.
    ///
    /// Panics if overflow occures.
    #[allow(clippy::expect_used)]
    pub const fn strict_mul(self, other: Self) -> Self {
        Self(
            self.0.checked_mul(
                other.0
            ).expect("attempt to multiply with overflow")
        )
    }
}


/// # Encoding
impl Length {
    const LEN: usize = 0u64.to_ne_bytes().len();

    fn encoded_len(self) -> Length {
        if self.0 > 0x7F {
            let idx = self.encoded_start_idx();
            debug_assert!(idx < Self::LEN);

            Length::from_usize(Self::LEN - idx + 1)
        }
        else {
            Length::from_u64(1)
        }
    }

    fn write_encoded<T: Target>(
        self, target: &mut T
    ) -> Result<(), T::Error> {
        if self.0 > 0x7F {
            let idx = self.encoded_start_idx();
            debug_assert!(idx < Self::LEN);

            // LEN will never be greater than 126 bytes. Also, `idx` won’t be
            // greater than LEN, so the subtraction here is fine.
            target.write_all(&[((Self::LEN - idx) | 0x80) as u8])?;

            // Panic: idx can’t be bigger than LEN, so this can’t panic.
            #[allow(clippy::indexing_slicing)]
            target.write_all(
                &self.0.to_be_bytes()[idx..]
            )
        }
        else {
            target.write_all(&[self.0 as u8])
        }
    }

    /// Returns the index of the first non-zero octet of `len`.
    fn encoded_start_idx(self) -> usize {
        (self.0.leading_zeros().next_multiple_of(8) / 8) as usize
    }
}


//--- From and TryFrom

impl From<u8> for Length {
    fn from(src: u8) -> Self {
        Self::from_u64(src.into())
    }
}

impl From<u64> for Length {
    fn from(src: u64) -> Self {
        Self::from_u64(src)
    }
}

impl From<Length> for u64 {
    fn from(src: Length) -> Self {
        src.to_u64()
    }
}

impl From<usize> for Length {
    fn from(src: usize) -> Self {
        Self::from_usize(src)
    }
}

impl TryFrom<Length> for usize {
    type Error = LengthOverflow;

    fn try_from(src: Length) -> Result<Self, Self::Error> {
        src.try_to_usize()
    }
}


//--- Arithmetic operators
//

impl ops::Add<Self> for Length {
    type Output = Self;

    fn add(self, other: Self) -> Self {
        if cfg!(debug_assertions) {
            self.strict_add(other)
        }
        else {
            self.saturating_add(other)
        }
    }
}

impl ops::Add<usize> for Length {
    type Output = Self;

    fn add(self, other: usize) -> Self {
        self.add(Length::from(other))
    }
}

impl ops::Add<u64> for Length {
    type Output = Self;

    fn add(self, other: u64) -> Self {
        self.add(Length::from(other))
    }
}

// We need Add<i32> since sometimes Rust insists on bare integer literals
// being i32.
impl ops::Add<i32> for Length {
    type Output = Self;

    fn add(self, other: i32) -> Self {
        if other >= 0 {
            self.add(other as u64)
        }
        else {
            ops::Sub::sub(self, other as u64)
        }
    }
}

impl ops::AddAssign<Self> for Length {
    fn add_assign(&mut self, other: Self) {
        *self = *self + other
    }
}

impl ops::AddAssign<u64> for Length {
    fn add_assign(&mut self, other: u64) {
        self.add_assign(Length::from(other))
    }
}

impl ops::AddAssign<usize> for Length {
    fn add_assign(&mut self, other: usize) {
        self.add_assign(Length::from(other))
    }
}

impl ops::Sub<Self> for Length {
    type Output = Self;

    fn sub(self, other: Self) -> Self {
        if cfg!(debug_assertions) {
            self.strict_sub(other)
        }
        else {
            self.saturating_sub(other)
        }
    }
}

impl ops::Sub<u64> for Length {
    type Output = Self;

    fn sub(self, other: u64) -> Self {
        self.sub(Length::from(other))
    }
}

impl ops::Sub<usize> for Length {
    type Output = Self;

    fn sub(self, other: usize) -> Self {
        self.sub(Length::from(other))
    }
}

impl ops::SubAssign<Self> for Length {
    fn sub_assign(&mut self, other: Self) {
        *self = *self - other
    }
}

impl ops::SubAssign<u64> for Length {
    fn sub_assign(&mut self, other: u64) {
        self.sub_assign(Length::from(other))
    }
}

impl ops::SubAssign<usize> for Length {
    fn sub_assign(&mut self, other: usize) {
        self.sub_assign(Length::from(other))
    }
}

impl ops::Mul<Self> for Length {
    type Output = Self;

    fn mul(self, other: Self) -> Self {
        if cfg!(debug_assertions) {
            self.strict_mul(other)
        }
        else {
            self.saturating_mul(other)
        }
    }
}

impl ops::Mul<u64> for Length {
    type Output = Self;

    fn mul(self, other: u64) -> Self {
        self.mul(Length::from(other))
    }
}

impl ops::Mul<usize> for Length {
    type Output = Self;

    fn mul(self, other: usize) -> Self {
        self.mul(Length::from(other))
    }
}

impl ops::MulAssign<Self> for Length {
    fn mul_assign(&mut self, other: Self) {
        *self = *self * other
    }
}

impl ops::MulAssign<u64> for Length {
    fn mul_assign(&mut self, other: u64) {
        self.mul_assign(Length::from(other))
    }
}

impl ops::MulAssign<usize> for Length {
    fn mul_assign(&mut self, other: usize) {
        self.mul_assign(Length::from(other))
    }
}


//--- PartialEq and PartialOrd
//
// Derived for Self as other.

impl PartialEq<u64> for Length {
    fn eq(&self, other: &u64) -> bool {
        self.0.eq(other)
    }
}

impl PartialEq<usize> for Length {
    fn eq(&self, other: &usize) -> bool {
        self.eq(&Length::from(*other))
    }
}

impl PartialEq<Length> for u64 {
    fn eq(&self, other: &Length) -> bool {
        self.eq(&other.0)
    }
}

impl PartialOrd<u64> for Length {
    fn partial_cmp(&self, other: &u64) -> Option<Ordering> {
        self.0.partial_cmp(other)
    }
}

impl PartialOrd<usize> for Length {
    fn partial_cmp(&self, other: &usize) -> Option<Ordering> {
        self.partial_cmp(&Length::from(*other))
    }
}

impl PartialOrd<Length> for u64 {
    fn partial_cmp(&self, other: &Length) -> Option<Ordering> {
        self.partial_cmp(&other.0)
    }
}


//--- Display

impl fmt::Display for Length {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.0.fmt(f)
    }
}


//------------ LengthOctets -------------------------------------------------

/// The length octets of an encoded value.
///
/// A length value can either be definite, meaning it provides the actual
/// number of content octets in the value, or indefinite, in which case the
/// content is delimited by a special end-of-value marker.
///
/// # BER Encoding
///
/// The length can be encoded in one of two basic ways. Which one is used is
/// determined by the most significant bit of the first octet. If it is not
/// set, the length octets is one octet long and the remaining bits of this
/// first octet provide the definite length. Thus, if the first octet is
/// less than 128, it provides the definite length already.
///
/// If the most significant bit is set, the remaining bits of the first
/// octet specify the number of octets that follow to encode the actual
/// length. If they specify that there are zero more octets, i.e., the
/// value of the first octet is 128, the length is indefinite. Otherwise,
/// those following octets give the big-endian encoding of the definite
/// length of the content octets.
///
/// Under both CER and DER rules, a definite length must be encoded in the
/// minimum number of octets.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct LengthOctets {
    /// The length.
    ///
    /// If this is `None`, the length is indefinite. Otherwise it is definite
    /// with the given value.
    length: Option<Length>,
}

impl LengthOctets {
    /// Creates a new length from the given optional length.
    ///
    /// If the length is `None`, creates an indefinite length value.
    pub fn new(length: Option<Length>) -> Self {
        Self { length }
    }

    /// Returns the length if it is definite.
    pub fn definite(self) -> Option<Length> {
        self.length
    }

    /// Parses a length from a source.
    pub fn read<M: Mode>(
        source: &mut impl io::Read
    ) -> Result<Self, io::Error> {
        // This branching should be optimized away after monomorphisation.
        if M::IS_RESTRICTED {
            Self::read_restricted(source)
        }
        else {
            Self::read_relaxed(source)
        }
    }

    /// Reads a length from a reader in BER mode.
    fn read_relaxed(reader: &mut impl io::Read) -> Result<Self, io::Error> {
        // Determine the length of the extra octets or return early.
        let mut len = match FirstOctet::read(reader)? {
            FirstOctet::Single(res) => return Ok(res),
            FirstOctet::Multi(len) => len,
        };

        // If we have more octets than fit into a u64, the excess octets need
        // to be zero or the length is too big.
        while len > Length::LEN {
            if reader.read_u8()? != 0 {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    "excessive length"
                ))
            }
            len -= 1;
        }

        // Now we have Length::LEN octets or less and can read them into
        // a byte array.
        let res = if len > 0 {
            let mut res = [0u8; Length::LEN];
            // Safety: len is <= than Length::LEN (see loop above).
            #[allow(clippy::indexing_slicing)]
            reader.read_exact(&mut res[(Length::LEN - len)..])?;
            res
        }
        else {
            Default::default()
        };
        Ok(Self::new(Some(u64::from_be_bytes(res).into())))
    }

    /// Reads a length from a reader in BER mode.
    fn read_restricted(
        reader: &mut impl io::Read
    ) -> Result<Self, io::Error> {
        // The difference to the BER case is the second octet can’t be zero
        // and it can’t be less that 0x80 if it is the last octet as well.
        // In both cases, there is a shorter encoding.
        //
        // This means we can skip reading zeros until the length is fine. It
        // has to be fine from the beginning.

        // Determine the length of the extra octets or return early.
        let len = match FirstOctet::read(reader)? {
            FirstOctet::Single(res) => return Ok(res),
            FirstOctet::Multi(len) => len,
        };

        if len > Length::LEN {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData, "excessive length"
            ))
        }
        
        let mut res = [0u8; Length::LEN];
        // Safety: len is <= than Length::LEN (see check above).
        #[allow(clippy::indexing_slicing)]
        reader.read_exact(&mut res[(Length::LEN - len)..])?;
        let res = u64::from_be_bytes(res);

        // Check that res wouldn’t have fit into the short form
        if res < 0x80 {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,"illegal length in CER/DER"
            ))
        }

        Ok(Self::new(Some(res.into())))
    }

    /// Read the length of an end-of-contents value.
    ///
    /// X.690 says that the length is a single zero, i.e., it has to be a
    /// definite length zero in short form. This function enforces that.
    pub fn read_end_of_contents(
        reader: &mut impl io::Read
    ) -> Result<(), io::Error> {
        match reader.read_u8()? {
            0 => Ok(()),
            0x80 => {
                Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    "indefinite length in end-of-contents value"
                ))
            }
            0xFF => {
                Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    "illegal length octets"
                ))
            }
            n if (n & 0x80) != 0 => {
                Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    "long form length octets in end-of-contents value"
                ))
            }
            _ => {
                Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    "non-zero length end-of-contents value"
                ))
            }
        }
    }

    /// Returns the length of the encoded representation of the value.
    ///
    /// The returned value is always the same, independent of the mode.
    pub fn encoded_len(self) -> Length {
        match self.length {
            Some(definite) => definite.encoded_len(),
            None => Length::from_u64(1),
        }
    }

    /// Writes the encoded length to the given writer.
    ///
    /// The written data is always the same, independent of the mode.
    pub fn write_encoded<T: Target>(
        self, target: &mut T
    ) -> Result<(), T::Error> {
        match self.length {
            Some(definite) => definite.write_encoded(target),
            None => target.write_all(&[0x80]),
        }
    }
}


//------------ FirstOctet ---------------------------------------------------

/// The first octet of the encoded length.
enum FirstOctet {
    /// The first octet is a length in and of itself.
    Single(LengthOctets),

    /// The first octet indicates the number of octets to follow.
    Multi(usize),
}

impl FirstOctet {
    /// Look at the first octet and check what it means.
    fn read(reader: &mut impl io::Read) -> Result<Self, io::Error> {
        match reader.read_u8()? {
            // Bit 7 clear: single.
            n if (n & 0x80) == 0 => {
                Ok(Self::Single(LengthOctets::new(Some(n.into()))))
            }

            // 0x80: indefinite.
            0x80 => Ok(Self::Single(LengthOctets::new(None))),

            // 0xFF: illegal.
            0xFF => {
                Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    "illegal length octets"
                ))
            }

            // anything else: clear left bit, number of octets.
            n => Ok(Self::Multi((n & 0x7F) as usize))
        }
    }
}


//============ Error Types ===================================================

//------------ LengthOverflow -----------------------------------------------

/// A length was too large to be supported.
#[derive(Clone, Debug)]
pub struct LengthOverflow(());

impl fmt::Display for LengthOverflow {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str("length overflow")
    }
}

impl error::Error for LengthOverflow { }


//============ Tests =========================================================

#[cfg(test)]
mod test {
    use crate::mode::{Ber, Der};
    use super::*;

    #[test]
    fn ber_take_from() {
        fn take_from<const N: usize>(
            src: &[u8; N]
        ) -> Result<Option<u64>, io::Error> {
            let mut src = src.as_ref();
            let res = LengthOctets::read::<Ber>(&mut src)?;
            if src.is_empty() {
                Ok(res.definite().map(Into::into))
            }
            else {
                Err(io::Error::new(io::ErrorKind::InvalidData, "TRAILING"))
            }
        }

        assert_eq!(take_from(b"\x00").unwrap(), Some(0x00));
        assert_eq!(take_from(b"\x12").unwrap(), Some(0x12));
        assert_eq!(take_from(b"\x7f").unwrap(), Some(0x7f));
        assert_eq!(take_from(b"\x80").unwrap(), None);
        assert_eq!(take_from(b"\x81\x00").unwrap(), Some(0));
        assert_eq!(take_from(b"\x81\xF0").unwrap(), Some(0xF0));
        assert_eq!(take_from(b"\x82\x00\x00").unwrap(), Some(0));
        assert_eq!(take_from(b"\x82\xF0\x0E").unwrap(), Some(0xF00E));
        assert_eq!(take_from(b"\x82\x00\x0E").unwrap(), Some(0x0E));
        assert!(take_from(b"\xFF").is_err());
    }

    #[test]
    fn der_take_from() {
        fn take_from<const N: usize>(
            src: &[u8; N]
        ) -> Result<Option<u64>, io::Error> {
            let mut src = src.as_ref();
            let res = LengthOctets::read::<Der>(&mut src)?;
            if src.is_empty() {
                Ok(res.definite().map(Into::into))
            }
            else {
                Err(io::Error::new(io::ErrorKind::InvalidData, "TRAILING"))
            }
        }

        assert_eq!(take_from(b"\x00").unwrap(), Some(0x00));
        assert_eq!(take_from(b"\x12").unwrap(), Some(0x12));
        assert_eq!(take_from(b"\x7f").unwrap(), Some(0x7f));
        assert_eq!(take_from(b"\x80").unwrap(), None);
        assert!(take_from(b"\x81\x00").is_err());
        assert!(take_from(b"\x81\x7f").is_err());
        assert_eq!(take_from(b"\x81\x80").unwrap(), Some(0x80));
        assert_eq!(take_from(b"\x81\xF0").unwrap(), Some(0xF0));
        assert!(take_from(b"\x82\x00\x00").is_err());
        assert_eq!(take_from(b"\x82\xF0\x0E").unwrap(), Some(0xF00E));
        assert!(take_from(b"\x82\x00\x0E").is_err());
        assert!(take_from(b"\xFF").is_err());
    }

    /*
    #[test]
    fn encode() {
        fn step<const N: usize>(l: Option<usize>, res: &[u8; N]) {
            let l = LengthOctets::<Ber>::new(l);
            let mut vec = Vec::new();
            l.append_encoded(&mut vec);
            assert_eq!(
                vec.as_slice(), res.as_ref(),
                "append failed for {l:?}: {vec:?}"
            );

            let mut vec = Vec::new();
            l.write_encoded(&mut vec).unwrap();
            assert_eq!(
                vec.as_slice(), res.as_ref(),
                "write failed for {l:?}: {vec:?}"
            );
        }

        step(None, b"\x80");
        step(Some(0), b"\x00");
        step(Some(0x12), b"\x12");
        step(Some(0x7f), b"\x7f");
        step(Some(0x80), b"\x81\x80");
        step(Some(0xdead), b"\x82\xde\xad");
    }
    */
}

