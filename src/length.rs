//! The Length Octets.
//!
//! This is a private module. Its public tiems are re-exported by the parent.

use std::io;
use crate::decode;
use crate::mode::Mode;


//------------ Length -------------------------------------------------------

/// The length octets of an encoded value.
///
/// A length value can either be definite, meaning it provides the actual
/// number of content octets in the value, or indefinite, in which case the
/// content is delimited by a special end-of-value marker.
///
/// # BER Encoding
///
/// The length can be encoded in one of two basic ways. Which is used is
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
/// Under both CER and DER rules, a definite length must be encded in the
/// minimum number of octets.
///
/// # Limitation
///
/// The current implementation is limited to 32 bits for an encoded definite
/// length. This is true even on 64 bit platforms where the `usize` can hold
/// more bits.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Length {
    /// A length value in definite form.
    ///
    /// Provides the actual length of the content in octets.
    Definite(usize),

    /// A length value in indefinite form.
    ///
    /// In this form, the end of a value is determined by a special tag.
    Indefinite
}

impl Length {
    /// Takes a length value from the beginning of a source.
    pub fn take_from<S: decode::Source>(
        source: &mut S,
        mode: Mode
    ) -> Result<Self, S::Err> {
        match source.take_u8()? {
            // Bit 7 clear: other bits are the length
            n if (n & 0x80) == 0 => Ok(Length::Definite(n as usize)),

            // Bit 7 set: other bits are the number of octets that 
            // encode the length. Unless they are all 0, in which case this
            // is the indefinite form.
            0x80 => Ok(Length::Indefinite),
            0x81 => {
                let len = source.take_u8()? as usize;
                if mode.is_ber() || len > 127 {
                    Ok(Length::Definite(len))
                }
                else {
                    Err(decode::Error::Malformed.into())
                }
            }
            0x82 => {
                let len =
                    (source.take_u8()? as usize) << 8 |
                    (source.take_u8()? as usize);
                if mode.is_ber() || len > 255 {
                    Ok(Length::Definite(len))
                }
                else {
                    Err(decode::Error::Malformed.into())
                }
            }
            0x83 => {
                let len =
                    (source.take_u8()? as usize) << 16 |
                    (source.take_u8()? as usize) << 8 |
                    (source.take_u8()? as usize);
                if mode.is_ber() || len > 0xFFFF {
                    Ok(Length::Definite(len))
                }
                else {
                    Err(decode::Error::Malformed.into())
                }
            }
            0x84 => {
                let len =
                    (source.take_u8()? as usize) << 24 |
                    (source.take_u8()? as usize) << 16 |
                    (source.take_u8()? as usize) << 8 |
                    (source.take_u8()? as usize);
                if mode.is_ber() || len > 0x00FF_FFFF {
                    Ok(Length::Definite(len))
                }
                else {
                    Err(decode::Error::Malformed.into())
                }
            }
            _ => {
                // We only implement up to two length bytes for now.
                Err(decode::Error::Unimplemented.into())
            }
        }
    }

    /// Returns whether the length is definite and zero.
    pub fn is_zero(&self) -> bool {
        if let Length::Definite(0) = *self { true }
        else { false }
    }

    /// Returns the length of the encoded representation of the value.
    #[cfg(not(target_pointer_width = "64"))]
    pub fn encoded_len(&self) -> usize {
        match *self {
            Length::Indefinite => 1,
            Length::Definite(len) => {
                if len < 0x80 { 1 }
                else if len < 0x1_00 { 2 }
                else if len < 0x1_0000 { 3 }
                else if len < 0x100_0000 { 4 }
                else {
                    panic!("excessive length")
                }
            }
        }
    }

    /// Returns the length of the encoded representation of the value.
    #[cfg(target_pointer_width = "64")]
    pub fn encoded_len(&self) -> usize {
        match *self {
            Length::Indefinite => 1,
            Length::Definite(len) => {
                if len < 0x80 { 1 }
                else if len < 0x1_00 { 2 }
                else if len < 0x1_0000 { 3 }
                else if len < 0x100_0000 { 4 }
                else if len < 0x1_0000_0000 { 5 }
                else {
                    panic!("excessive length")
                }
            }
        }
    }

    /// Writes the encoded value to a target.
    #[cfg(target_pointer_len = "64")]
    pub fn write_encoded<W: io::Write>(
        &self,
        target: &mut W
    ) -> Result<(), io::Error> {
        match *self {
            Length::Indefinite => {
                let buf = [0x80];
                target.write_all(&buf)
            }
            Length::Definite(len) => {
                if len < 0x80 {
                    let buf = [len as u8];
                    target.write_all(&buf)
                }
                else if len < 0x1_00 {
                    let buf = [0x81, len as u8];
                    target.write_all(&buf)
                }
                else if len < 0x1_0000 {
                    let buf = [
                        0x82, (len >> 8) as u8, len as u8
                    ];
                    target.write_all(&buf)

                }
                else if len < 0x100_0000 {
                    let buf = [
                        0x83, (len >> 16) as u8, (len >> 8) as u8, len as u8
                    ];
                    target.write_all(&buf)
                }
                else if len < 0x1_0000_0000 {
                    let buf = [
                        0x84,
                        (len >> 24) as u8, (len >> 16) as u8,
                        (len >> 8) as u8, len as u8
                    ];
                    target.write_all(&buf)
                }
                else {
                    panic!("excessive length")
                }
            }
        }
    }

    /// Writes the encoded value to a target.
    #[cfg(not(target_pointer_len = "64"))]
    pub fn write_encoded<W: io::Write>(
        &self,
        target: &mut W
    ) -> Result<(), io::Error> {
        match *self {
            Length::Indefinite => {
                let buf = [0x80];
                target.write_all(&buf)
            }
            Length::Definite(len) => {
                if len < 0x80 {
                    let buf = [len as u8];
                    target.write_all(&buf)
                }
                else if len < 0x1_00 {
                    let buf = [0x81, len as u8];
                    target.write_all(&buf)
                }
                else if len < 0x1_0000 {
                    let buf = [
                        0x82, (len >> 8) as u8, len as u8
                    ];
                    target.write_all(&buf)

                }
                else if len < 0x100_0000 {
                    let buf = [
                        0x83, (len >> 16) as u8, (len >> 8) as u8, len as u8
                    ];
                    target.write_all(&buf)
                }
                else {
                    panic!("excessive length")
                }
            }
        }
    }
}
