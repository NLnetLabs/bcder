
use std::io;
use super::length::Length;
use super::mode::Mode;
use super::tag::Tag;


//============ Traits ========================================================

//------------ Values --------------------------------------------------------

/// A trait for a value encoder.
///
/// A value encoder is a type that knows how to encode itself into a
/// sequence of BER encoded values. While you can impl this trait for your
/// type manually, in practice it is often easier to define a method called
/// `encode` and let it return some dedicated value encoder type from this
/// module.
///
/// A type implementing this trait should encodes itself into one or more
/// BER values. That is, the type becomes the content or part of the content
/// of a constructed value.
pub trait Values {
    /// Returns the length of the encoded values for the given mode.
    fn encoded_len(&self, mode: Mode) -> usize;

    /// Encodes the values in the given mode and writes them to `target`.
    fn write_encoded<W: io::Write>(
        &self,
        mode: Mode,
        target: &mut W
    ) -> Result<(), io::Error>;
}


//--- Blanket impls

impl<'a, T: Values> Values for &'a T {
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


//--- Impls for Tuples

impl<T: Values, U: Values> Values for (T, U) {
    fn encoded_len(&self, mode: Mode) -> usize {
        self.0.encoded_len(mode) + self.1.encoded_len(mode)
    }

    fn write_encoded<W: io::Write>(
        &self,
        mode: Mode,
        target: &mut W
    ) -> Result<(), io::Error> {
        self.0.write_encoded(mode, target)?;
        self.1.write_encoded(mode, target)?;
        Ok(())
    }
}

impl<R: Values, S: Values, T: Values> Values for (R, S, T) {
    fn encoded_len(&self, mode: Mode) -> usize {
        self.0.encoded_len(mode) + self.1.encoded_len(mode)
        + self.2.encoded_len(mode)
    }

    fn write_encoded<W: io::Write>(
        &self,
        mode: Mode,
        target: &mut W
    ) -> Result<(), io::Error> {
        self.0.write_encoded(mode, target)?;
        self.1.write_encoded(mode, target)?;
        self.2.write_encoded(mode, target)?;
        Ok(())
    }
}

impl<R: Values, S: Values, T: Values, U: Values> Values for (R, S, T, U) {
    fn encoded_len(&self, mode: Mode) -> usize {
        self.0.encoded_len(mode) + self.1.encoded_len(mode)
        + self.2.encoded_len(mode) + self.3.encoded_len(mode)
    }

    fn write_encoded<W: io::Write>(
        &self,
        mode: Mode,
        target: &mut W
    ) -> Result<(), io::Error> {
        self.0.write_encoded(mode, target)?;
        self.1.write_encoded(mode, target)?;
        self.2.write_encoded(mode, target)?;
        self.3.write_encoded(mode, target)?;
        Ok(())
    }
}


//--- Impl for Option

impl<V: Values> Values for Option<V> {
    fn encoded_len(&self, mode: Mode) -> usize {
        match self {
            Some(v) => v.encoded_len(mode),
            None => 0
        }
    }

    fn write_encoded<W: io::Write>(
        &self,
        mode: Mode,
        target: &mut W
    ) -> Result<(), io::Error> {
        match self {
            Some(v) => v.write_encoded(mode, target),
            None => Ok(())
        }
    }
}


//--- Impl for Vec

impl<V: Values> Values for Vec<V> {

    fn encoded_len(&self, mode: Mode) -> usize {
        self.iter().fold(0, |l, i| { l + i.encoded_len(mode)} )
    }

    fn write_encoded<W: io::Write>(&self, mode: Mode, target: &mut W)
        -> Result<(), io::Error>
    {
        for i in self {
            i.write_encoded(mode, target)?;
        };
        Ok(())
    }
}



//------------ PrimitiveContent ----------------------------------------------

/// A trait for the content of a primitive value.
pub trait PrimitiveContent {
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

    /// Returns a value encoder for this content using the given tag.
    ///
    /// The returned value is a content encoder that produces a single
    /// primitive BER encoded value. The tag for this value is explicitely
    /// given via the `tag` argument.
    fn tagged(&self, tag: Tag) -> Primitive<Self> {
        Primitive { tag, prim: self }
    }

    /// Returns a value encoder for this content using the natural tag.
    ///
    /// This is like `tagged` except that it uses `Self::TAG` as the tag.
    fn value(&self) -> Primitive<Self> {
        self.tagged(Self::TAG)
    }
}


//--- impl for built-in types

impl PrimitiveContent for u32 {
    const TAG: Tag = Tag::INTEGER;

    fn encoded_len(&self, _: Mode) -> usize {
        ((32 - self.leading_zeros()) / 8 + 1) as usize
    }

    fn write_encoded<W: io::Write>(
        &self,
        _: Mode,
        target: &mut W
    ) -> Result<(), io::Error> {
        if *self < 0xFF {
            target.write_all(&[*self as u8])
        }
        else if *self < 0xFFFF {
            target.write_all(&[
                (*self >> 8) as u8,
                *self as u8
            ])
        }
        else if *self < 0xFF_FFFF {
            target.write_all(&[
                (*self >> 16) as u8,
                (*self >> 8) as u8,
                *self as u8
            ])
        }
        else if *self < 0xFFFF_FFFF {
            target.write_all(&[
                (*self >> 24) as u8,
                (*self >> 16) as u8,
                (*self >> 8) as u8,
                *self as u8
            ])
        }
        else {
            target.write_all(&[0, 0xFF, 0xFF, 0xFF, 0xFF])
        }
    }
}

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
        match self {
            true => target.write(&[0xff]).unwrap(),
            false => target.write(&[0]).unwrap(),
        };
        Ok(())
    }
}

//============ Standard Types ================================================

/// A value encoder for a single constructed value.
pub struct Constructed<V> {
    /// The tag of the value.
    tag: Tag,

    /// A value encoder for the content of the value.
    inner: V,
}

impl<V> Constructed<V> {
    pub fn new(tag: Tag, inner: V) -> Self {
        Constructed { tag, inner }
    }
}

impl<V: Values> Values for Constructed<V> {
    fn encoded_len(&self, mode: Mode) -> usize {
        let len = self.inner.encoded_len(mode);
        let len = len + match mode {
            Mode::Ber | Mode::Der => {
                Length::Definite(len).encoded_len()
            }
            Mode::Cer => {
                Length::Indefinite.encoded_len()
                + EndOfValue.encoded_len(mode)
            }
        };
        self.tag.encoded_len() + len
    }

    fn write_encoded<W: io::Write>(
        &self,
        mode: Mode,
        target: &mut W
    ) -> Result<(), io::Error> {
        self.tag.write_encoded(true, target)?;
        match mode {
            Mode::Ber | Mode::Der => {
                Length::Definite(self.inner.encoded_len(mode))
                    .write_encoded(target)?;
                self.inner.write_encoded(mode, target)
            }
            Mode::Cer => {
                Length::Indefinite.write_encoded(target)?;
                self.inner.write_encoded(mode, target)?;
                EndOfValue.write_encoded(mode, target)
            }
        }
    }
}


//------------ Choice2 -------------------------------------------------------

/// A value encoder for a two-variant enum.
///
/// Instead of implementing `Values` for an enum manually, you can just
/// define a method `encode` that returns a value of this type.
pub enum Choice2<L, R> {
    /// The first choice.
    One(L),

    /// The second choice.
    Two(R)
}

impl<L: Values, R: Values> Values for Choice2<L, R> {
    fn encoded_len(&self, mode: Mode) -> usize {
        match *self {
            Choice2::One(ref inner) => inner.encoded_len(mode),
            Choice2::Two(ref inner) => inner.encoded_len(mode),
        }
    }

    fn write_encoded<W: io::Write>(
        &self,
        mode: Mode,
        target: &mut W
    ) -> Result<(), io::Error> {
        match *self {
            Choice2::One(ref inner) => inner.write_encoded(mode, target),
            Choice2::Two(ref inner) => inner.write_encoded(mode, target),
        }
    }
}


/// A wrapper for an iterator of values.
///
/// The wrapper is needed because a blanket impl on any iterator type is
/// currently not possible.
///
/// Note that `T` needs to be clone because we need to be able to restart
/// iterating at the beginning.
pub struct Iter<T>(pub T);

impl<T> Values for Iter<T>
where T: Clone + Iterator, <T as Iterator>::Item: Values {
    fn encoded_len(&self, mode: Mode) -> usize {
        self.0.clone().map(|item| item.encoded_len(mode)).sum()
    }

    fn write_encoded<W: io::Write>(
        &self,
        mode: Mode,
        target: &mut W
    ) -> Result<(), io::Error> {
        self.0.clone().try_for_each(|item| item.write_encoded(mode, target))
    }
}


//============ Standard Functions ============================================

/// Returns a value encoder for a SEQUENCE.
pub fn sequence<V: Values>(inner: V) -> impl Values {
    Constructed::new(Tag::SEQUENCE, inner)
}

/// Returns a value encoder for a SET
pub fn set<V: Values>(inner: V) -> impl Values {
    Constructed::new(Tag::SET, inner)
}

/// Returns the length for a structure based on the tag and content length.
pub fn total_encoded_len(tag: Tag, content_l: usize) -> usize {
    tag.encoded_len() + Length::Definite(content_l).encoded_len() + content_l
}

/// Writes a header for a structure.
pub fn write_header<W: io::Write>(
    target: &mut W,
    tag: Tag,
    constructed: bool,
    content_length: usize
) -> Result<(), io::Error> {
    tag.write_encoded(constructed, target)?;
    Length::Definite(content_length).write_encoded(target)?;
    Ok(())
}


//============ Helper Types ==================================================

//------------ Primitive -----------------------------------------------------

/// A value encoder for primitively encoded types.
pub struct Primitive<'a, P: 'a + ?Sized> {
    /// The tag for this value.
    tag: Tag,

    /// The primitive content.
    prim: &'a P
}

impl<'a, P: PrimitiveContent + 'a> Values for Primitive<'a, P> {
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


//------------ EndOfValue ----------------------------------------------------

struct EndOfValue;

impl Values for EndOfValue {
    fn encoded_len(&self, _: Mode) -> usize {
        2
    }

    fn write_encoded<W: io::Write>(
        &self,
        _: Mode,
        target: &mut W
    ) -> Result<(), io::Error> {
        let buf = [0, 0];
        target.write_all(&buf)
    }
}


pub struct Nothing;

impl Values for Nothing {
    fn encoded_len(&self, _mode: Mode) -> usize {
        0
    }

    fn write_encoded<W: io::Write>(
        &self,
        _mode: Mode,
        _target: &mut W
    ) -> Result<(), io::Error> {
        Ok(())
    }
}

