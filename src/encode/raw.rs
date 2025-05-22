//! Encoding raw data.

use std::marker::PhantomData;
use crate::ident::Tag;
use crate::length::Length;
use super::primitive::PrimitiveContent;
use super::target::Target;
use super::values::{
    Values, total_indefinite_len, total_len, write_end_of_contents,
    write_header, write_indefinite_header,
};


pub fn primitive<'s, M: 's>(
    tag: Tag, data: &'s (impl AsRef<[u8]> + ?Sized),
) -> impl Values<M> + 's {
    data.as_ref().encode_as(tag)
}

pub use self::primitive as prim;


pub fn definite_constructed<M, V: Values<M>>(
    tag: Tag, content: V
) -> impl Values<M> {
    DefiniteConstructed { tag, content, marker: PhantomData }
}

pub use self::definite_constructed as dcons;


struct DefiniteConstructed<M, V> {
    tag: Tag,
    content: V,
    marker: PhantomData<M>,
}

impl<M, V: Values<M>> Values<M> for DefiniteConstructed<M, V> {
    fn encoded_len(&self) -> Length {
        total_len(self.tag, self.content.encoded_len())
    }

    fn write_encoded<T: Target>(
        &self, target: &mut T
    ) -> Result<(), T::Error> {
        write_header(target, self.tag, true, self.content.encoded_len())?;
        self.content.write_encoded(target)
    }
}


pub fn indefinite_constructed<M, V: Values<M>>(
    tag: Tag, content: V
) -> impl Values<M> {
    IndefiniteConstructed { tag, content, marker: PhantomData }
}

pub use self::indefinite_constructed as icons;


struct IndefiniteConstructed<M, V> {
    tag: Tag,
    content: V,
    marker: PhantomData<M>,
}

impl<M, V: Values<M>> Values<M> for IndefiniteConstructed<M, V> {
    fn encoded_len(&self) -> Length {
        total_indefinite_len(self.tag, self.content.encoded_len())
    }

    fn write_encoded<T: Target>(
        &self, target: &mut T
    ) -> Result<(), T::Error> {
        write_indefinite_header(target, self.tag)?;
        self.content.write_encoded(target)?;
        write_end_of_contents(target)
    }
}

