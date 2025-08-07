//! Decoding either type of value.
//!
//! This is a private module. The relevant items are re-exported by the
//! parent.

use std::io;
use crate::captured::Captured;
use crate::ident::Tag;
use crate::length::Length;
use crate::mode::Mode;
use super::constructed::Constructed;
use super::error::Error;
use super::nested::NestedItem;
use super::primitive::Primitive;
use super::source::CaptureSource;


//------------ Value ---------------------------------------------------------

pub enum Value<'a, M: Mode, R: io::BufRead + 'a> {
    /// The value is a primitive value.
    Primitive(Primitive<'a, M, R>),

    /// The value is a constructed value.
    Constructed(Constructed<'a, M, R>)
}

impl<'a, M: Mode, R: io::BufRead + 'a> Value<'a, M, R> {
    /// Returns whether this value is a primitive value.
    pub fn is_primitive(&self) -> bool {
        match *self {
            Value::Primitive(_) => true,
            Value::Constructed(_) => false,
        }
    }

    /// Returns whether this value is a constructed value.
    pub fn is_constructed(&self) -> bool {
        match *self {
            Value::Primitive(_) => false,
            Value::Constructed(_) => true,
        }
    }

    /// Converts a reference into into one to a primitive value or errors out.
    pub fn into_primitive(
        self
    ) -> Result<Primitive<'a, M, R>, Error> {
        match self {
            Value::Primitive(inner) => Ok(inner),
            Value::Constructed(inner) => {
                Err(Error::content(
                    "expected primitive value", inner.start()
                ))
            }
        }
    }

    /// Converts a reference into on to a constructed value or errors out.
    pub fn into_constructed(
        self
    ) -> Result<Constructed<'a, M, R>, Error> {
        match self {
            Value::Primitive(inner) => {
                Err(Error::content(
                    "expected constructed value", inner.start()
                ))
            }
            Value::Constructed(inner) => Ok(inner),
        }
    }

    /// Converts a reference into into one to a primitive value or errors out.
    pub fn as_primitive(
        &mut self
    ) -> Result<&mut Primitive<'a, M, R>, Error> {
        match *self {
            Value::Primitive(ref mut inner) => Ok(inner),
            Value::Constructed(ref inner) => {
                Err(Error::content("expected primitive value", inner.start()))
            }
        }
    }

    /// Converts a reference into on to a constructed value or errors out.
    pub fn as_constructed(
        &mut self
    ) -> Result<&mut Constructed<'a, M, R>, Error> {
        match *self {
            Value::Primitive(ref inner) => {
                Err(Error::content("expected constructed value", inner.start()))
            }
            Value::Constructed(ref mut inner) => Ok(inner),
        }
    }

    /// Returns the start position of the value.
    pub fn start(&self) -> Length {
        match self {
            Value::Primitive(inner) => inner.start(),
            Value::Constructed(inner) => inner.start(),
        }
    }

    /// Returns the tag of the value.
    pub fn tag(&self) -> Tag {
        match self {
            Value::Primitive(inner) => inner.tag(),
            Value::Constructed(inner) => inner.tag(),
        }
    }

    pub fn skip<F>(
        self, mut op: F
    ) -> Result<(), Error> 
    where
        R: io::BufRead,
        F: FnMut(Tag, bool, usize) -> Result<(), Error>,
    {
        match self {
            Value::Primitive(prim) => {
                op(prim.tag(), false, 0)?;
                prim.skip_all()?;
                Ok(())
            }
            Value::Constructed(cons) => {
                let mut depth = 0;
                cons.process_nested(|item| {
                    match item {
                        NestedItem::Constructed(cons) => {
                            depth = cons.depth;
                            op(cons.tag, true, cons.depth)
                        },
                        NestedItem::Primitive(prim) => {
                            op(prim.tag(), false, depth + 1)?;
                            prim.skip_all()
                        }
                    }
                })?;
                Ok(())
            }
        }
    }

    pub fn capture<F>(self, op: F) -> Result<Box<Captured<M>>, Error>
    where
        R: io::BufRead,
        F: FnOnce(Value<M, CaptureSource<M, R>>) -> Result<(), Error>
    {
        match self {
            Value::Primitive(prim) => {
                prim.capture(|prim| op(Value::Primitive(prim)))
            }
            Value::Constructed(cons) => {
                cons.capture(|cons| op(Value::Constructed(cons)))
            }
        }
    }
}

