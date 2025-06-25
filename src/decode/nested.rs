//! Processing of nested values.

use std::io;
use smallvec::SmallVec;
use crate::ident::{Ident, Tag};
use crate::length::{Length, LengthOctets};
use crate::mode::Mode;
use super::constructed::{Constructed, ReadableConstructed};
use super::error::Error;
use super::source::Source;
use super::primitive::Primitive;


//------------ NestedIter ----------------------------------------------------

pub struct NestedIter<'a, M: Mode, R: io::Read> {
    cons: ReadableConstructed<'a, M, R>,
    stack: Stack,
}

impl<'a, M: Mode, R: io::Read> NestedIter<'a, M, R> {
    pub fn new(cons: Constructed<'a, M, R>) -> Self {
        Self {
            cons: cons.into(),
            stack: Stack::default(),
        }
    }

    pub fn next_item(&mut self) -> Result<Option<NestedItem<M, R>>, Error> {
        // Take the top off the stack. We’ll put it back if haven’t reached
        // the end of that value yet.
        while let Some(item) = self.stack.pop() {
            match self.stack_next(item)? {
                PreItem::Cons { tag, start, length, stack } => {
                    self.stack.push(item);
                    self.stack.push(stack);
                    return Ok(Some(NestedItem::Constructed {
                        tag, start, length
                    }))
                }
                PreItem::Prim { tag, start, limit } => {
                    self.stack.push(item);
                    return Ok(Some(NestedItem::Primitive(Primitive::new(
                        self.cons.source(), limit, tag, start
                    ))))
                }
                PreItem::EndOfCons => {
                    // Climb up the stack.
                }
            }
        }

        // Nothing on the stack, so we have to use the next value from
        // `self.cons`.
        match self.cons_next()? {
            PreItem::Cons { tag, start, length, stack } => {
                self.stack.push(stack);
                Ok(Some(NestedItem::Constructed {
                    tag, start, length
                }))
            }
            PreItem::Prim { tag, start, limit } => {
                Ok(Some(NestedItem::Primitive(Primitive::new(
                    self.cons.source(), limit, tag, start
                ))))
            }
            PreItem::EndOfCons => {
                // We are done.
                Ok(None)
            }
        }
    }

    fn stack_next(&mut self, item: StackItem) -> Result<PreItem, Error> {
        match item {
            StackItem::Definite(limit) => {
                self.stack_next_definite(limit)
            }
            StackItem::Indefinite(limit) => {
                self.stack_next_indefinite(limit)
            }
        }
    }

    fn stack_next_definite(
        &mut self, limit: Length
    ) -> Result<PreItem, Error> {
        let mut source = LimitedSource::new(self.cons.source(), Some(limit));

        let start = source.pos();
        let Some(ident) = Ident::read_opt(&mut source).map_err(|err| {
            Error::from_io(err, start)
        })? else {
            return Ok(PreItem::EndOfCons)
        };
        if ident == Ident::END_OF_CONTENTS {
            return Err(Error::content(
                "end-of-contents in definite length value", start
            ))
        }

        let length = LengthOctets::read::<M>(&mut source).map_err(|err| {
            Error::from_io(err, start)
        })?;

        if !ident.is_constructed() {
            let Some(length) = length.definite() else {
                return Err(Error::content(
                    "indefinite length primitive value", start
                ));
            };
            let limit = source.pos() + length;
            if let Some(source_limit) = source.limit {
                if limit > source_limit {
                    return Err(Error::content(
                        "nested value too long", start
                    ))
                }
            }
            Ok(PreItem::Prim { tag: ident.tag(), start, limit })
        }
        else if let Some(length) = length.definite() {
            // Definite-length constructed.
            if !M::ALLOW_DEFINITE_CONSTRUCTED {
                return Err(Error::content(
                    "definite length constructed in CER", start
                ))
            }
            let limit = source.pos() + length;
            if let Some(source_limit) = source.limit {
                if limit > source_limit {
                    return Err(Error::content(
                        "nested value too long", start
                    ))
                }
            }
            Ok(PreItem::Cons {
                tag: ident.tag(), start,
                length: Some(length),
                stack: StackItem::Definite(limit)
            })
        }
        else {
            // Indefinite-length constructed.
            if !M::ALLOW_INDEFINITE_CONSTRUCTED {
                return Err(Error::content(
                    "indefinite length constructed in DER", start
                ))
            }
            Ok(PreItem::Cons {
                tag: ident.tag(), start,
                length: None,
                stack: StackItem::Indefinite(source.limit)
            })
        }
    }

    fn stack_next_indefinite(
        &mut self, limit: Option<Length>
    ) -> Result<PreItem, Error> {
        let mut source = LimitedSource::new(self.cons.source(), limit);

        let start = source.pos();
        let ident = Ident::read(&mut source).map_err(|err| {
            Error::from_io(err, start)
        })?;

        if ident == Ident::END_OF_CONTENTS {
            LengthOctets::read_end_of_contents(&mut source).map_err(|err| {
                Error::from_io(err, start)
            })?;
            return Ok(PreItem::EndOfCons)
        }

        let length = LengthOctets::read::<M>(&mut source).map_err(|err| {
            Error::from_io(err, start)
        })?;

        if !ident.is_constructed() {
            let Some(length) = length.definite() else {
                return Err(Error::content(
                    "indefinite length primitive value", start
                ));
            };
            let limit = source.pos() + length;
            if let Some(source_limit) = source.limit {
                if limit > source_limit {
                    return Err(Error::content(
                        "nested value too long", start
                    ))
                }
            }
            Ok(PreItem::Prim { tag: ident.tag(), start, limit })
        }
        else if let Some(length) = length.definite() {
            // Definite-length constructed.
            if !M::ALLOW_DEFINITE_CONSTRUCTED {
                return Err(Error::content(
                    "definite length constructed in CER", start
                ))
            }
            let limit = source.pos() + length;
            if let Some(source_limit) = source.limit {
                if limit > source_limit {
                    return Err(Error::content(
                        "nested value too long", start
                    ))
                }
            }
            Ok(PreItem::Cons {
                tag: ident.tag(), start,
                length: Some(length),
                stack: StackItem::Definite(limit)
            })
        }
        else {
            // Indefinite-length constructed.
            if !M::ALLOW_INDEFINITE_CONSTRUCTED {
                return Err(Error::content(
                    "indefinite length constructed in DER", start
                ))
            }
            Ok(PreItem::Cons {
                tag: ident.tag(), start,
                length: None,
                stack: StackItem::Indefinite(source.limit)
            })
        }
    }

    fn cons_next(&mut self) -> Result<PreItem, Error> {
        let Some((ident, start)) = self.cons.read_opt_ident()? else {
            return Ok(PreItem::EndOfCons)
        };
        let length = LengthOctets::read::<M>(&mut self.cons).map_err(|err| {
            Error::from_io(err, start)
        })?;

        if !ident.is_constructed() {
            let Some(length) = length.definite() else {
                return Err(Error::content(
                    "indefinite length primitive value", start
                ));
            };
            let limit = self.cons.pos() + length;
            if let Some(source_limit) = self.cons.limit() {
                if limit > source_limit {
                    return Err(Error::content(
                        "nested value too long", start
                    ))
                }
            }
            Ok(PreItem::Prim { tag: ident.tag(), start, limit })
        }
        else if let Some(length) = length.definite() {
            // Definite-length constructed.
            if !M::ALLOW_DEFINITE_CONSTRUCTED {
                return Err(Error::content(
                    "definite length constructed in CER", start
                ))
            }
            let limit = self.cons.pos() + length;
            if let Some(source_limit) = self.cons.limit() {
                if limit > source_limit {
                    return Err(Error::content(
                        "nested value too long", start
                    ))
                }
            }
            Ok(PreItem::Cons {
                tag: ident.tag(), start,
                length: Some(length),
                stack: StackItem::Definite(limit)
            })
        }
        else {
            // Indefinite-length constructed.
            if !M::ALLOW_INDEFINITE_CONSTRUCTED {
                return Err(Error::content(
                    "indefinite length constructed in DER", start
                ))
            }
            Ok(PreItem::Cons {
                tag: ident.tag(), start,
                length: None,
                stack: StackItem::Indefinite(self.cons.limit())
            })
        }
    }
}


//------------ NestedItem ----------------------------------------------------

enum PreItem {
    Cons {
        tag: Tag,
        start: Length,
        length: Option<Length>,
        stack: StackItem,
    },
    Prim {
        tag: Tag,
        start: Length,
        limit: Length,
    },
    EndOfCons,
}


//------------ NestedItem ----------------------------------------------------

pub enum NestedItem<'a, M, R> {
    Constructed {
        tag: Tag,
        start: Length,
        length: Option<Length>,
    },
    Primitive(Primitive<'a, M, R>),
}


//------------ Stack ---------------------------------------------------------

#[derive(Clone, Debug, Default)]
struct Stack {
    items: SmallVec::<[StackItem; 4]>,
}

impl Stack {
    fn push(&mut self, item: StackItem) {
        self.items.push(item)
    }

    fn pop(&mut self) -> Option<StackItem> {
        self.items.pop()
    }
}


//------------ StackItem -----------------------------------------------------

#[derive(Clone, Copy, Debug)]
enum StackItem {
    /// Definite constructed value.
    ///
    /// It definitely has a limit which is the end position in the source.
    Definite(Length),

    /// Indefinite constructed value.
    ///
    /// It may have a limit if it is contained in an item with a limit.
    Indefinite(Option<Length>),
}


//------------ LimitedSource -------------------------------------------------

struct LimitedSource<'a, R> {
    source: &'a mut Source<R>,
    limit: Option<Length>,
}

impl<'a, R> LimitedSource<'a, R> {
    fn new(source: &'a mut Source<R>, limit: Option<Length>) -> Self {
        Self { source, limit }
    }

    fn pos(&self) -> Length {
        self.source.pos()
    }
}

impl<R: io::Read> io::Read for LimitedSource<'_, R> {
    fn read(&mut self, buf: &mut [u8]) -> Result<usize, io::Error> {
        if let Some(limit) = self.limit {
            let remaining = match limit.checked_sub(
                self.source.pos()
            ) {
                Some(remaining) => remaining.to_usize_saturating(),
                None => {
                    return Err(io::Error::new(
                        io::ErrorKind::InvalidData,
                        "long nested value"
                    ))
                }
            };
            if let Some(short_buf) = buf.get_mut(..remaining) {
                return self.source.read(short_buf)
            }
        }
        self.source.read(buf)
    }
}

