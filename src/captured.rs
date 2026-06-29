//! Captured encoded data.
//!
//! This is a private module. Its public items are re-exported by the parent.

use std:: mem;
use std::marker::PhantomData;
use std::sync::Arc;
use crate::{decode, encode};
use crate::length::Length;
use crate::mode::Mode;


//------------ Captured ------------------------------------------------------

/// A slice of data containing encoded data.
#[repr(transparent)]
pub struct Captured<M> {
    /// A marker for the mode.
    marker: PhantomData<M>,

    /// The actual data.
    data: [u8],
}

impl<M> Captured<M> {
    pub fn from_slice(slice: &[u8]) -> &Self {
        unsafe { mem::transmute(slice) }
    }

    pub fn from_box(data: Box<[u8]>) -> Box<Self> {
        unsafe { mem::transmute(data) }
    }

    pub fn from_arc(data: Arc<[u8]>) -> Arc<Self> {
        unsafe { mem::transmute(data) }
    }

    pub fn from_values<V: encode::Values<M>>(values: &V) -> Box<Self> {
        let res = values.to_vec().into_boxed_slice();
        Self::from_box(res)
    }

    /// Returns a bytes slice with the raw data of the captured value.
    pub fn as_slice(&self) -> &[u8] {
        &self.data
    }

    pub fn process<F, T>(&self, op: F) -> Result<T, decode::Error>
    where
        M: Mode,
        F: FnOnce(decode::Value<M, &[u8]>) -> Result<T, decode::Error>
    {
        decode::Data::process(&self.data, op)
    }
}


//--- AsRef

impl<M> AsRef<[u8]> for Captured<M> {
    fn as_ref(&self) -> &[u8] {
        self.as_slice()
    }
}


//--- encode::Values

impl<M> encode::Values<M> for Captured<M> {
    fn encoded_len(&self) -> Length {
        self.data.len().into()
    }

    fn write_encoded<T: encode::Target>(
        &self, target: &mut T
    ) -> Result<(), T::Error> {
        target.write_all(&self.data)
    }
}


