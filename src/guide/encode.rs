//! Encoding data in BER.
//!
//! _Note: This guide is still work in progress and will be extended._
//!
//! In many cases, BER requires that a value can state the length of its
//! encoded content before actually starting to encode this content. Since
//! this requires duplicate code in many cases, we have decided to use
//! placeholder objects for encoding. These placeholders, called value
//! encoders, are available for most built-in types as well as for various
//! constructions such as tuples, a specific type can produce a
//! value encoder by manufacturing it from these existing parts.
//!
//! To return to the example from the decoding guide. It was using this
//! ASN.1:
//!
//!
//! ```text
//! EncapsulatedContentInfo  ::=  SEQUENCE  {
//!     eContentType ContentType,
//!     eContent [0] EXPLICIT OCTET STRING OPTIONAL
//! }
//!
//! ContentType  ::=  OBJECT IDENTIFIER
//! ```
//!
//! The structure was represented by this Rust struct:
//!
//! ```
//! use bcder::{Oid, OctetString};
//!
//! pub struct EncapsulatedContentInfo {
//!     content_type: Box<Oid>,
//!     content: Option<Box<OctetString>>,
//! }
//! ```
//! 
//! The value encoders all implement the trait [`encode::Values`] which
//! represents a sequence of BER-encodable values. The implementation of
//! our struct could return such an encoder like this:
//!
//! ```
//! # use bcder::{Oid, OctetString};
//! # use bcder::encode::PrimitiveContent;
//! use bcder::{Mode, Tag};
//! use bcder::encode;
//!
//! # pub struct EncapsulatedContentInfo {
//! #     content_type: Box<Oid>,
//! #     content: Option<Box<OctetString>>,
//! # }
//! # 
//! impl EncapsulatedContentInfo {
//!     pub fn encode<M: Mode>(&self) -> impl encode::Values<M> + '_ {
//!         self.encode_as(Tag::SEQUENCE)
//!     }
//!
//!     pub fn encode_as<M: Mode>(&self, tag: Tag) -> impl encode::Values<M> + '_ {
//!         encode::sequence_as(tag, (
//!             self.content_type.encode(),
//!             self.content.as_ref().map(|s| s.encode())
//!         ))
//!     }
//! }
//! ```
//!
//! The conventional name for the method produces a value encoder with the
//! natural tag is `encode`. If necessary, `encode_as` should be present to
//! allow getting a value encoder with a chosen tag for implicit tagging.
//!
//! The signature of these methods will most likely require a lifetime bound
//! for the return value as in the example above, if the returned value
//! contains references to the value or its elements. This is completely fine,
//! since typically the returned value will only be used to encode the value
//! right away and then dropped.
//!
//! [`encode::Values`]: ../../encode/trait.Values.html
