# Change Log

## Unreleased next version

Breaking Changes

New

Bug Fixes

*  Fix incorrect encoding of primitive unsigned integers for values with a
   number of leading zero bits divisible by eight. [(#16)]

Dependencies


[(#16)]: https://github.com/NLnetLabs/rpki-rs/pull/16


## 0.2.0

Breaking Changes

*  Drop use of _failure_ crate. Error types now provide a `Display`
   implementation only. [(#15)]

*  `PrimitiveContent`’s methods take `self` instead of `&self`. This
   avoids the lifetime argument in `Primitive`, its encoder. [(#7)]

*  For all provided type, change `encode` and `encode_as` methods to take
   self by value and introduce `encode_ref` and `encode_ref_as` that take
   self by reference. [(#12)]

*  `RestrictedString::from_str` replaced by an implementation of the
   `FromStr` trait. [(#13)]

New

*  `encode::Values` implemented for tuples of up to twelve elements.
   [(#9)]

*  `OctetString::encode_slice` and `encode_slice_as`: allows encoding a bytes
   slice as an octet string without going through making an `OctetString`
   first.

*  `encode::Slice` wraps a slice of values encoding `encode::Values` and
   provides an encoder for it. [(#11)]

*  new functions: `encode::slice` and `encode::iter` as shortcuts for the
   respective associated functions. [(#11)]

*  `OctetString::is_empty` [(#13)], `OctetString::into_bytes` [(#14)].

[(#7)]: https://github.com/NLnetLabs/bcder/pull/7
[(#9)]: https://github.com/NLnetLabs/bcder/pull/9
[(#10)]: https://github.com/NLnetLabs/bcder/pull/10
[(#11)]: https://github.com/NLnetLabs/bcder/pull/11
[(#12)]: https://github.com/NLnetLabs/bcder/pull/12
[(#13)]: https://github.com/NLnetLabs/bcder/pull/13
[(#14)]: https://github.com/NLnetLabs/bcder/pull/14
[(#14)]: https://github.com/NLnetLabs/bcder/pull/15


## 0.1.0

Initial public release.

