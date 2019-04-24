# Change Log

## Unreleased next version

Breaking

New

* New methods for checking the class and number on `Tag`. [(#20)]
* Implement `TryFrom` for builtin integers and `Integer` and `Unsigned`.
  [(#23)]

Bug Fixes

Other Changes

* The `xerr!` macro now prints a backtrace with the `extra-debug` feature
  enabled instead of panicking. [(#21)]

Dependencies

[(#20)]: https://github.com/NLnetLabs/rpki-rs/pull/20
[(#21)]: https://github.com/NLnetLabs/rpki-rs/pull/21
[(#23)]: https://github.com/NLnetLabs/rpki-rs/pull/23


## 0.2.1

New

*  Add `BitString::encode_slice` and `encode_slice_as`. [(#17)]

Bug Fixes

*  Fix incorrect encoding of primitive unsigned integers for values with a
   number of leading zero bits divisible by eight. [(#16)]
*  Fix the mkoid tool to correctly encode large subidentifiers. [(#18)]

[(#16)]: https://github.com/NLnetLabs/rpki-rs/pull/16
[(#17)]: https://github.com/NLnetLabs/rpki-rs/pull/17
[(#18)]: https://github.com/NLnetLabs/rpki-rs/pull/18


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

