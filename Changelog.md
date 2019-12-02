# Change Log

## Unreleased next version

Breaking

New

Bug Fixes

* Fix encoding of signed builtin integer (`i8`, `i16`, …). [(#39)]

Dependencies


[(#39)]: https://github.com/NLnetLabs/bcder/pull/39


## 0.4.0

Breaking

* Dropped `RestrictedString::to_string` and implemented it via `Display`
  instead. Therefore, you will have to `use std::fmt::Display` to get it
  back. [(#33)]

Bug Fixes

* Safely decode deeply nested BER such as octet strings. Decoding such
  types now uses an allocated artificial stack and will thus not overflow
  the regular one. [(#30)]

Miscellaneous

* Dropped dependency on `derive_more` for fewer dependencies and faster
  compiling. ([#32], thanks to [@nocduro]).

[(#30)]: https://github.com/NLnetLabs/bcder/pull/30
[#32]: https://github.com/NLnetLabs/bcder/pull/32
[(#33)]: https://github.com/NLnetLabs/bcder/pull/33
[@nocduro]: https://github.com/nocduro


## 0.3.1

Bug Fixes

* Fix a lifetime warning from the new borrow checker. [(#27)]
* Build on 32 bit systems. [(#29)]

Other Changes

* Switch to Rust edition 2018.

[(#27)]: https://github.com/NLnetLabs/bcder/pull/27
[(#29)]: https://github.com/NLnetLabs/bcder/pull/29


## 0.3.0

Breaking

* The minimum supported Rust version is now 1.34.0. [(#22)]

New

* New methods for checking the class and number on `Tag`. [(#20)]
* Implement `TryFrom` for builtin integers and `Integer` and `Unsigned`.
  [(#23)]
* `RestrictedString::into_bytes` [(#24)]

Other Changes

* The `xerr!` macro now prints a backtrace with the `extra-debug` feature
  enabled instead of panicking. [(#21)]

[(#20)]: https://github.com/NLnetLabs/rpki-rs/pull/20
[(#21)]: https://github.com/NLnetLabs/rpki-rs/pull/21
[(#22)]: https://github.com/NLnetLabs/rpki-rs/pull/22
[(#23)]: https://github.com/NLnetLabs/rpki-rs/pull/23
[(#24)]: https://github.com/NLnetLabs/rpki-rs/pull/24


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

