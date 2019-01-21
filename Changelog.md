# Change Log

## 0.2.0

Breaking Changes

*  `PrimitiveContent`’s methods take `self` instead of `&self`. This
   avoids the lifetime argument in `Primitive`, its encoder. [(#7)]

New

*  `encode::Values` implemented for tuples of up to twelve elements.
   [(#9)]
*  `OctetString::encode_slice` and `encode_slice_as`: allows encoding a bytes
   slice as an octet string without going through making an `OctetString`
   first.

Bug Fixes

Dependencies

[(#7)]: https://github.com/NLnetLabs/bcder/pull/7
[(#9)]: https://github.com/NLnetLabs/bcder/pull/9
[(#10)]: https://github.com/NLnetLabs/bcder/pull/10


## 0.1.0

Initial public release.

