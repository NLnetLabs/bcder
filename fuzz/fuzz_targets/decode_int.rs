#![no_main]

use libfuzzer_sys::fuzz_target;
use bcder::decode::SliceSource;
use bcder::int::{Integer, Unsigned};
use bcder::{Mode, Tag};

macro_rules! decode_builtin {
    ( $data:expr, $fn:ident ) => {{
        let _ = Mode::Ber.decode(SliceSource::new($data), |cons| {
            cons.take_primitive_if(Tag::INTEGER, |prim| prim.$fn())
        });
    }}
}

fuzz_target!(|data: &[u8]| {
    let _ = Mode::Ber.decode(SliceSource::new(data), |cons| {
        Integer::take_from(cons)
    });
    let _ = Mode::Ber.decode(SliceSource::new(data), |cons| {
        Unsigned::take_from(cons)
    });

    decode_builtin!(data, to_i8);
    decode_builtin!(data, to_u8);
    decode_builtin!(data, to_i16);
    decode_builtin!(data, to_u16);
    decode_builtin!(data, to_i32);
    decode_builtin!(data, to_u32);
    decode_builtin!(data, to_i64);
    decode_builtin!(data, to_u64);
    decode_builtin!(data, to_i128);
    decode_builtin!(data, to_u128);
});

