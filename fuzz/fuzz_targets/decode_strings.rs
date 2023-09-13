#![no_main]

use libfuzzer_sys::fuzz_target;
use bcder::decode::SliceSource;
use bcder::string::{
    BitString, OctetString, Ia5String, NumericString, PrintableString,
    Utf8String,
};
use bcder::Mode;

macro_rules! decode_strings {
    ( $data:expr, [ $( $mode:ident ),* ] ) => {{
        $(
            let take = Mode::$mode.decode(SliceSource::new($data), |cons| {
                BitString::take_from(cons)
            });
            let skip = Mode::$mode.decode(SliceSource::new($data), |cons| {
                BitString::skip_in(cons)
            }).is_ok();
            assert_eq!(take.is_ok(), skip);

            if let Ok(take) = take {
                assert!(take.unused() < 8);
                assert!(take.octet_len() > 0 || take.unused() == 0);
            }

            let _ = Mode::$mode.decode(SliceSource::new($data), |cons| {
                OctetString::take_from(cons)
            });
            let _ = Mode::$mode.decode(SliceSource::new($data), |cons| {
                OctetString::take_opt_from(cons)
            });
            let _ = Mode::$mode.decode(SliceSource::new($data), |cons| {
                Ia5String::take_from(cons)
            });
            let _ = Mode::$mode.decode(SliceSource::new($data), |cons| {
                NumericString::take_from(cons)
            });
            let _ = Mode::$mode.decode(SliceSource::new($data), |cons| {
                PrintableString::take_from(cons)
            });
            let _ = Mode::$mode.decode(SliceSource::new($data), |cons| {
                Utf8String::take_from(cons)
            });
        )*
    }}

}

fuzz_target!(|data: &[u8]| {
    decode_strings!(data, [Ber, Cer, Der]);
});

