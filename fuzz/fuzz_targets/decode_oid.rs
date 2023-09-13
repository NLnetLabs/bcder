#![no_main]

use libfuzzer_sys::fuzz_target;
use bcder::decode::SliceSource;
use bcder::{ConstOid, Oid};
use bcder::Mode;

pub const SHA256: ConstOid = Oid(&[96, 134, 72, 1, 101, 3, 4, 2, 1]);

fuzz_target!(|data: &[u8]| {
    let take = Mode::Ber.decode(SliceSource::new(data), |cons| {
        Oid::take_from(cons)
    });
    let skip = Mode::Ber.decode(SliceSource::new(data), |cons| {
        Oid::skip_in(cons)
    }).is_ok();
    assert_eq!(take.is_ok(), skip);

    if let Ok(take) = take.as_ref() {
        let _ = take.to_string();
    }

    let skip_if = Mode::Ber.decode(SliceSource::new(data), |cons| {
        SHA256.skip_if(cons)
    }).is_ok();

    if skip_if {
        assert_eq!(take.unwrap(), SHA256);
    }

    let _ = Mode::Ber.decode(SliceSource::new(data), |cons| {
        Oid::skip_opt_in(cons)
    });

});
