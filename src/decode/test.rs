#![cfg(test)]

use crate::encode;
use crate::encode::raw::{dcons, icons, prim};
use crate::ident::Tag;
use crate::mode::Ber;
use super::*;

fn prepare_ber(val: impl encode::Values<Ber>) -> Vec<u8> {
    val.to_vec()
}

fn decode_ber(slice: &[u8]) -> Data<Ber, &[u8]> {
    Data::new(slice)
}

#[test]
fn short_reads() {
    let ber = prepare_ber((
        dcons(Tag::SEQUENCE, (
            prim(Tag::ctx(0), "foo"),
            prim(Tag::ctx(1), "bar"),
        )),
        dcons(Tag::ctx(0), prim(Tag::ctx(0), "baz"))
    ));

    // Check short read on a primitive.
    let mut data = decode_ber(&ber);
    let mut cons = data.next_value().unwrap()
        .into_constructed().unwrap();
    {
        let mut prim = cons.next_value().unwrap()
            .into_primitive().unwrap();
        assert_eq!(
            prim.read_exact_into_box(2).unwrap().as_ref(), b"fo".as_ref()
        );
    }
    assert!(cons.next_value().is_err());

    // Check short read on a definite constructed.
    let mut data = decode_ber(&ber);
    {
        let mut cons = data.next_value().unwrap()
            .into_constructed().unwrap();
        assert_eq!(
            cons.next_value().unwrap().into_primitive().unwrap()
                .read_all_into_box().unwrap().as_ref(),
            b"foo"
        );
    }
    assert!(data.next_value().is_err());

    // Check short read on an indefinite constructed.
    let ber = prepare_ber((
        icons(Tag::SEQUENCE, (
            prim(Tag::ctx(0), "foo"),
            prim(Tag::ctx(1), "bar"),
        )),
        dcons(Tag::ctx(0), prim(Tag::ctx(0), "baz"))
    ));
    let mut data = decode_ber(&ber);
    {
        let mut cons = data.next_value().unwrap()
            .into_constructed().unwrap();
        assert_eq!(
            cons.next_value().unwrap().into_primitive().unwrap()
                .read_all_into_box().unwrap().as_ref(),
            b"foo"
        );
    }
    assert!(data.next_value().is_err());
}

