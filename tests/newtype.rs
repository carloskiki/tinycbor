use tinycbor::{Decode, Decoder, to_vec};
use tinycbor_derive::{CborLen, Decode, Encode};

#[derive(Debug, Encode, Decode, CborLen, PartialEq)]
struct Struct(u32);

#[derive(Debug, Encode, Decode, CborLen, PartialEq)]
enum Enum {
    #[n(0)]
    Newtype(u32),
}

#[derive(Debug, Encode, Decode, CborLen, PartialEq)]
enum WithOthers {
    #[n(1)]
    Unit,
    #[n(0)]
    Newtype(u32),
}

#[test]
fn roundtrip() {
    let s = Struct(42);
    let e = Enum::Newtype(42);
    let w = WithOthers::Newtype(42);

    let s_bytes = to_vec(&s);
    let e_bytes = to_vec(&e);
    let w_bytes = to_vec(&w);

    assert_eq!(s, Struct::decode(&mut Decoder(&s_bytes)).unwrap());
    assert_eq!(e, Enum::decode(&mut Decoder(&e_bytes)).unwrap());
    assert_eq!(w, WithOthers::decode(&mut Decoder(&w_bytes)).unwrap());
}
