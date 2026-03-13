use tinycbor_derive::{Encode, Decode, CborLen};
use tinycbor::Decode;

#[derive(Debug, Encode, Decode, CborLen)]
enum A {}


#[derive(Debug, Encode, Decode, CborLen)]
#[cbor(naked)]
enum B {}

#[derive(Debug, Encode, Decode, CborLen)]
#[cbor(tag(1))]
enum C {}

#[derive(Encode, Decode, CborLen)]
struct D;

#[derive(Encode, Decode, CborLen)]
#[cbor(naked)]
struct E;

#[derive(Encode, Decode, CborLen)]
#[cbor(tag(42))]
struct F;

#[derive(Encode, Decode, CborLen)]
#[cbor(map)]
struct G;

#[derive(Encode, Decode, CborLen)]
#[cbor(map, tag(42))]
struct H;

macro_rules! roundtrip {
    ($ty:ident) => {
        let value = $ty;
        let encoded = tinycbor::to_vec(&value);
        let mut decoder = tinycbor::Decoder(&encoded);
        let _ = $ty::decode(&mut decoder).unwrap();
    };
}

#[test]
fn units() {
    roundtrip!(D);
    roundtrip!(E);
    roundtrip!(F);
    roundtrip!(G);
    roundtrip!(H);
}

#[test]
fn void() {
    A::decode(&mut tinycbor::Decoder(&[0x80])).unwrap_err();
    B::decode(&mut tinycbor::Decoder(&[])).unwrap_err();
    C::decode(&mut tinycbor::Decoder(&[0xc1, 0x80])).unwrap_err();
}
