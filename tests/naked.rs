use tinycbor_derive::{Encode, Decode, CborLen};
use tinycbor::*;

#[derive(Debug, PartialEq, Encode, Decode, CborLen)]
#[cbor(naked, error = "HelloError")]
pub enum Hello {
    #[n(0)]
    World,
    #[n(3)]
    People,
    #[n(2)]
    Guys,
    #[n(1)]
    Folks,
}

#[derive(Debug, PartialEq, Encode, Decode, CborLen)]
#[cbor(naked)]
pub struct Wrapper(u64);

#[test]
fn roundtrip() {
    let value = Wrapper(42);
    let encoded = to_vec(&value);
    let decoded: Wrapper = Decode::decode(&mut Decoder(&encoded)).unwrap();
    assert_eq!(value, decoded);

    let value = Hello::People;
    let encoded = to_vec(&value);
    let decoded: Hello = Decode::decode(&mut Decoder(&encoded)).unwrap();
    assert_eq!(value, decoded);
}
