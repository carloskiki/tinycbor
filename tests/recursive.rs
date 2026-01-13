#![cfg(feature = "alloc")]
extern crate alloc;

use tinycbor::{Decode, Decoder, to_vec};
use tinycbor_derive::{Encode, Decode, CborLen};

#[derive(Encode, Decode, CborLen, PartialEq, Eq, Debug)]
#[cbor(recursive)]
struct Thing {
    value: i32,
    next: Option<Box<Thing>>,
}

#[derive(Encode, Decode, CborLen, PartialEq, Eq, Debug)]
#[cbor(error = "BinaryError", recursive)]
enum Binary {
    #[n(0)]
    Leaf(Thing),
    #[n(1)]
    Node(Box<Binary>, Box<Binary>),
}

#[test]
fn roundtrip() {
    let original = Binary::Node(
        Box::new(Binary::Leaf(Thing {
            value: 1,
            next: Some(Box::new(Thing { value: 2, next: None })),
        })),
        Box::new(Binary::Leaf(Thing {
            value: 3,
            next: None,
        })),
    );

    let encoded = to_vec(&original);
    let decoded: Binary = Decode::decode(&mut Decoder(&encoded)).unwrap();

    assert_eq!(original, decoded);
    
}
