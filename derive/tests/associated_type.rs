use tinycbor::Decode as _;
use tinycbor_derive::Decode;

trait HasAssoc {
    type Assoc;
}

struct Marker;

impl HasAssoc for Marker {
    type Assoc = u64;
}

#[derive(Decode)]
#[cbor(decode_bound = "T::Assoc: tinycbor::Decode<'_>")]
struct Associated<T: HasAssoc> {
    value: T::Assoc,
    other: u64,
}

#[test]
fn decodes_associated_type_field() {
    let value = Associated::<Marker>::decode(&mut tinycbor::Decoder(&[0x82, 1, 2])).unwrap();
    assert_eq!(value.value, 1);
    assert_eq!(value.other, 2);
}
