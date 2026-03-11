use tinycbor_derive::{Encode, Decode, CborLen};

#[derive(Encode, Decode, CborLen)]
enum A {}


#[derive(Encode, Decode, CborLen)]
#[cbor(naked)]
enum B {}

#[derive(Encode, Decode, CborLen)]
#[cbor(tag(42))]
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
