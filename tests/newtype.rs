use tinycbor_derive::{Encode, Decode, CborLen};

#[derive(Encode, Decode, CborLen)]
struct Struct(u32);

#[derive(Encode, Decode, CborLen)]
enum Enum {
    #[n(0)]
    Newtype(u32),
}
