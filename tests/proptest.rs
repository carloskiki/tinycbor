use std::{
    cell::{Cell, RefCell},
    collections::{BTreeMap, HashMap, HashSet},
    num::NonZeroUsize,
};

use proptest::{
    prelude::{Strategy, any},
    proptest,
    test_runner::FileFailurePersistence,
};
use proptest_derive::Arbitrary;
use tinycbor::{
    CborLen, Decode, Decoder, Encode,
    num::Int,
    primitive::{Null, Simple, Undefined},
};
use tinycbor_derive::{CborLen, Decode, Encode};

#[derive(Debug, Encode, Decode, CborLen, Arbitrary, PartialEq)]
#[cbor(tag_only, error = "TagOnlyError")]
enum TagOnly {
    #[n(0)]
    First,
    #[n(17)]
    Second,
    #[n(4)]
    Third,
    #[n(5)]
    Fourth,
    #[n(100)]
    Fifth,
    #[n(1025)]
    Sixth,
    #[n(200000)]
    Seventh,
    #[n(99999999)]
    Eighth,
    #[n(99999999999)]
    Ninth,
}

#[derive(Debug, Encode, Decode, CborLen, Arbitrary, PartialEq)]
#[cbor(error = "PartAError")]
struct PartA {
    #[proptest(value = "Null")]
    a: Null,
    b: u32,
    #[cbor(with = "&'_ str")]
    c: String,
    d: Vec<u8>,
    #[cbor(tag(42))]
    e: RefCell<Box<[u8]>>,
}

#[derive(Debug, Encode, Decode, CborLen, Arbitrary, PartialEq)]
#[cbor(error = "PartBError", map, tag(2001))]
struct PartB {
    #[n(1)]
    #[proptest(value = "Undefined")]
    a: Undefined,
    #[cbor(n(14445), optional)]
    #[proptest(strategy = "simple_strategy()")]
    b: Option<Simple>,
    #[n(3)]
    c: std::num::Wrapping<i64>,
    #[cbor(n(45), tag(45))]
    #[proptest(strategy = "int_strategy()")]
    d: Int,
    #[cbor(n(5), tag(99), with = "tinycbor::num::U8")]
    e: u8,
}

#[derive(Debug, Encode, Decode, CborLen, Arbitrary, PartialEq)]
#[cbor(error = "PartCError", map)]
struct PartC {
    #[n(10101010)]
    a: Box<PartA>,
    #[n(20202020)]
    b: RefCell<NonZeroUsize>,
    #[n(30303030)]
    c: Cell<u64>,
    #[n(40404040)]
    d: HashMap<u32, String>,
    #[n(50505050)]
    e: Box<[u8]>,
}

#[derive(Debug, Encode, Decode, CborLen, Arbitrary, PartialEq)]
#[cbor(error = "PartDError")]
enum PartD {
    #[n(0)]
    VariantA {
        a: HashSet<i16>,
        #[cbor(tag(12))]
        b: f32,
    },
    #[n(1)]
    VariantB(BTreeMap<String, usize>, [u8; 16]),
    #[n(2)]
    VariantC,
}

#[derive(Debug, Encode, Decode, CborLen, Arbitrary, PartialEq)]
#[cbor(error = "PartEError")]
#[cbor(
    decode_bound = "T: Decode<'_>",
    encode_bound = "T: Encode",
    len_bound = "T: CborLen"
)]
struct PartE<T, const N: usize>([T; N]);

#[derive(Debug, Encode, Decode, CborLen, Arbitrary, PartialEq)]
struct Complete {
    a: PartA,
    b: PartB,
    c: PartC,
    d: PartD,
    e: PartE<PartD, 3>,
    tag: TagOnly,
}

fn int_strategy() -> impl Strategy<Value = Int> {
    (proptest::num::u64::ANY, proptest::bool::ANY)
        .prop_map(|(bits, negative)| Int { negative, bits })
}

fn simple_strategy() -> impl Strategy<Value = Option<Simple>> {
    proptest::option::of(
        (0u8..=19)
            .prop_union(32..=255)
            .prop_map(|b| Simple::try_from(b).unwrap()),
    )
}

proptest! {
    #![proptest_config(config())]
    #[test]
    fn roundtrip(value in any::<Complete>()) {
        let len = value.cbor_len();
        let buf = tinycbor::to_vec(&value);
        assert_eq!(buf.len(), len);
        let decoded: Complete = Decode::decode(&mut Decoder(&buf)).unwrap();
        assert_eq!(value, decoded);
    }
}

fn config() -> proptest::test_runner::Config {
    proptest::test_runner::Config {
        cases: 500,
        failure_persistence: None,
        ..proptest::test_runner::Config::default()
    }
}
