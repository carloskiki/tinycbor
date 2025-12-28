use std::cell::RefCell;

use tinycbor::{num::Int, primitive::{Null, Simple, Undefined}};
use tinycbor_derive::{CborLen, Decode, Encode};


#[derive(Debug, Encode, Decode, PartialEq)]
#[cbor(error = "PartBError", map, tag(2001))]
struct PartB {
    #[n(1)]
    a: Undefined,
    #[cbor(n(14445), optional)]
    b: Option<Simple>,
    #[n(3)]
    c: std::num::Wrapping<i64>,
    #[cbor(n(45), tag(45))]
    d: Int,
    #[cbor(n(5), tag(99), with = "tinycbor::num::U8")]
    e: u8,
}


const _: () = {
    use ::core::convert::{AsRef, Into};
    fn __is_default<T: ::core::default::Default + ::core::cmp::PartialEq>(
        value: &T,
    ) -> bool {
        value == &T::default()
    }
    trait AsRefFallback<T> {
        fn _as_ref(&self) -> &T;
    }
    impl<T, U> AsRefFallback<T> for &U
    where
        U: AsRef<T>,
    {
        fn _as_ref(&self) -> &T {
            self.as_ref()
        }
    }
    #[automatically_derived]
    impl ::tinycbor::CborLen for PartB {
        fn cbor_len(&self) -> usize {
            ::tinycbor::CborLen::cbor_len(&2001u64)
                + {
                    {
                        let Self { a: _a, b: _b, c: _c, d: _d, e: _e } = self;
                        let mut count = 4usize;
                        (<u64 as ::tinycbor::CborLen>::cbor_len(&1u64)
                            + <Undefined as ::tinycbor::CborLen>::cbor_len(_a))
                            + (if !__is_default(_b) {
                                count += 1;
                                <u64 as ::tinycbor::CborLen>::cbor_len(&14445u64)
                                    + <Option<Simple> as ::tinycbor::CborLen>::cbor_len(_b)
                            } else {
                                0
                            })
                            + (<u64 as ::tinycbor::CborLen>::cbor_len(&3u64)
                                + <std::num::Wrapping<
                                    i64,
                                > as ::tinycbor::CborLen>::cbor_len(_c))
                            + (<u64 as ::tinycbor::CborLen>::cbor_len(&45u64)
                                + <::tinycbor::tag::Tagged<
                                    Int,
                                    45u64,
                                > as ::tinycbor::CborLen>::cbor_len(
                                    <&::tinycbor::tag::Tagged<
                                        Int,
                                        45u64,
                                    > as ::core::convert::From<&Int>>::from(_d),
                                ))
                            + (<u64 as ::tinycbor::CborLen>::cbor_len(&5u64)
                                + <::tinycbor::tag::Tagged<
                                    tinycbor::num::U8,
                                    99u64,
                                > as ::tinycbor::CborLen>::cbor_len(
                                    <&::tinycbor::tag::Tagged<
                                        tinycbor::num::U8,
                                        99u64,
                                    > as ::core::convert::From<
                                        &tinycbor::num::U8,
                                    >>::from(_e.into()),
                                )) + <usize as ::tinycbor::CborLen>::cbor_len(&count)
                    }
                }
        }
    }
};

fn main() {}
