#![feature(prelude_import)]
#[macro_use]
extern crate std;
#[prelude_import]
use std::prelude::rust_2024::*;
use tinycbor_derive::{Encode, Decode, CborLen};
use tinycbor::*;
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
#[automatically_derived]
impl ::core::fmt::Debug for Hello {
    #[inline]
    fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
        ::core::fmt::Formatter::write_str(
            f,
            match self {
                Hello::World => "World",
                Hello::People => "People",
                Hello::Guys => "Guys",
                Hello::Folks => "Folks",
            },
        )
    }
}
#[automatically_derived]
impl ::core::marker::StructuralPartialEq for Hello {}
#[automatically_derived]
impl ::core::cmp::PartialEq for Hello {
    #[inline]
    fn eq(&self, other: &Hello) -> bool {
        let __self_discr = ::core::intrinsics::discriminant_value(self);
        let __arg1_discr = ::core::intrinsics::discriminant_value(other);
        __self_discr == __arg1_discr
    }
}
const _: () = {
    use ::core::convert::{AsRef, Into};
    struct __Empty;
    #[automatically_derived]
    impl ::tinycbor::Encode for __Empty {
        fn encode<W: ::tinycbor::Write>(
            &self,
            _e: &mut ::tinycbor::Encoder<W>,
        ) -> Result<(), W::Error> {
            Ok(())
        }
    }
    fn __is_default<T: ::core::default::Default + ::core::cmp::PartialEq>(
        value: &T,
    ) -> bool {
        value == &T::default()
    }
    #[automatically_derived]
    impl ::tinycbor::Encode for Hello {
        #[allow(unreachable_code)]
        fn encode<W: ::tinycbor::Write>(
            &self,
            e: &mut ::tinycbor::Encoder<W>,
        ) -> Result<(), W::Error> {
            match self {
                Self::World {} => {
                    <u64 as ::tinycbor::Encode>::encode(&0u64, e)?;
                    Ok(())
                }
                Self::People {} => {
                    <u64 as ::tinycbor::Encode>::encode(&3u64, e)?;
                    Ok(())
                }
                Self::Guys {} => {
                    <u64 as ::tinycbor::Encode>::encode(&2u64, e)?;
                    Ok(())
                }
                Self::Folks {} => {
                    <u64 as ::tinycbor::Encode>::encode(&1u64, e)?;
                    Ok(())
                }
                _ => ::core::panicking::panic("internal error: entered unreachable code"),
            }
        }
    }
};
const _: () = {
    use ::core::convert::Infallible as __Error;
    struct __Empty;
    #[automatically_derived]
    impl ::tinycbor::Decode<'_> for __Empty {
        type Error = ::core::convert::Infallible;
        fn decode(d: &mut ::tinycbor::Decoder<'_>) -> Result<Self, Self::Error> {
            Ok(__Empty)
        }
    }
    #[automatically_derived]
    impl<'__bytes> ::tinycbor::Decode<'__bytes> for Hello
    where
        '__bytes:,
    {
        type Error = ::tinycbor::tag::Error<::core::convert::Infallible>;
        #[allow(unreachable_code)]
        fn decode(
            d: &mut ::tinycbor::Decoder<'__bytes>,
        ) -> Result<Self, <Self as ::tinycbor::Decode<'__bytes>>::Error> {
            Ok({
                let tag: u64 = ::tinycbor::Decode::decode(d)
                    .map_err(|e| { ::tinycbor::tag::Error::Malformed(e) })?;
                match tag {
                    0u64 => Self::World {},
                    3u64 => Self::People {},
                    2u64 => Self::Guys {},
                    1u64 => Self::Folks {},
                    _ => {
                        return Err(::tinycbor::tag::Error::InvalidTag);
                    }
                }
            })
        }
    }
};
const _: () = {
    use ::core::convert::{AsRef, Into};
    fn __is_default<T: ::core::default::Default + ::core::cmp::PartialEq>(
        value: &T,
    ) -> bool {
        value == &T::default()
    }
    #[automatically_derived]
    impl ::tinycbor::CborLen for Hello {
        fn cbor_len(&self) -> usize {
            {
                match self {
                    Self::World {} => {
                        let mut total_len = <u64 as ::tinycbor::CborLen>::cbor_len(
                            &0u64,
                        );
                        total_len
                    }
                    Self::People {} => {
                        let mut total_len = <u64 as ::tinycbor::CborLen>::cbor_len(
                            &3u64,
                        );
                        total_len
                    }
                    Self::Guys {} => {
                        let mut total_len = <u64 as ::tinycbor::CborLen>::cbor_len(
                            &2u64,
                        );
                        total_len
                    }
                    Self::Folks {} => {
                        let mut total_len = <u64 as ::tinycbor::CborLen>::cbor_len(
                            &1u64,
                        );
                        total_len
                    }
                    _ => {
                        ::core::panicking::panic(
                            "internal error: entered unreachable code",
                        )
                    }
                }
            }
        }
    }
};
#[cbor(naked)]
pub struct Wrapper(u64);
#[automatically_derived]
impl ::core::fmt::Debug for Wrapper {
    #[inline]
    fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
        ::core::fmt::Formatter::debug_tuple_field1_finish(f, "Wrapper", &&self.0)
    }
}
#[automatically_derived]
impl ::core::marker::StructuralPartialEq for Wrapper {}
#[automatically_derived]
impl ::core::cmp::PartialEq for Wrapper {
    #[inline]
    fn eq(&self, other: &Wrapper) -> bool {
        self.0 == other.0
    }
}
const _: () = {
    use ::core::convert::{AsRef, Into};
    struct __Empty;
    #[automatically_derived]
    impl ::tinycbor::Encode for __Empty {
        fn encode<W: ::tinycbor::Write>(
            &self,
            _e: &mut ::tinycbor::Encoder<W>,
        ) -> Result<(), W::Error> {
            Ok(())
        }
    }
    fn __is_default<T: ::core::default::Default + ::core::cmp::PartialEq>(
        value: &T,
    ) -> bool {
        value == &T::default()
    }
    #[automatically_derived]
    impl ::tinycbor::Encode for Wrapper {
        #[allow(unreachable_code)]
        fn encode<W: ::tinycbor::Write>(
            &self,
            e: &mut ::tinycbor::Encoder<W>,
        ) -> Result<(), W::Error> {
            let Self { 0: _0 } = self;
            {
                <u64 as ::tinycbor::Encode>::encode(_0, e)?;
            }
            return Ok(());
        }
    }
};
const _: () = { (/*ERROR*/) };
const _: () = {
    use ::core::convert::{AsRef, Into};
    fn __is_default<T: ::core::default::Default + ::core::cmp::PartialEq>(
        value: &T,
    ) -> bool {
        value == &T::default()
    }
    #[automatically_derived]
    impl ::tinycbor::CborLen for Wrapper {
        fn cbor_len(&self) -> usize {
            {
                let Self { 0: _0 } = self;
                <u64 as ::tinycbor::CborLen>::cbor_len(_0)
            }
        }
    }
};
extern crate test;
#[rustc_test_marker = "roundtrip"]
#[doc(hidden)]
pub const roundtrip: test::TestDescAndFn = test::TestDescAndFn {
    desc: test::TestDesc {
        name: test::StaticTestName("roundtrip"),
        ignore: false,
        ignore_message: ::core::option::Option::None,
        source_file: "tests/naked.rs",
        start_line: 22usize,
        start_col: 4usize,
        end_line: 22usize,
        end_col: 13usize,
        compile_fail: false,
        no_run: false,
        should_panic: test::ShouldPanic::No,
        test_type: test::TestType::IntegrationTest,
    },
    testfn: test::StaticTestFn(#[coverage(off)] || test::assert_test_result(roundtrip())),
};
fn roundtrip() {
    let value = Wrapper(42);
    let encoded = to_vec(&value);
    let decoded: Wrapper = Decode::decode(&mut Decoder(&encoded)).unwrap();
    match (&value, &decoded) {
        (left_val, right_val) => {
            if !(*left_val == *right_val) {
                let kind = ::core::panicking::AssertKind::Eq;
                ::core::panicking::assert_failed(
                    kind,
                    &*left_val,
                    &*right_val,
                    ::core::option::Option::None,
                );
            }
        }
    };
    let value = Hello::People;
    let encoded = to_vec(&value);
    let decoded: Hello = Decode::decode(&mut Decoder(&encoded)).unwrap();
    match (&value, &decoded) {
        (left_val, right_val) => {
            if !(*left_val == *right_val) {
                let kind = ::core::panicking::AssertKind::Eq;
                ::core::panicking::assert_failed(
                    kind,
                    &*left_val,
                    &*right_val,
                    ::core::option::Option::None,
                );
            }
        }
    };
}
#[rustc_main]
#[coverage(off)]
#[doc(hidden)]
pub fn main() -> () {
    extern crate test;
    test::test_main_static(&[&roundtrip])
}
