#![feature(prelude_import)]
#[macro_use]
extern crate std;
#[prelude_import]
use std::prelude::rust_2024::*;
use std::cell::RefCell;
use tinycbor::{num::Int, primitive::{Null, Simple, Undefined}};
use tinycbor_derive::{CborLen, Decode, Encode};
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
#[automatically_derived]
impl ::core::fmt::Debug for PartB {
    #[inline]
    fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
        ::core::fmt::Formatter::debug_struct_field5_finish(
            f,
            "PartB",
            "a",
            &self.a,
            "b",
            &self.b,
            "c",
            &self.c,
            "d",
            &self.d,
            "e",
            &&self.e,
        )
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
    impl ::tinycbor::Encode for PartB {
        #[allow(unreachable_code)]
        fn encode<W: ::tinycbor::Write>(
            &self,
            e: &mut ::tinycbor::Encoder<W>,
        ) -> Result<(), W::Error> {
            ::tinycbor::Encode::encode(
                &::tinycbor::tag::Tagged::<__Empty, 2001u64>(__Empty),
                e,
            )?;
            let Self { a: _a, b: _b, c: _c, d: _d, e: _e } = self;
            e.map({
                let mut count = 4usize;
                if !__is_default(_b) {
                    count += 1;
                }
                count
            })?;
            <u64 as ::tinycbor::Encode>::encode(&1u64, e)?;
            {
                <Undefined as ::tinycbor::Encode>::encode(_a, e)?;
            }
            if !__is_default(_b) {
                <u64 as ::tinycbor::Encode>::encode(&14445u64, e)?;
                {
                    <Option<Simple> as ::tinycbor::Encode>::encode(_b, e)?;
                }
            }
            <u64 as ::tinycbor::Encode>::encode(&3u64, e)?;
            {
                <std::num::Wrapping<i64> as ::tinycbor::Encode>::encode(_c, e)?;
            }
            <u64 as ::tinycbor::Encode>::encode(&45u64, e)?;
            {
                <::tinycbor::tag::Tagged<
                    Int,
                    45u64,
                > as ::tinycbor::Encode>::encode(
                    <&::tinycbor::tag::Tagged<
                        Int,
                        45u64,
                    > as ::core::convert::From<&Int>>::from(_d),
                    e,
                )?;
            }
            <u64 as ::tinycbor::Encode>::encode(&5u64, e)?;
            {
                <::tinycbor::tag::Tagged<
                    tinycbor::num::U8,
                    99u64,
                > as ::tinycbor::Encode>::encode(
                    <&::tinycbor::tag::Tagged<
                        tinycbor::num::U8,
                        99u64,
                    > as ::core::convert::From<&tinycbor::num::U8>>::from(_e.into()),
                    e,
                )?;
            }
            return Ok(());
            let Self { a: _a, b: _b, c: _c, d: _d, e: _e } = self;
            e.map({
                let mut count = 4usize;
                if !__is_default(_b) {
                    count += 1;
                }
                count
            })?;
            <u64 as ::tinycbor::Encode>::encode(&1u64, e)?;
            {
                <Undefined as ::tinycbor::Encode>::encode(_a, e)?;
            }
            if !__is_default(_b) {
                <u64 as ::tinycbor::Encode>::encode(&14445u64, e)?;
                {
                    <Option<Simple> as ::tinycbor::Encode>::encode(_b, e)?;
                }
            }
            <u64 as ::tinycbor::Encode>::encode(&3u64, e)?;
            {
                <std::num::Wrapping<i64> as ::tinycbor::Encode>::encode(_c, e)?;
            }
            <u64 as ::tinycbor::Encode>::encode(&45u64, e)?;
            {
                <::tinycbor::tag::Tagged<
                    Int,
                    45u64,
                > as ::tinycbor::Encode>::encode(
                    <&::tinycbor::tag::Tagged<
                        Int,
                        45u64,
                    > as ::core::convert::From<&Int>>::from(_d),
                    e,
                )?;
            }
            <u64 as ::tinycbor::Encode>::encode(&5u64, e)?;
            {
                <::tinycbor::tag::Tagged<
                    tinycbor::num::U8,
                    99u64,
                > as ::tinycbor::Encode>::encode(
                    <&::tinycbor::tag::Tagged<
                        tinycbor::num::U8,
                        99u64,
                    > as ::core::convert::From<&tinycbor::num::U8>>::from(_e.into()),
                    e,
                )?;
            }
            return Ok(());
        }
    }
};
enum PartBError {
    A(<Undefined as ::tinycbor::Decode<'static>>::Error),
    B(<Option<Simple> as ::tinycbor::Decode<'static>>::Error),
    C(<std::num::Wrapping<i64> as ::tinycbor::Decode<'static>>::Error),
    D(<::tinycbor::tag::Tagged<Int, 45u64> as ::tinycbor::Decode<'static>>::Error),
    E(
        <::tinycbor::tag::Tagged<
            tinycbor::num::U8,
            99u64,
        > as ::tinycbor::Decode<'static>>::Error,
    ),
}
#[automatically_derived]
impl ::core::fmt::Debug for PartBError {
    #[inline]
    fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
        match self {
            PartBError::A(__self_0) => {
                ::core::fmt::Formatter::debug_tuple_field1_finish(f, "A", &__self_0)
            }
            PartBError::B(__self_0) => {
                ::core::fmt::Formatter::debug_tuple_field1_finish(f, "B", &__self_0)
            }
            PartBError::C(__self_0) => {
                ::core::fmt::Formatter::debug_tuple_field1_finish(f, "C", &__self_0)
            }
            PartBError::D(__self_0) => {
                ::core::fmt::Formatter::debug_tuple_field1_finish(f, "D", &__self_0)
            }
            PartBError::E(__self_0) => {
                ::core::fmt::Formatter::debug_tuple_field1_finish(f, "E", &__self_0)
            }
        }
    }
}
const _: () = {
    use PartBError as __Error;
    #[automatically_derived]
    impl ::core::fmt::Display for __Error {
        fn fmt(&self, formatter: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
            formatter.write_fmt(format_args!("in {0}: ", "PartB"))?;
            match self {
                __Error::A(_0) => {
                    formatter.write_fmt(format_args!("in field `a`: {0}", _0))
                }
                __Error::B(_0) => {
                    formatter.write_fmt(format_args!("in field `b`: {0}", _0))
                }
                __Error::C(_0) => {
                    formatter.write_fmt(format_args!("in field `c`: {0}", _0))
                }
                __Error::D(_0) => {
                    formatter.write_fmt(format_args!("in field `d`: {0}", _0))
                }
                __Error::E(_0) => {
                    formatter.write_fmt(format_args!("in field `e`: {0}", _0))
                }
                _ => ::core::panicking::panic("internal error: entered unreachable code"),
            }
        }
    }
    #[automatically_derived]
    impl ::core::error::Error for __Error {
        fn source(&self) -> Option<&(dyn ::core::error::Error + 'static)> {
            match self {
                __Error::A(_0) => ::core::option::Option::Some(_0),
                __Error::B(_0) => ::core::option::Option::Some(_0),
                __Error::C(_0) => ::core::option::Option::Some(_0),
                __Error::D(_0) => ::core::option::Option::Some(_0),
                __Error::E(_0) => ::core::option::Option::Some(_0),
                _ => ::core::panicking::panic("internal error: entered unreachable code"),
            }
        }
    }
    struct __Empty;
    #[automatically_derived]
    impl ::tinycbor::Decode<'_> for __Empty {
        type Error = ::core::convert::Infallible;
        fn decode(d: &mut ::tinycbor::Decoder<'_>) -> Result<Self, Self::Error> {
            Ok(__Empty)
        }
    }
    #[automatically_derived]
    impl<'__bytes> ::tinycbor::Decode<'__bytes> for PartB
    where
        '__bytes:,
    {
        type Error = ::tinycbor::tag::Error<
            ::tinycbor::collections::fixed::Error<
                ::tinycbor::collections::map::Error<
                    ::tinycbor::primitive::Error,
                    __Error,
                >,
            >,
        >;
        #[allow(unreachable_code)]
        fn decode(d: &mut ::tinycbor::Decoder<'__bytes>) -> Result<Self, Self::Error> {
            match <::tinycbor::tag::Tagged<
                __Empty,
                2001u64,
            > as ::tinycbor::Decode<'__bytes>>::decode(d) {
                Ok(_) => {}
                Err(::tinycbor::tag::Error::InvalidTag) => {
                    return Err(::tinycbor::tag::Error::InvalidTag);
                }
                Err(::tinycbor::tag::Error::Malformed(e)) => {
                    return Err(::tinycbor::tag::Error::Malformed(e));
                }
            }
            (|| {
                let mut _a: ::core::option::Option<Undefined> = ::core::option::Option::None;
                let mut _b: ::core::option::Option<Option<Simple>> = ::core::option::Option::None;
                let mut _c: ::core::option::Option<std::num::Wrapping<i64>> = ::core::option::Option::None;
                let mut _d: ::core::option::Option<Int> = ::core::option::Option::None;
                let mut _e: ::core::option::Option<u8> = ::core::option::Option::None;
                let mut visitor = d
                    .map_visitor()
                    .map_err(|e| {
                        ::tinycbor::collections::fixed::Error::Collection(
                            ::tinycbor::collections::Error::Malformed(e),
                        )
                    })?;
                loop {
                    if _a.is_some() && _b.is_some() && _c.is_some() && _d.is_some()
                        && _e.is_some() && true
                    {
                        if visitor.remaining() != Some(0) {
                            return Err(::tinycbor::collections::fixed::Error::Surplus);
                        }
                        break;
                    }
                    let ::core::option::Option::Some(result) = visitor
                        .with_key::<
                            ::core::primitive::u64,
                            _,
                            _,
                        >(|k, d| -> Result<bool, _> {
                            match ::core::primitive::u64::from(k) {
                                1u64 if _a.is_none() => {
                                    _a = ::core::option::Option::Some(
                                        <Undefined as ::tinycbor::Decode<'__bytes>>::decode(d)
                                            .map_err(|e| __Error::A(e))?,
                                    );
                                }
                                14445u64 if _b.is_none() => {
                                    _b = ::core::option::Option::Some(
                                        <Option<Simple> as ::tinycbor::Decode<'__bytes>>::decode(d)
                                            .map_err(|e| __Error::B(e))?,
                                    );
                                }
                                3u64 if _c.is_none() => {
                                    _c = ::core::option::Option::Some(
                                        <std::num::Wrapping<
                                            i64,
                                        > as ::tinycbor::Decode<'__bytes>>::decode(d)
                                            .map_err(|e| __Error::C(e))?,
                                    );
                                }
                                45u64 if _d.is_none() => {
                                    _d = ::core::option::Option::Some(
                                        <::tinycbor::tag::Tagged<
                                            Int,
                                            45u64,
                                        > as ::tinycbor::Decode<'__bytes>>::decode(d)
                                            .map_err(|e| __Error::D(e))?
                                            .0,
                                    );
                                }
                                5u64 if _e.is_none() => {
                                    _e = ::core::option::Option::Some(
                                        <::tinycbor::tag::Tagged<
                                            tinycbor::num::U8,
                                            99u64,
                                        > as ::tinycbor::Decode<'__bytes>>::decode(d)
                                            .map_err(|e| __Error::E(e))?
                                            .0
                                            .into(),
                                    );
                                }
                                _ => return Ok(false),
                            };
                            #[allow(unreachable_code)] Ok(true)
                        }) else {
                        break;
                    };
                    match result {
                        ::core::result::Result::Ok(
                            ::core::result::Result::Err(value_err),
                        ) => {
                            return ::core::result::Result::Err(
                                ::tinycbor::collections::fixed::Error::Collection(
                                    ::tinycbor::collections::Error::Element(
                                        ::tinycbor::collections::map::Error::Value(value_err),
                                    ),
                                ),
                            );
                        }
                        ::core::result::Result::Err(key_err) => {
                            return ::core::result::Result::Err(
                                ::tinycbor::collections::fixed::Error::Collection(
                                    ::tinycbor::collections::Error::Element(
                                        ::tinycbor::collections::map::Error::Key(key_err),
                                    ),
                                ),
                            );
                        }
                        ::core::result::Result::Ok(::core::result::Result::Ok(false)) => {
                            return ::core::result::Result::Err(
                                ::tinycbor::collections::fixed::Error::Surplus,
                            );
                        }
                        _ => {}
                    }
                }
                Ok(Self {
                    a: _a.ok_or(::tinycbor::collections::fixed::Error::Missing)?,
                    b: _b.unwrap_or_default(),
                    c: _c.ok_or(::tinycbor::collections::fixed::Error::Missing)?,
                    d: _d.ok_or(::tinycbor::collections::fixed::Error::Missing)?,
                    e: _e.ok_or(::tinycbor::collections::fixed::Error::Missing)?,
                })
            })()
                .map_err(|e| { ::tinycbor::tag::Error::Inner(e) })
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
            ::tinycbor::CborLen(&2001u64)
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
#[automatically_derived]
impl ::core::marker::StructuralPartialEq for PartB {}
#[automatically_derived]
impl ::core::cmp::PartialEq for PartB {
    #[inline]
    fn eq(&self, other: &PartB) -> bool {
        self.e == other.e && self.a == other.a && self.b == other.b && self.c == other.c
            && self.d == other.d
    }
}
fn main() {}
