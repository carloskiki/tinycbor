//! Procedural macros to derive [`tinycbor`](https://docs.rs/tinycbor)'s [`Encode`], [`Decode`], and [`CborLen`]
//! traits.
//!
//! Deriving is supported for `struct`s and `enum`s. The encoding is cannonical whenever possible,
//! and decoding is stricter than with [`ciborium`] or [`minicbor`].
//!
//!
//! [`ciborium`]: https://docs.rs/ciborium
//! [`minicbor`]: https://docs.rs/minicbor
//!
//! # Codec Specification
//!
//! Deriving `Encode`, `Decode` and `CborLen` is supported for `enum`s and `struct`s. This section
//! goes over the representation of these containers, as well as how the attributes modify the
//! behaviour of the macros.
//! 
//! ## Array representation for `struct`s
//!
//! A `struct` is encoded as a CBOR array by default. The fields are encoded in their order
//! of declaration. The `Decode` implementation allows for both definite and indefinite length
//! arrays, but the exact number of fields must be present in both cases. A missing or extra field
//! leads to a decoding error.
//!
//! ```
//! use tinycbor_derive::{Encode, Decode};
//! use tinycbor::{to_vec, Decoder, Token};
//!
//! #[derive(Encode, Decode)]
//! struct Account {
//!     email: String,
//!     username: Option<String>,
//!     password_hash: [u8; 32],
//! }
//!
//! let encoded = to_vec(
//!     &Account {
//!         email: "me@yahoo.com".to_string(),
//!         username: None,
//!         password_hash: [0u8; 32],
//!     }
//! );
//! let tokens = Decoder(&encoded).collect::<Result<Vec<_>, _>>().unwrap();
//!
//! assert_eq!(tokens, vec![
//!     Token::Array(3),
//!     Token::String("me@yahoo.com"),
//!     Token::Null,
//!     Token::Bytes(&[0u8; 32]),
//! ]);
//! ```
//!
//! ## Map representation for `struct`s
//! 
//! A `struct` can alternatively be encoded as a map by adding `#[cbor(map)]` on the container. The
//! fields are encoded as values within a map, with unsigned integers as keys. The `Decode`
//! implementation allows for both definite and indefinite length maps. All fields must be present
//! in the encoded map (unless [`#[cbor(optional)]`](#cboroptional) is used), otherwise a decoding
//! error is returned. An unknown or repeated key causes a decoding error.
//!
//! The key for each field is specified using the `#[n(<u64>)]` or `#[cbor(n(<u64>))]` attribute on
//! the field.
//! 
//! ```
//! use tinycbor_derive::{Encode, Decode};
//! use tinycbor::{to_vec, Decoder, Token};
//!
//! #[derive(Encode, Decode)]
//! #[cbor(map)]
//! struct Account {
//!     #[n(0)]
//!     email: String,
//!     #[n(1)]
//!     username: Option<String>,
//!     #[n(2)]
//!     password_hash: [u8; 32],
//! }
//!
//! let encoded = to_vec(
//!     &Account {
//!         email: "me@yahoo.com".to_string(),
//!         username: None,
//!         password_hash: [0u8; 32],
//!     }
//! );
//! let tokens = Decoder(&encoded).collect::<Result<Vec<_>, _>>().unwrap();
//!
//! assert_eq!(tokens, vec![
//!     Token::Map(3),
//!     Token::Int(0.into()),
//!     Token::String("me@yahoo.com"),
//!     Token::Int(1.into()),
//!     Token::Null,
//!     Token::Int(2.into()),
//!     Token::Bytes(&[0u8; 32]),
//! ]);
//! ```
//!
//! ### `#[cbor(optional)]`
//!
//! If a field implements `Default` and `PartialEq`, it can be marked as optional. When encoding a
//! field marked as optional, the map entry is ommitted if the field value is equal to
//! `Default::default()`. When decoding and the map entry is missing, the field is initialized with
//! `Default::default()`.
//!
//! ```
//! use tinycbor_derive::{Encode, Decode};
//! use tinycbor::{to_vec, Decoder, Token};
//!
//! #[derive(Encode, Decode, PartialEq)]
//! #[cbor(map)]
//! struct Account {
//!    #[n(0)]
//!    email: String,
//!    #[cbor(n(1), optional)]
//!    username: Option<String>,
//!    #[n(2)]
//!    password_hash: [u8; 32],
//! }
//!
//! let encoded = to_vec(
//!     &Account {
//!         email: "me@yahoo.com".to_string(),
//!         username: None,
//!         password_hash: [0u8; 32],
//!     }
//! );
//! let tokens = Decoder(&encoded).collect::<Result<Vec<_>, _>>().unwrap();
//!
//! assert_eq!(tokens, vec![
//!     Token::Map(2),
//!     Token::Int(0u8.into()),
//!     Token::String("me@yahoo.com"),
//!     Token::Int(2u8.into()),
//!     Token::Bytes(&[0u8; 32]),
//! ]);
//! ```
//!
//! ## Representation for `enum`s
//!
//! An `enum` is encoded as a CBOR array. The first element of the array is the variant tag of the
//! enum (a `u64`), followed by the encoded fields of the variant (if any).
//!
//! The variant tag for each variant is specified using the `#[n(<u64>)]` or `#[cbor(n(<u64>))]`
//! attribute on the variant.
//!
//! ```
//! use tinycbor_derive::{Encode, Decode};
//! use tinycbor::{to_vec, Decoder, Token};
//!
//! #[derive(Encode, Decode)]
//! enum Shape {
//!     #[n(0)]
//!     Dot,
//!     #[n(1)]
//!     Circle { radius: f64 },
//!     #[n(2)]
//!     Rectangle { width: f64, height: f64 },
//! }
//!
//! let encoded = to_vec(&Shape::Rectangle { width: 3.0, height: 4.0 });
//! let tokens = Decoder(&encoded).collect::<Result<Vec<_>, _>>().unwrap();
//!
//! assert_eq!(tokens, vec![
//!     Token::Array(3),
//!     Token::Int(2u8.into()),
//!     Token::Float(3.0),
//!     Token::Float(4.0),
//! ]);
//! ```
//!
//! ## Attributes
//!
//! Unless otherwise noted, the attributes should only be specified on the container.
//!
//! ### `#[cbor(error = "<Ident>")]`
//!
//! This attribute gives the name of the error type to be generated when deriving `Decode`. It
//! has no effect when deriving `Encode` or `CborLen`. By default, the error type is named
//! `Error`.
//!
//! ```no_run
//! use tinycbor_derive::{Decode};
//!
//! #[derive(Decode)]
//! #[cbor(error = "PersonError")]
//! struct Person {
//!     name: String,
//!     age: u16,
//! }
//!
//! #[derive(Decode)]
//! struct Company {
//!     name: String,
//!     ceo: Person,
//!     employees: Vec<Person>,
//! }
//!
//! type PersonErrorType = PersonError;
//! type CompanyErrorType = Error;
//! ```
//!
//! The error type generated by the macro uses associated types, which makes the generated
//! documentation cluttered. To make it look normal, use the `-Znormalize-docs` flag on `rustdoc`.
//!
//! ### `#[cbor({encode_,decode_,len_,}bound = "<WherePredicate>")]`
//!
//! Used to provide bounds on the derived implementations of `Encode`, `Decode` and `CborLen`.
//! The `bound` statement applies to all three traits, and the others apply to their respective
//! trait.
//!
//! Note that by default, the macros do not add any bounds to generic type parameters. This
//! requires the user to add necessary bounds manually. The exception to this rule are lifetimes.
//! For `Decode`, the lifetime attached to the trait is bound to outlive all other lifetimes in the
//! type. This translates to:
//! ```no_run
//! # use tinycbor::{Decode, Decoder};
//! # use std::{convert::Infallible, marker::PhantomData};
//! # struct MyType<'a, 'b> { x: PhantomData<&'b &'a ()> }
//! impl <'de, 'a, 'b, /* ... */> Decode<'de> for MyType<'a, 'b, /* ... */>
//! where
//!   'de: 'a + 'b + /* ... */,
//!   // User specified bounds...
//! {
//!     // Implementation...
//!     # type Error = Infallible;
//!     # fn decode(d: &mut Decoder<'de>) -> Result<Self, Self::Error> {
//!     #     unimplemented!()
//!     # }
//! }
//! ```
//!
//! For `decode_bound` the predicate is allowed to use the special lifetime `'_`, which is
//! replaced with the trait input lifetime when deriving `Decode`.
//!
//! ```no_run
//! use std::borrow::Cow;
//! use tinycbor_derive::{Encode, Decode, CborLen};
//! use tinycbor::{Encode, Decode, CborLen};
//!
//! #[derive(Encode, Decode, CborLen)]
//! #[cbor(bound = "L: std::fmt::Debug")]
//! #[cbor(decode_bound = "L: Decode<'_>")]
//! #[cbor(encode_bound = "L: Encode")]
//! #[cbor(len_bound = "L: CborLen")]
//! struct Car<'a, L> {
//!     model: Cow<'a, str>,
//!     kilometers: u64,
//!     license: L,
//! }
//!
//! ```
//!
//! ### `#[cbor(naked)]`
//!
//! Removes the outer CBOR array from the representation. That is, array `struct`s and `enum`s
//! are encoded as their contents only. map `struct`s cannot be marked as naked, as they can
//! have varying lengths.
//!
//! The simplest usecase is to make fieldless `enum`s encode and decode as integers instead of
//! single-element arrays.
//!
//! ```no_run
//! use tinycbor_derive::{Encode, Decode, CborLen};
//! 
//! #[derive(Encode, Decode, CborLen)]
//! #[cbor(naked)]
//! enum Status {
//!    #[n(0)]
//!    Ok,
//!    #[n(1)]
//!    Error,
//!    #[n(2)]
//!    Sunday,
//! }
//! ```
//!
//! When the resulting representation is more than one CBOR element, the type should not be used as
//! part of a larger structure without care. Consider the following example:
//! ```
//! use tinycbor_derive::Encode;
//! use tinycbor::{Decoder, to_vec, Token};
//! 
//! #[derive(Encode)]
//! #[cbor(naked)]
//! struct Danger {
//!     value: u64,
//!     oh_no: i64,
//! }
//!
//! #[derive(Encode)]
//! struct Careless {
//!     value: Danger,
//! }
//!
//! let cbor = to_vec(&Careless { value: Danger { value: 42, oh_no: -7 } });
//! let tokens = Decoder(&cbor).collect::<Result<Vec<_>, _>>().unwrap();
//!
//! // This is probably not what you want!
//! assert_eq!(
//!     tokens,
//!     vec![
//!         Token::Array(1),
//!         Token::Int(42.into()),
//!         Token::Int((-7).into()),
//!     ]
//! );
//! ```
//!
//! ### `#[cbor(tag(<u64>))]`
//!
//! This attribute is allowed on containers _and_ fields. It specifies a CBOR tag that wraps the
//! encoded value.
//!
//! ```no_run
//! use tinycbor_derive::{Encode, Decode, CborLen};
//!
//! #[derive(Encode, Decode, CborLen)]
//! #[cbor(tag(0))]
//! struct SavingsAccount {
//!     unlocked: u64,
//!     #[cbor(tag(55))]
//!     locked: u64,
//!     rate: f32
//! }
//! ```
//!
//! ### `#[cbor({encode_,decode_,len_,}with = "<Type>")]`
//!
//! This attribute is only allowed on fields. It specifies a type that provides custom `Encode`,
//! `Decode` and/or `CborLen` implementations.
//!
//! When deriving `Decode` and using `#[cbor({decode_,}with = "<Type>")]`, `<Type>` must implement
//! `Into<T>`, or have a method named `into` with signature `<Type> -> T`, where `T` is the field
//! type. All occurences of `'_` lifetimes within `<Type>` are replaced with the trait input
//! lifetime.
//!
//! When deriving `Encode` or `CborLen` and using `#[cbor({encode_,len_,}with = "<Type>")]`,
//! `&T` must implement `Into<&<Type>>`.
//! 
//! ```no_run
//! use tinycbor_derive::{Encode, Decode, CborLen};
//!
//! #[derive(Encode, Decode, CborLen)]
//! struct HotelRoom {
//!     #[cbor(decode_with = "u16")]
//!     number: u32,
//!     #[cbor(with = "tinycbor::num::U8")]
//!     floor: u8,
//!     #[cbor(decode_with = "&'_ str")]
//!     name: String,
//!     #[cbor(with = "tinycbor::Encoded<Vec<String>>")]
//!     amenities: Vec<String>,
//! }
//!
//! ```
//!
//! __Interaction with [`#[cbor(optional)]`](#cboroptional)__:
//!
//! With `#[cbor(optional, {encode_,len_,}with = "<Type>")]`, the original field type's
//! `Default` implementation is used for field initialization and encoding checks, rather than the type provided
//! in `with`.
//!
//! A recurring pattern is to use `Option<T>` fields with `#[cbor(optional)]`. Note that in this
//! case, both _"the field is absent"_ and _"the field is present with value `null`"_ are accepted
//! when decoding. If only the former behaviour is desired (i.e., the field being `null` should
//! error), one can use the following:
//! ```no_run
//! use tinycbor_derive::{Encode, Decode};
//!
//! #[derive(Encode, Decode)]
//! #[cbor(map)]
//! struct Account {
//!     #[n(0)]
//!     email: String,
//!     #[cbor(n(1), decode_with = "String", optional)] // Using `decode_with = "String` prevents `null`.
//!     username: Option<String>,
//!     #[n(2)]
//!     password_hash: [u8; 32],
//! }
//! ```

use ast::Container;

extern crate proc_macro;

mod ast;

/// Derive the `tinycbor::Decode` trait.
///
/// See the [crate] documentation for details.
#[proc_macro_derive(Decode, attributes(n, cbor))]
pub fn derive_decode(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let input = syn::parse_macro_input!(input as syn::DeriveInput);
    match Container::try_from(input) {
        Ok(container) => container.decode(),
        Err(e) => e.into_compile_error(),
    }
    .into()
}

/// Derive the `tinycbor::Encode` trait.
///
/// See the [crate] documentation for details.
#[proc_macro_derive(Encode, attributes(n, cbor))]
pub fn derive_encode(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let input = syn::parse_macro_input!(input as syn::DeriveInput);
    match Container::try_from(input) {
        Ok(container) => container.encode(),
        Err(e) => e.into_compile_error(),
    }
    .into()
}

/// Derive the `tinycbor::CborLen` trait.
///
/// See the [crate] documentation for details.
#[proc_macro_derive(CborLen, attributes(n, cbor))]
pub fn derive_cbor_len(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let input = syn::parse_macro_input!(input as syn::DeriveInput);
    match Container::try_from(input) {
        Ok(container) => container.len(),
        Err(e) => e.into_compile_error(),
    }
    .into()
}
