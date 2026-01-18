use std::collections::HashSet;

use proc_macro2::{Span, TokenStream};
use quote::{ToTokens as _, quote};
use syn::{Ident, spanned::Spanned as _, visit_mut::VisitMut};

mod field;
mod variant;

pub use field::{Field, MapField};

use crate::ast::{field::parse_fields, variant::Variant};

/// A container that derives `Encode`, `Decode`, or `CborLen`.
pub struct Container {
    pub tag: Option<u64>,
    pub bounds: Bounds,
    pub data: Data,
    pub error: syn::Ident,
    pub recursive: bool,
    pub original: syn::DeriveInput,
}

impl Container {
    pub fn decode(self) -> TokenStream {
        let Container {
            tag,
            bounds:
                Bounds {
                    bound,
                    decode_bound,
                    ..
                },
            data,
            original:
                syn::DeriveInput {
                    ident,
                    mut generics,
                    ..
                },
            error,
            recursive,
        } = self;

        let (_, ty_generics, _) = generics.split_for_impl();
        let ty_generics = quote! { #ty_generics };

        let (error_def, error_impl) = data.error_def(&error, &ident).unzip();
        let error_import = if error_def.is_some() {
            quote! { use #error as __Error; }
        } else {
            quote! { use ::core::convert::Infallible as __Error; }
        };
        let mut error_ty = data.error_ty();

        let lifetimes = generics
            .lifetimes()
            .map(|lifetime| lifetime.lifetime.clone())
            .collect::<Vec<_>>();
        generics.params.push(syn::parse_quote! { '__bytes });
        let where_clause = generics.make_where_clause();
        where_clause.predicates.push(syn::parse_quote! {
            '__bytes: #(#lifetimes)+*
        });
        where_clause.predicates.extend(bound);
        where_clause.predicates.extend(decode_bound);

        let (impl_generics_lifetime, _, where_clause_lifetime) = generics.split_for_impl();
        let mut procedure = data.decode();
        if let Some(tag) = tag {
            procedure = quote! {
                <::tinycbor::tag::Tagged<__Empty, #tag> as ::tinycbor::Decode<'__bytes>>::decode(d).map_err(|e| {
                    e.map(|e| match e {})
                })?;
                (|| { #procedure })().map_err(|e| {
                    ::tinycbor::tag::Error::Content(e)
                })
            };

            error_ty = quote! { ::tinycbor::tag::Error<#error_ty> };
        }
        if recursive {
            procedure = quote! {
                (|| { #procedure })().map_err(|e| {
                    ::alloc::boxed::Box::new(e)
                })
            };

            error_ty = quote! { ::alloc::boxed::Box<#error_ty> };
        }

        quote! {
            #error_def

            const _: () = {
                #error_import

                #error_impl

                struct __Empty;
                #[automatically_derived]
                impl ::tinycbor::Decode<'_> for __Empty {
                    type Error = ::core::convert::Infallible;
                    fn decode(d: &mut ::tinycbor::Decoder<'_>) -> Result<Self, Self::Error> {
                        Ok(__Empty)
                    }
                }

                #[automatically_derived]
                impl #impl_generics_lifetime ::tinycbor::Decode<'__bytes> for #ident #ty_generics
                    #where_clause_lifetime
                {
                    type Error = #error_ty;

                    #[allow(unreachable_code)]
                    fn decode(
                        d: &mut ::tinycbor::Decoder<'__bytes>,
                    ) -> Result<Self, <Self as ::tinycbor::Decode<'__bytes>>::Error> {
                        #procedure
                    }
                }

            };
        }
    }

    pub fn encode(self) -> TokenStream {
        let Container {
            tag,
            bounds:
                Bounds {
                    bound,
                    encode_bound,
                    ..
                },
            data,
            original:
                syn::DeriveInput {
                    ident,
                    mut generics,
                    ..
                },
            ..
        } = self;
        let where_clause = generics.make_where_clause();
        where_clause.predicates.extend(bound);
        where_clause.predicates.extend(encode_bound);

        let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

        let procedure = data.encode();
        let tag = tag.map(|tag| {
            quote! {
                ::tinycbor::Encode::encode(&::tinycbor::tag::Tagged::<__Empty, #tag>(__Empty), e)?;
            }
        });

        let is_default = is_default();

        quote! {
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

                #is_default

                #[automatically_derived]
                impl #impl_generics ::tinycbor::Encode for #ident #ty_generics
                    #where_clause
                {
                    #[allow(unreachable_code)]
                    fn encode<W: ::tinycbor::Write>(
                        &self,
                        e: &mut ::tinycbor::Encoder<W>,
                    ) -> Result<(), W::Error> {
                        #tag
                        #procedure
                    }
                }
            };
        }
    }

    pub fn len(self) -> TokenStream {
        let Container {
            tag,
            bounds: Bounds {
                bound, len_bound, ..
            },
            data,
            original:
                syn::DeriveInput {
                    ident,
                    mut generics,
                    ..
                },
            ..
        } = self;
        let where_clause = generics.make_where_clause();
        where_clause.predicates.extend(bound);
        where_clause.predicates.extend(len_bound);
        let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

        let tag = tag.map(|t| quote! { ::tinycbor::CborLen::cbor_len(&#t) + });

        let procedure = data.len();

        let is_default = is_default();

        quote! {

            const _: () = {
                use ::core::convert::{AsRef, Into};

                #is_default

                #[automatically_derived]
                impl #impl_generics ::tinycbor::CborLen for #ident #ty_generics
                    #where_clause
                {
                    fn cbor_len(
                        &self,
                    ) -> usize {
                        #tag { #procedure }
                    }
                }
            };
        }
    }
}

impl TryFrom<syn::DeriveInput> for Container {
    type Error = syn::Error;

    fn try_from(input: syn::DeriveInput) -> Result<Self, Self::Error> {
        let mut tag = None;
        let mut bounds = Bounds::default();
        let mut map = false;
        let mut naked = false;
        let mut recursive = false;
        let mut error = None;

        for attr in &input.attrs {
            if !attr.path().is_ident("cbor") {
                continue;
            }
            attr.parse_nested_meta(|meta| {
                if bounds.update(&meta)? || tag_update(&mut tag, &meta)? {
                    return Ok(());
                }
                if meta.path.is_ident("map") {
                    map = true;
                    return Ok(());
                } else if meta.path.is_ident("naked") {
                    naked = true;
                    return Ok(());
                } else if meta.path.is_ident("recursive") {
                    recursive = true;
                    return Ok(());
                } else if meta.path.is_ident("error") {
                    if error.is_some() {
                        return Err(meta.error("duplicate `error` attribute"));
                    }
                    let val: syn::LitStr = meta.value()?.parse()?;
                    let ident: syn::Ident = val.parse()?;
                    error = Some(ident);

                    return Ok(());
                }

                Err(meta.error("unknown attribute"))
            })?;
        }

        let data = match input.data {
            syn::Data::Struct(ref data) => {
                if map {
                    if naked {
                        return Err(syn::Error::new_spanned(
                            input.ident,
                            "`naked` attribute is not applicable to map structs",
                        ));
                    }

                    let fields = data
                        .fields
                        .iter()
                        .zip(data.fields.members())
                        .map(|(f, member)| MapField::parse(f, member, &input.generics))
                        .collect::<syn::Result<Vec<_>>>()?;
                    // Check for duplicate indices
                    let mut existing = HashSet::<u64>::new();
                    for field in &fields {
                        if !existing.insert(field.index) {
                            return Err(syn::Error::new_spanned(
                                &field.field.member,
                                format!("Duplicate map index: {}", field.index),
                            ));
                        }
                    }
                    Data::Map(fields)
                } else {
                    Data::Array {
                        fields: parse_fields(&data.fields, &input.generics)?,
                        naked,
                    }
                }
            }
            syn::Data::Enum(ref data) => {
                if map {
                    return Err(syn::Error::new_spanned(
                        input.ident,
                        "`map` attribute is only applicable to structs",
                    ));
                } else {
                    // TODO: uniqueness of tags?
                    Data::Enum {
                        variants: data
                            .variants
                            .iter()
                            .map(|v| Variant::parse(v, &input.generics))
                            .collect::<syn::Result<Vec<_>>>()?,
                        naked,
                    }
                }
            }
            syn::Data::Union(_) => {
                return Err(syn::Error::new_spanned(
                    input.ident,
                    "unions are not supported",
                ));
            }
        };

        Ok(Container {
            tag,
            bounds,
            data,
            original: input,
            error: error.unwrap_or_else(|| Ident::new("Error", Span::call_site())),
            recursive,
        })
    }
}

pub enum Data {
    Array { fields: Vec<Field>, naked: bool },
    Map(Vec<MapField>),
    Enum { variants: Vec<Variant>, naked: bool },
}

impl Data {
    pub fn error_def(
        &self,
        error_name: &syn::Ident,
        name: &syn::Ident,
    ) -> Option<(TokenStream, TokenStream)> {
        // Returns (display_arms, error_arms)
        fn _impl(iter: impl Iterator<Item = (String, syn::Ident)>) -> (TokenStream, TokenStream) {
            iter.map(|(message, variant_name)| {
                (
                    quote! {
                        __Error::#variant_name(_0) => ::core::write!(formatter, #message),
                    },
                    quote! {
                        __Error::#variant_name(_0) => ::core::option::Option::Some(_0),
                    },
                )
            })
            .collect::<(TokenStream, TokenStream)>()
        }
        let struct_impl = (
            quote! {
                __Error(_0) => ::core::write!(formatter, "{}", _0),
            },
            quote! {
                __Error(_0) => ::core::option::Option::Some(_0),
            },
        );

        let mut generic_count = 0usize;
        let mut variant_ty = |field: &Field| {
            if field.generic {
                generic_count += 1;
                quote::format_ident!("E{}", generic_count - 1).to_token_stream()
            } else {
                struct LifetimeReplacer;
                impl VisitMut for LifetimeReplacer {
                    fn visit_lifetime_mut(&mut self, lt: &mut syn::Lifetime) {
                        *lt = syn::parse_quote! { 'static }
                    }
                }

                let mut ty = syn::parse2(field.decode_ty()).expect("valid type");
                LifetimeReplacer.visit_type_mut(&mut ty);
                quote! { <#ty as ::tinycbor::Decode<'static>>::Error }
            }
        };

        let error_generics = self.error_generics();
        let (is_enum, content, (display_arms, error_arms)) = match self {
            Data::Array { fields, .. } if fields.len() > 1 => (
                true,
                {
                    let variants = fields
                        .iter()
                        .map(|f| {
                            let ty = variant_ty(f);
                            let name = f.error_name();
                            quote! {
                                #name(#ty),
                            }
                        })
                        .collect::<TokenStream>();
                    quote! { { #variants } }
                },
                _impl(fields.iter().map(|f| (f.error_message(), f.error_name()))),
            ),
            Data::Map(map_fields) if map_fields.len() > 1 => (
                true,
                {
                    let variants = map_fields
                        .iter()
                        .map(|mf| {
                            let ty = variant_ty(&mf.field);
                            let name = mf.field.error_name();
                            quote! {
                                #name(#ty),
                            }
                        })
                        .collect::<TokenStream>();
                    quote! { { #variants } }
                },
                _impl(
                    map_fields
                        .iter()
                        .map(|mf| (mf.field.error_message(), mf.field.error_name())),
                ),
            ),
            Data::Array { fields, .. } if fields.len() == 1 => (
                false,
                {
                    let ty = variant_ty(&fields[0]);
                    quote! { (pub #ty); }
                },
                struct_impl.clone(),
            ),
            Data::Map(map_fields) if map_fields.len() == 1 => (
                false,
                {
                    let ty = variant_ty(&map_fields[0].field);
                    quote! { (pub #ty); }
                },
                struct_impl.clone(),
            ),
            Data::Enum { variants, .. } => {
                let (tokens, impl_material) = variants
                    .iter()
                    .flat_map(|v| {
                        let field_count = v.fields.len();
                        v.fields
                            .iter()
                            .map(|f| {
                                let ty = variant_ty(f);
                                let ident = &v.ident;
                                let name = if field_count == 1 {
                                    ident.clone()
                                } else {
                                    quote::format_ident!("{}{}", ident, f.error_name())
                                };
                                let message =
                                    format!("{} of variant `{}`", f.error_message(), ident);
                                (
                                    quote! {
                                        #name(#ty),
                                    },
                                    (message, name),
                                )
                            })
                            .collect::<Vec<_>>()
                    })
                    .collect::<(TokenStream, Vec<(String, Ident)>)>();
                if tokens.is_empty() {
                    return None;
                }
                (
                    true,
                    quote! { { #tokens } },
                    _impl(impl_material.into_iter()),
                )
            }
            _ => return None,
        };

        let container = match is_enum {
            true => quote! { enum },
            false => quote! { struct },
        };

        let definition = quote! {
            #[derive(::core::fmt::Debug)]
            pub #container #error_name <#(#error_generics),*> #content
        };

        let (diplay_bounds, error_bounds) = error_generics
            .iter()
            .map(|ty| {
                (
                    quote! { #ty: ::core::fmt::Display, },
                    quote! { #ty: ::core::error::Error + 'static, },
                )
            })
            .collect::<(TokenStream, TokenStream)>();
        let generics = quote! { <#(#error_generics),*> };
        let _impl = quote! {
            #[automatically_derived]
            impl #generics ::core::fmt::Display for __Error #generics
                where #diplay_bounds
            {

                fn fmt(&self, formatter: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
                    match self {
                        #display_arms
                        _ => ::core::unreachable!(),
                    }?;
                    ::core::write!(formatter, " in type `{}`", stringify!(#name))
                }
            }

            #[automatically_derived]
            impl #generics ::core::error::Error for __Error #generics
                where #error_bounds
            {
                fn source(&self) -> Option<&(dyn ::core::error::Error + 'static)> {
                    match self {
                        #error_arms
                        _ => ::core::unreachable!(),
                    }
                }
            }
        };
        Some((definition, _impl))
    }

    pub fn error_ty(&self) -> TokenStream {
        match self {
            Data::Array { fields, naked } => {
                let generic_tys = fields
                    .iter()
                    .filter_map(|f| {
                        if f.generic {
                            let ty = f.decode_ty();
                            Some(quote! { <#ty as ::tinycbor::Decode<'__bytes>>::Error })
                        } else {
                            None
                        }
                    })
                    .collect::<Vec<_>>();

                let mut error_ty = quote! { __Error<#(#generic_tys),*> };
                if !naked {
                    error_ty = quote! { ::tinycbor::container::Error<::tinycbor::container::bounded::Error<#error_ty>> };
                }
                error_ty
            }
            Data::Map(fields) => {
                let generic_tys = fields.iter().filter_map(|f| {
                    if f.field.generic {
                        let ty = f.field.decode_ty();
                        Some(quote! { <#ty as ::tinycbor::Decode<'__bytes>>::Error })
                    } else {
                        None
                    }
                });
                quote! {
                    ::tinycbor::container::Error<::tinycbor::container::bounded::Error<
                        ::tinycbor::container::map::Error<
                            ::tinycbor::primitive::Error, __Error<#(#generic_tys),*>
                        >
                    >>
                }
            }
            Data::Enum { variants, naked } => {
                let generic_tys = variants.iter().flat_map(|v| {
                    v.fields.iter().filter_map(|f| {
                        if f.generic {
                            let ty = f.decode_ty();
                            Some(quote! { <#ty as ::tinycbor::Decode<'__bytes>>::Error })
                        } else {
                            None
                        }
                    })
                });

                let mut error_ty = quote! {
                    ::tinycbor::tag::Error<__Error<#(#generic_tys),*>>
                };
                if !naked {
                    error_ty = quote! { ::tinycbor::container::Error<::tinycbor::container::bounded::Error<#error_ty>> };
                }
                error_ty
            }
        }
    }

    pub fn decode(self) -> TokenStream {
        match self {
            Data::Array { fields, naked } => {
                let field_count = fields.len();
                let fields = fields.into_iter().map(|f| {
                    let error_constructor = if field_count == 1 {
                        quote! { __Error(e) }
                    } else {
                        let error_name = f.error_name();
                        quote! { __Error::#error_name(e) }
                    };

                    f.decode(&error_constructor, naked)
                });
                let procedure = quote! {
                    Ok(Self {
                        #(#fields),*
                    })
                };
                if naked {
                    return procedure;
                }
                quote! {
                    let mut visitor = d.array_visitor().map_err(|e| {
                        ::tinycbor::container::Error::Malformed(e)
                    })?;
                    let result = #procedure;
                    if visitor.remaining() != Some(0) {
                        Err(::tinycbor::container::Error::Content(::tinycbor::container::bounded::Error::Surplus))?;
                    }
                    result
                }
            }
            Data::Map(map_fields) => {
                let field_count = map_fields.len();
                let variables: Vec<Ident> = map_fields.iter().map(|f| f.field.variable()).collect();
                let (variable_defs, arms, constructors): (
                    Vec<TokenStream>,
                    Vec<TokenStream>,
                    Vec<TokenStream>,
                ) = map_fields
                    .into_iter()
                    .map(|f| f.decode(field_count == 1))
                    .collect();

                quote! {
                    #(#variable_defs)*

                    let mut visitor = d.map_visitor().map_err(|e| {
                        ::tinycbor::container::Error::Malformed(e)
                    })?;
                    loop {
                        if #(#variables.is_some() &&)* true {
                            if visitor.remaining() != Some(0) {
                                return Err(::tinycbor::container::Error::Content(::tinycbor::container::bounded::Error::Surplus));
                            }
                            break;
                        }
                        let ::core::option::Option::Some(result) = visitor.with_key::<::core::primitive::u64, _, _>(
                            |k, d| -> Result<bool, _> {
                                match ::core::primitive::u64::from(k) {
                                    #(#arms)*
                                    _ => return Ok(false),
                                };
                                #[allow(unreachable_code)]
                                Ok(true)
                            }) else {
                            break;
                        };
                        match result {
                            ::core::result::Result::Ok(::core::result::Result::Err(value_err)) =>
                            return ::core::result::Result::Err(::tinycbor::container::Error::Content(
                                    ::tinycbor::container::bounded::Error::Content(
                                        ::tinycbor::container::map::Error::Value(
                                            value_err
                                        )
                                    )
                                )
                            ),
                            ::core::result::Result::Err(key_err) =>
                            return ::core::result::Result::Err(::tinycbor::container::Error::Content(
                                    ::tinycbor::container::bounded::Error::Content(
                                        ::tinycbor::container::map::Error::Key(
                                            key_err
                                        )
                                    )
                                )
                            ),
                            ::core::result::Result::Ok(::core::result::Result::Ok(false)) =>
                            return ::core::result::Result::Err(::tinycbor::container::Error::Content(::tinycbor::container::bounded::Error::Surplus)),
                            _ => {}
                        }
                    }

                    Ok(Self {
                        #(#constructors)*
                    })
                }
            }
            Data::Enum { variants, naked } => {
                let arms = variants.into_iter().map(|v| v.decode(naked));

                let (tag, invalid_tag) = if naked {
                    (
                        quote! {
                            let tag: u64 = ::tinycbor::Decode::decode(d)
                                .map_err(|e| { ::tinycbor::tag::Error::Malformed(e) })?;
                        },
                        quote! {
                            ::tinycbor::tag::Error::InvalidTag
                        },
                    )
                } else {
                    (
                        quote! {
                            let tag = visitor
                                .visit::<u64>()
                                .ok_or(::tinycbor::container::Error::Content(::tinycbor::container::bounded::Error::Missing))?
                                .map_err(|e|
                                    ::tinycbor::container::Error::Content(
                                        ::tinycbor::container::bounded::Error::Content(
                                            ::tinycbor::tag::Error::Malformed(e)
                                        )
                                    )
                                )?;
                        },
                        quote! {
                            ::tinycbor::container::Error::Content(
                                ::tinycbor::container::bounded::Error::Content(::tinycbor::tag::Error::InvalidTag)
                            )
                        },
                    )
                };

                let procedure = quote! {
                    Ok({
                        #tag
                        match tag {
                            #(#arms)*
                            _ => {
                                return Err(#invalid_tag);
                            }
                        }
                    })
                };
                if naked {
                    return procedure;
                }

                quote! {
                    let mut visitor = d.array_visitor().map_err(|e| {
                        ::tinycbor::container::Error::Malformed(e)
                    })?;

                    let result = #procedure;

                    if visitor.remaining() != Some(0) {
                        Err(::tinycbor::container::Error::Content(::tinycbor::container::bounded::Error::Surplus))?;
                    }
                    result
                }
            }
        }
    }

    pub fn encode(self) -> TokenStream {
        match self {
            Data::Array { fields, naked } => {
                let field_count = fields.len();
                let destruct: TokenStream = fields.iter().map(|f| f.destruct()).collect();
                let procedures = fields.into_iter().map(|f| f.encode());
                let container = (!naked).then(|| {
                    quote! {
                        e.array(#field_count)?;
                    }
                });
                quote! {
                    #container
                    let Self { #destruct } = self;

                    #(#procedures)*
                    return Ok(());
                }
            }
            Data::Map(map_fields) => {
                let field_count_min = map_fields.iter().filter(|f| !f.optional).count();
                let field_count_opt = map_fields.iter().filter_map(|f| {
                    let variable = f.field.variable();
                    if f.optional {
                        Some(quote! {
                            if !__is_default(#variable) {
                                count += 1;
                            }
                        })
                    } else {
                        None
                    }
                });
                let field_count = quote! {
                    {
                        let mut count = #field_count_min;
                        #(#field_count_opt)*
                        count
                    }
                };

                let destruct: TokenStream = map_fields.iter().map(|f| f.field.destruct()).collect();
                let procedures = map_fields.into_iter().map(|f| {
                    let index = f.index;
                    let variable = f.field.variable();
                    let value = f.field.encode();
                    let mut tokens = quote! {
                        <u64 as ::tinycbor::Encode>::encode(&#index, e)?;
                        #value
                    };
                    if f.optional {
                        tokens = quote! {
                            if !__is_default(#variable) {
                                #tokens
                            }
                        };
                    }
                    tokens
                });
                quote! {
                    let Self { #destruct } = self;
                    e.map(#field_count)?;
                    #(#procedures)*
                    return Ok(());
                }
            }
            Data::Enum { variants, naked } => {
                let arms = variants.into_iter().map(|v| v.encode(naked));
                quote! {
                    match self {
                        #(#arms)*
                        _ => ::core::unreachable!(),
                    }
                }
            }
        }
    }

    pub fn len(self) -> TokenStream {
        match self {
            Data::Array { fields, naked } => {
                let field_count = fields.len();
                let destructure: TokenStream = fields.iter().map(|f| f.destruct()).collect();
                let procedures = fields.into_iter().map(|f| f.len());
                let container = (!naked).then(|| {
                    quote! {
                        <usize as ::tinycbor::CborLen>::cbor_len(&#field_count) +
                    }
                });
                quote! {
                    let Self { #destructure } = self;

                    #container
                    #(#procedures)+*
                }
            }
            Data::Map(map_fields) => {
                let field_count_min = map_fields.iter().filter(|f| !f.optional).count();
                let destruct: TokenStream = map_fields.iter().map(|f| f.field.destruct()).collect();
                let procedures = map_fields.into_iter().map(|f| {
                    let index = f.index;
                    let variable = f.field.variable();
                    let value = f.field.len();
                    let mut tokens = quote! {
                        <u64 as ::tinycbor::CborLen>::cbor_len(&#index) + #value
                    };
                    if f.optional {
                        tokens = quote! {
                            if !__is_default(#variable) {
                                count += 1;
                                #tokens
                            } else {
                                0
                            }
                        };
                    }
                    tokens
                });
                quote! {
                    {
                        let Self { #destruct } = self;
                        let mut count = #field_count_min;

                        #((#procedures) + )*
                        <usize as ::tinycbor::CborLen>::cbor_len(&count)
                    }
                }
            }
            Data::Enum { variants, naked } => {
                let arms = variants.into_iter().map(|v| v.len(naked));
                quote! {
                    match self {
                        #(#arms)*
                        _ => ::core::unreachable!(),
                    }
                }
            }
        }
    }

    fn error_generic_count(&self) -> usize {
        match self {
            Data::Array { fields, .. } => fields.iter().filter(|f| f.generic).count(),
            Data::Map(fields) => fields.iter().filter(|f| f.field.generic).count(),
            Data::Enum { variants, .. } => variants
                .iter()
                .flat_map(|v| v.fields.iter())
                .filter(|f| f.generic)
                .count(),
        }
    }

    fn error_generics(&self) -> Vec<Ident> {
        (0..self.error_generic_count())
            .map(|i| syn::Ident::new(&format!("E{}", i), Span::call_site()))
            .collect()
    }
}

#[derive(Clone, Default)]
pub struct Bounds {
    pub bound: Vec<syn::WherePredicate>,
    pub decode_bound: Vec<syn::WherePredicate>,
    pub encode_bound: Vec<syn::WherePredicate>,
    pub len_bound: Vec<syn::WherePredicate>,
}

impl Bounds {
    pub fn update(&mut self, meta: &syn::meta::ParseNestedMeta) -> syn::Result<bool> {
        let mut decode = false;
        let buf = if meta.path.is_ident("bound") {
            &mut self.bound
        } else if meta.path.is_ident("decode_bound") {
            decode = true;
            &mut self.decode_bound
        } else if meta.path.is_ident("encode_bound") {
            &mut self.encode_bound
        } else if meta.path.is_ident("len_bound") {
            &mut self.len_bound
        } else {
            return Ok(false);
        };
        let val: syn::LitStr = meta.value()?.parse()?;
        let mut predicate: syn::WherePredicate = val.parse()?;
        if decode {
            LifetimeReplacer.visit_where_predicate_mut(&mut predicate);
        }
        buf.push(predicate);

        Ok(true)
    }
}

struct LifetimeReplacer;
impl VisitMut for LifetimeReplacer {
    fn visit_lifetime_mut(&mut self, lt: &mut syn::Lifetime) {
        if lt.ident == "_" {
            lt.ident = syn::Ident::new("__bytes", lt.span());
        }
    }
}

fn tag_update(tag: &mut Option<u64>, meta: &syn::meta::ParseNestedMeta) -> syn::Result<bool> {
    if meta.path.is_ident("tag") {
        if tag.is_some() {
            return Err(meta.error("Duplicate `tag` attribute"));
        }
        let val;
        syn::parenthesized!(val in meta.input);
        *tag = Some(val.parse::<syn::LitInt>()?.base10_parse::<u64>()?);
        return Ok(true);
    }
    Ok(false)
}

fn attr_index(index: &mut Option<u64>, attribute: &syn::Attribute) -> syn::Result<bool> {
    if !attribute.path().is_ident("n") {
        return Ok(false);
    }

    if index.is_some() {
        return Err(syn::Error::new_spanned(
            attribute,
            "duplicate `n` attribute",
        ));
    }
    let val = attribute.parse_args::<syn::LitInt>()?;
    *index = Some(val.base10_parse::<u64>()?);

    Ok(true)
}

fn meta_index(index: &mut Option<u64>, meta: &syn::meta::ParseNestedMeta) -> syn::Result<bool> {
    if !meta.path.is_ident("n") {
        return Ok(false);
    }

    if index.is_some() {
        return Err(meta.error("Duplicate index attribute"));
    }
    let val;
    syn::parenthesized!(val in meta.input);
    *index = Some(val.parse::<syn::LitInt>()?.base10_parse::<u64>()?);

    Ok(true)
}

fn is_default() -> TokenStream {
    quote! {
        fn __is_default<T: ::core::default::Default + ::core::cmp::PartialEq>(value: &T) -> bool {
            value == &T::default()
        }
    }
}
