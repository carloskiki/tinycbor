use proc_macro2::TokenStream;
use quote::quote;
use syn::spanned::Spanned as _;

use crate::ast::{Field, parse_fields};

pub struct VariantTag {
    pub tag: u64,
    pub ident: syn::Ident,
}

impl TryFrom<&syn::Variant> for VariantTag {
    type Error = syn::Error;

    fn try_from(input: &syn::Variant) -> Result<Self, Self::Error> {
        let mut index = None;

        for attr in &input.attrs {
            if super::attr_index(&mut index, attr)? {
                continue;
            }
            if !attr.path().is_ident("cbor") {
                continue;
            }
            attr.parse_nested_meta(|meta| {
                if super::meta_index(&mut index, &meta)? {
                    return Ok(());
                }
                Err(meta.error("unknown attribute"))
            })?;
        }

        Ok(VariantTag {
            tag: index.ok_or_else(|| syn::Error::new_spanned(input, "missing index attribute"))?,
            ident: input.ident.clone(),
        })
    }
}

pub struct TagOnly(pub VariantTag);

impl TryFrom<&syn::Variant> for TagOnly {
    type Error = syn::Error;

    fn try_from(input: &syn::Variant) -> Result<Self, Self::Error> {
        if !input.fields.is_empty() {
            return Err(syn::Error::new_spanned(
                input,
                "index enum variants must be unit variants",
            ));
        }

        Ok(TagOnly(VariantTag::try_from(input)?))
    }
}

impl TagOnly {
    pub fn decode(self) -> TokenStream {
        let VariantTag { tag, ident } = self.0;
        quote::quote! {
            #tag => Self::#ident,
        }
    }

    pub fn encode(self) -> TokenStream {
        let VariantTag { tag, ident } = self.0;
        quote::quote! {
            Self::#ident => {
                <u64 as ::tinycbor::Encode>::encode(&#tag, e)
            }
        }
    }

    pub fn len(self) -> TokenStream {
        let VariantTag { tag, ident } = self.0;
        quote::quote! {
            Self::#ident => {
               <u64 as ::tinycbor::CborLen>::cbor_len(&#tag)
            }
        }
    }
}

pub struct Variant {
    pub index: TagOnly,
    pub fields: Vec<Field>,
}

impl Variant {
    pub fn parse(input: &syn::Variant, generics: &syn::Generics) -> syn::Result<Self> {
        let index = VariantTag::try_from(input)?;

        Ok(Variant {
            index: TagOnly(index),
            fields: parse_fields(&input.fields, generics)?,
        })
    }

    pub fn decode(self) -> TokenStream {
        let Variant {
            index: TagOnly(VariantTag { tag, ident }),
            fields,
        } = self;
        let variant_name = &ident;

        let field_count = fields.len();
        let fields = fields.into_iter().map(|f| {
            let member = f.member.clone();
            let ty = f.decode_ty();
            let extension = f.decode();
            let ty_span = ty.span();

            let error_constructor = if field_count == 1 {
                quote! { __Error::#variant_name }
            } else {
                let error_name = f.error_name();
                let ident = quote::format_ident!("{}{}", variant_name, error_name);
                quote! { __Error::#ident }
            };

            quote::quote_spanned! {ty_span=>
                #member: visitor.visit::<#ty>()
                .ok_or(::tinycbor::collections::Error::Element(::tinycbor::collections::fixed::Error::Missing))?
                .map_err(|e| ::tinycbor::collections::Error::Element(
                    ::tinycbor::collections::fixed::Error::Inner(
                        ::tinycbor::tag::Error::Inner(
                            #error_constructor(e)
                        )
                    )
                ))?#extension
            }
        });

        quote! {
            #tag => {
                Self::#ident {
                    #(#fields),*
                }
            }
        }
    }

    pub fn encode(self) -> TokenStream {
        let Variant {
            index: TagOnly(VariantTag { tag, ident }),
            fields,
        } = self;
        let variant_name = &ident;
        let field_count = fields.len();

        let destruct: TokenStream = fields.iter().map(|f| f.destruct()).collect();
        let procedures = fields.into_iter().map(|f| f.encode());

        quote! {
            Self::#variant_name { #destruct } => {
                e.array(#field_count + 1)?;
                <u64 as ::tinycbor::Encode>::encode(&#tag, e)?;
                #(#procedures)*
                Ok(())
            }
        }
    }

    pub fn len(self) -> TokenStream {
        let Variant {
            index: TagOnly(VariantTag { tag, ident }),
            fields,
        } = self;
        let variant_name = &ident;
        let field_count = fields.len();

        let destructors: TokenStream = fields.iter().map(|f| f.destruct()).collect();
        let field_lens = fields.into_iter().map(|f| f.len());
        quote! {
            Self::#variant_name { #destructors } => {
                let mut total_len = <usize as ::tinycbor::CborLen>::cbor_len(&(#field_count + 1))
                    + <u64 as ::tinycbor::CborLen>::cbor_len(&#tag);
                #(total_len += #field_lens;)*
                total_len
            }
        }
    }
}
