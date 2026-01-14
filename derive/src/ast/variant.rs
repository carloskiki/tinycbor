use proc_macro2::TokenStream;
use quote::quote;

use crate::ast::{Field, parse_fields};

pub struct Variant {
    pub tag: u64,
    pub ident: syn::Ident,
    pub fields: Vec<Field>,
}

impl Variant {
    pub fn parse(input: &syn::Variant, generics: &syn::Generics) -> syn::Result<Self> {
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

        Ok(Variant {
            tag: index.ok_or_else(|| syn::Error::new_spanned(input, "missing index attribute"))?,
            ident: input.ident.clone(),
            fields: parse_fields(&input.fields, generics)?,
        })
    }

    pub fn decode(self, naked: bool) -> TokenStream {
        let Variant { tag, ident, fields } = self;
        let variant_name = &ident;

        let field_count = fields.len();
        let fields = fields.into_iter().map(|f| {
            let error_constructor = if field_count == 1 {
                quote! {
                ::tinycbor::tag::Error::Content(__Error::#variant_name(e)) }
            } else {
                let error_name = f.error_name();
                let ident = quote::format_ident!("{}{}", variant_name, error_name);
                quote! { ::tinycbor::tag::Error::Content(__Error::#ident(e)) }
            };

            f.decode(&error_constructor, naked)
        });

        quote! {
            #tag => {
                Self::#ident {
                    #(#fields),*
                }
            }
        }
    }

    pub fn encode(self, naked: bool) -> TokenStream {
        let Variant { tag, ident, fields } = self;
        let variant_name = &ident;
        let field_count = fields.len();

        let destruct: TokenStream = fields.iter().map(|f| f.destruct()).collect();
        let procedures = fields.into_iter().map(|f| f.encode());
        let container = (!naked).then(|| quote! { e.array(#field_count + 1)?; });

        quote! {
            Self::#variant_name { #destruct } => {
                #container
                <u64 as ::tinycbor::Encode>::encode(&#tag, e)?;
                #(#procedures)*
                Ok(())
            }
        }
    }

    pub fn len(self, naked: bool) -> TokenStream {
        let Variant { tag, ident, fields } = self;
        let variant_name = &ident;
        let field_count = fields.len();

        let destructors: TokenStream = fields.iter().map(|f| f.destruct()).collect();
        let field_lens = fields.into_iter().map(|f| f.len());
        let container_len = (!naked).then(|| {
            quote! {
                total_len += <usize as ::tinycbor::CborLen>::cbor_len(&(#field_count + 1));
            }
        });
        quote! {
            Self::#variant_name { #destructors } => {
                let mut total_len = <u64 as ::tinycbor::CborLen>::cbor_len(&#tag);
                #container_len
                #(total_len += #field_lens;)*
                total_len
            }
        }
    }
}
