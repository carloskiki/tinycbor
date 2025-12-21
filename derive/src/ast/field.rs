use heck::ToPascalCase as _;
use proc_macro2::TokenStream;
use quote::{ToTokens as _, format_ident, quote};
use syn::{spanned::Spanned as _, visit_mut::VisitMut};

struct With {
    decode_with: Option<syn::Type>,
    encode_with: Option<syn::Type>,
    len_with: Option<syn::Type>,
    with: Option<syn::Type>,
}

struct Attributes {
    index: Option<u64>,
    optional: bool,
    tag: Option<u64>,
    with: With,
}

impl TryFrom<&syn::Field> for Attributes {
    type Error = syn::Error;

    fn try_from(field: &syn::Field) -> Result<Self, Self::Error> {
        let syn::Field { attrs, .. } = field;
        let mut index = None;
        let mut optional = false;
        let mut tag = None;
        let mut with = None;
        let mut decode_with = None;
        let mut encode_with = None;
        let mut len_with = None;

        for attr in attrs {
            if super::attr_index(&mut index, attr)? || !attr.path().is_ident("cbor") {
                continue;
            }

            attr.parse_nested_meta(|meta| {
                let with_var = if meta.path.is_ident("with") {
                    &mut with
                } else if meta.path.is_ident("decode_with") {
                    &mut decode_with
                } else if meta.path.is_ident("encode_with") {
                    &mut encode_with
                } else if meta.path.is_ident("len_with") {
                    &mut len_with
                } else if super::tag_update(&mut tag, &meta)?
                    || super::meta_index(&mut index, &meta)?
                {
                    return Ok(());
                } else if meta.path.is_ident("optional") {
                    optional = true;
                    return Ok(());
                } else {
                    return Err(meta.error("unknown attribute"));
                };

                if with_var.is_some() {
                    return Err(meta.error("duplicate attribute"));
                }
                let val: syn::LitStr = meta.value()?.parse()?;
                *with_var = Some(val.parse()?);

                Ok(())
            })?;
        }

        Ok(Attributes {
            index,
            optional,
            tag,
            with: With {
                decode_with,
                encode_with,
                len_with,
                with,
            },
        })
    }
}

pub struct Field {
    pub tag: Option<u64>,
    pub member: syn::Member,
    with: With,
    pub ty: syn::Type,
    pub generic: bool,
}

impl Field {
    pub fn parse(
        field: &syn::Field,
        member: syn::Member,
        generics: &syn::Generics,
    ) -> syn::Result<Self> {
        let mut ty = field.ty.clone();
        let mut detector = GenericDetector {
            generics,
            is_generic: false,
        };
        detector.visit_type_mut(&mut ty);

        let Attributes {
            index,
            optional,
            tag,
            with,
        } = Attributes::try_from(field)?;

        if index.is_some() {
            return Err(syn::Error::new_spanned(
                &member,
                "`n` attribute is not allowed for array encodings",
            ));
        } else if optional {
            return Err(syn::Error::new_spanned(
                &member,
                "`optional` attribute is not allowed for array encodings",
            ));
        }

        Ok(Field {
            tag,
            with,
            member,
            ty,
            generic: detector.is_generic,
        })
    }

    pub fn error_name(&self) -> syn::Ident {
        match &self.member {
            syn::Member::Named(ident) => {
                syn::Ident::new(ident.to_string().to_pascal_case().as_str(), ident.span())
            }
            syn::Member::Unnamed(index) => format_ident!("Field{}", index.index),
        }
    }

    pub fn error_message(&self) -> String {
        format!("in field `{}`: {{0}}", self.member.to_token_stream())
    }

    pub fn decode_ty(&self) -> TokenStream {
        self.tagged(
            self.with
                .decode_with
                .as_ref()
                .or(self.with.with.as_ref())
                .map(|t| {
                    let mut ty = t.clone();
                    super::LifetimeReplacer.visit_type_mut(&mut ty);
                    ty.into_token_stream()
                })
                .unwrap_or(self.ty.to_token_stream()),
        )
    }

    pub fn encode_ty(&self) -> TokenStream {
        self.tagged(
            self.with
                .encode_with
                .as_ref()
                .or(self.with.with.as_ref())
                .unwrap_or(&self.ty)
                .to_token_stream(),
        )
    }

    pub fn len_ty(&self) -> TokenStream {
        self.tagged(
            self.with
                .len_with
                .as_ref()
                .or(self.with.with.as_ref())
                .unwrap_or(&self.ty)
                .to_token_stream(),
        )
    }

    fn tagged(&self, ty: TokenStream) -> TokenStream {
        if let Some(tag) = self.tag {
            quote! { ::tinycbor::tag::Tagged<#ty, #tag> }
        } else {
            ty.to_token_stream()
        }
    }

    // Returns the extension to be suffixed after the call to
    // decode: `<#type as Decode<'_>>::decode(d)#extension`
    pub fn decode(&self) -> TokenStream {
        let mut extension = TokenStream::new();
        if self.tag.is_some() {
            extension.extend(quote! { .0 });
        }
        if let Some(with) = self.with.decode_with.as_ref().or(self.with.with.as_ref()) {
            let spanned = with.span();
            extension.extend(quote::quote_spanned! {spanned=> .into() });
        }

        extension
    }

    pub fn variable(&self) -> syn::Ident {
        let member = &self.member;
        format_ident!("_{}", member)
    }

    pub fn destruct(&self) -> TokenStream {
        let member = &self.member;
        let variable = self.variable();
        quote! {
            #member: #variable,
        }
    }

    pub fn encode(self) -> TokenStream {
        let mut input = self.variable().into_token_stream();
        if self.with.with.is_some() || self.with.encode_with.is_some() {
            input = quote! { #input.as_ref() }
        }
        if let Some(tag) = &self.tag {
            input = quote! { <::tinycbor::tag::Tagged::<_, #tag>>::from_ref(#input) };
        }

        let ty = self.encode_ty();

        quote! {
            <#ty as ::tinycbor::Encode>::encode(&#input, e)?;
        }
    }

    pub fn len(self) -> TokenStream {
        let mut input = self.variable().into_token_stream();
        if self.with.with.is_some() || self.with.len_with.is_some() {
            input = quote! { #input.as_ref() }
        }
        if let Some(tag) = &self.tag {
            input = quote! { <::tinycbor::tag::Tagged::<_, #tag>>::from_ref(#input) };
        }

        let ty = self.len_ty();

        quote! {
            <#ty as ::tinycbor::CborLen>::cbor_len(&#input)
        }
    }
}

pub fn parse_fields(fields: &syn::Fields, generics: &syn::Generics) -> syn::Result<Vec<Field>> {
    fields
        .iter()
        .zip(fields.members())
        .map(|(field, member)| Field::parse(field, member, generics))
        .collect()
}

pub struct MapField {
    pub index: u64,
    pub optional: bool,
    pub field: Field,
}

impl MapField {
    pub fn parse(
        field: &syn::Field,
        member: syn::Member,
        generics: &syn::Generics,
    ) -> syn::Result<Self> {
        let Attributes {
            index,
            optional,
            tag,
            with,
        } = Attributes::try_from(field)?;

        let index = match index {
            Some(i) => i,
            None => {
                return Err(syn::Error::new_spanned(
                    &member,
                    "missing required `n` attribute for map encoding",
                ));
            }
        };

        let mut ty = field.ty.clone();
        let mut detector = GenericDetector {
            generics,
            is_generic: false,
        };
        detector.visit_type_mut(&mut ty);

        Ok(MapField {
            index,
            optional,
            field: Field {
                tag,
                with,
                member,
                ty,
                generic: detector.is_generic,
            },
        })
    }

    /// Returns (variable name, match arm, constructor field expression)
    pub fn decode(self, single: bool) -> (TokenStream, TokenStream, TokenStream) {
        let variable_ident = self.field.variable();
        let member = self.field.member.clone();
        let index = self.index;
        let error_name = self.field.error_name();
        let ty = self.field.decode_ty();
        let extension = self.field.decode();
        let ty_span = ty.span();
        let error_constructor = if single {
            quote! { __Error }
        } else {
            quote! { __Error::#error_name }
        };

        let raw_ty = self.field.ty;
        let variable = quote! {
            let mut #variable_ident: ::core::option::Option<#raw_ty> = ::core::option::Option::None;
        };

        let decode_result = quote! {
            ::core::option::Option::Some(<#ty as ::tinycbor::Decode<'__bytes>>::decode(d)
                .map_err(|e| #error_constructor(e))? #extension)
        };

        let match_arm = quote::quote_spanned! {ty_span=>
            #index if #variable_ident.is_none() => {
                #variable_ident = #decode_result;
            }
        };

        let unwrap = if self.optional {
            quote! { .unwrap_or_default() }
        } else {
            quote! { .ok_or(::tinycbor::collections::fixed::Error::Missing)? }
        };

        let constructor = quote! {
            #member: #variable_ident #unwrap,
        };

        (variable, match_arm, constructor)
    }
}

struct GenericDetector<'a> {
    generics: &'a syn::Generics,
    is_generic: bool,
}

impl<'a> VisitMut for GenericDetector<'a> {
    fn visit_path_mut(&mut self, i: &mut syn::Path) {
        // Check if the path is a simple identifier (like `T` or `N`)
        // and matches one of our generic params.
        if i.leading_colon.is_none()
            && i.segments.len() == 1
            && self.generics.params.iter().any(|param| {
                let param_ident = match param {
                    syn::GenericParam::Type(t) => &t.ident,
                    syn::GenericParam::Const(c) => &c.ident,
                    syn::GenericParam::Lifetime(_) => return false,
                };
                i.segments[0].ident == *param_ident
            })
        {
            self.is_generic = true;
        }

        syn::visit_mut::visit_path_mut(self, i);
    }
}
