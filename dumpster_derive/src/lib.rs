/*
    dumpster, a cycle-tracking garbage collector for Rust.
    Copyright (C) 2023 Clayton Ramsey.

    This Source Code Form is subject to the terms of the Mozilla Public
    License, v. 2.0. If a copy of the MPL was not distributed with this
    file, You can obtain one at http://mozilla.org/MPL/2.0/.
*/

#![warn(clippy::pedantic)]
#![warn(clippy::cargo)]
#![allow(clippy::multiple_crate_versions)]

use proc_macro2::{TokenStream, TokenTree};
use quote::{format_ident, quote, quote_spanned, ToTokens as _};
use syn::{
    parse_macro_input, parse_quote, spanned::Spanned, Data, DeriveInput, Fields, GenericParam,
    Generics, Ident, Index, Path,
};

#[proc_macro_derive(Trace, attributes(dumpster))]
/// Derive `Trace` for a type.
pub fn derive_trace(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    let mut dumpster: Path = parse_quote!(::dumpster);

    // look for `crate` argument
    for attr in &input.attrs {
        if !attr.path().is_ident("dumpster") {
            continue;
        }

        let result = attr.parse_nested_meta(|meta| {
            if meta.path.is_ident("crate") {
                dumpster = meta.value()?.parse()?;
                Ok(())
            } else {
                Err(meta.error("unsupported attribute"))
            }
        });

        if let Err(err) = result {
            return err.into_compile_error().into();
        }
    }

    // name of the type being implemented
    let name = &input.ident;

    // generic parameters of the type being implemented
    let generics = add_trait_bounds(&dumpster, input.generics);
    let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

    let impl_generics = {
        let tokens = impl_generics.into_token_stream();
        let param = quote! { __V: #dumpster::Visitor };

        let params = if tokens.is_empty() {
            quote! { #param }
        } else {
            // remove the angle bracket delimiters
            let mut tokens: Vec<TokenTree> = tokens.into_iter().skip(1).collect();
            tokens.pop();

            let tokens: TokenStream = tokens.into_iter().collect();

            quote! { #param, #tokens }
        };

        quote! { < #params > }
    };

    let do_visitor = delegate_methods(&dumpster, name, &input.data);

    let generated = quote! {
        unsafe impl #impl_generics #dumpster::TraceWith<__V> for #name #ty_generics #where_clause {
            #[inline]
            fn accept(&self, visitor: &mut __V) -> ::core::result::Result<(), ()> {
                #do_visitor
            }
        }
    };

    generated.into()
}

/// Collect the trait bounds for some generic expression.
fn add_trait_bounds(dumpster: &Path, mut generics: Generics) -> Generics {
    for param in &mut generics.params {
        if let GenericParam::Type(ref mut type_param) = *param {
            type_param
                .bounds
                .push(parse_quote!(#dumpster::TraceWith<__V>));
        }
    }
    generics
}

#[allow(clippy::too_many_lines)]
/// Generate method implementations for [`Trace`] for some data type.
fn delegate_methods(dumpster: &Path, name: &Ident, data: &Data) -> TokenStream {
    match data {
        Data::Struct(data) => match data.fields {
            Fields::Named(ref f) => {
                let delegate_visit = f.named.iter().map(|f| {
                    let name = &f.ident;
                    quote_spanned! {f.span() =>
                        #dumpster::TraceWith::accept(
                            &self.#name,
                            visitor
                        )?;
                    }
                });

                quote! { #(#delegate_visit)* ::core::result::Result::Ok(()) }
            }
            Fields::Unnamed(ref f) => {
                let delegate_visit = f.unnamed.iter().enumerate().map(|(i, f)| {
                    let index = Index::from(i);
                    quote_spanned! {f.span() =>
                        #dumpster::TraceWith::accept(
                            &self.#index,
                            visitor
                        )?;
                    }
                });

                quote! { #(#delegate_visit)* ::core::result::Result::Ok(()) }
            }
            Fields::Unit => quote! { ::core::result::Result::Ok(()) },
        },
        Data::Enum(e) => {
            let mut delegate_visit = TokenStream::new();
            for var in &e.variants {
                let var_name = &var.ident;

                match &var.fields {
                    Fields::Named(n) => {
                        let mut binding = TokenStream::new();
                        let mut execution_visit = TokenStream::new();
                        for (i, name) in n.named.iter().enumerate() {
                            let field_name = format_ident!("field{i}");
                            let field_ident = name.ident.as_ref().unwrap();
                            if i == 0 {
                                binding.extend(quote! {
                                    #field_ident: #field_name
                                });
                            } else {
                                binding.extend(quote! {
                                    , #field_ident: #field_name
                                });
                            }

                            execution_visit.extend(quote! {
                                #dumpster::TraceWith::accept(
                                    #field_name,
                                    visitor
                                )?;
                            });
                        }

                        delegate_visit.extend(
                            quote! {#name::#var_name{#binding} => {#execution_visit ::core::result::Result::Ok(())},},
                        );
                    }
                    Fields::Unnamed(u) => {
                        let mut binding = TokenStream::new();
                        let mut execution_visit = TokenStream::new();
                        for (i, _) in u.unnamed.iter().enumerate() {
                            let field_name = format_ident!("field{i}");
                            if i == 0 {
                                binding.extend(quote! {
                                    #field_name
                                });
                            } else {
                                binding.extend(quote! {
                                    , #field_name
                                });
                            }

                            execution_visit.extend(quote! {
                                #dumpster::TraceWith::accept(
                                    #field_name,
                                    visitor
                                )?;
                            });
                        }

                        delegate_visit.extend(
                            quote! {#name::#var_name(#binding) => {#execution_visit ::core::result::Result::Ok(())},},
                        );
                    }
                    Fields::Unit => {
                        delegate_visit
                            .extend(quote! {#name::#var_name => ::core::result::Result::Ok(()),});
                    }
                }
            }

            quote! {match self {#delegate_visit}}
        }
        Data::Union(u) => {
            quote_spanned! {
                u.union_token.span => compile_error!("`Trace` must be manually implemented for unions");
            }
        }
    }
}
