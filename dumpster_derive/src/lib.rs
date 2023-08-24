/*
   dumpster, a cycle-tracking garbage collector for Rust.
   Copyright (C) 2023 Clayton Ramsey.

   This program is free software: you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation, either version 3 of the License, or
   (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program.  If not, see <http://www.gnu.org/licenses/>.
*/

#![warn(clippy::pedantic)]
#![warn(clippy::cargo)]
#![allow(clippy::multiple_crate_versions)]

use proc_macro2::TokenStream;
use quote::{format_ident, quote, quote_spanned};
use syn::{
    parse_macro_input, parse_quote, spanned::Spanned, Data, DeriveInput, Fields, GenericParam,
    Generics, Ident, Index,
};

#[proc_macro_derive(Collectable)]
pub fn derive_collectable(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let input = parse_macro_input!(input as DeriveInput);

    // name of the type being implemented
    let name = &input.ident;

    // generic parameters of the type being implemented
    let generics = add_trait_bounds(input.generics);
    let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

    let do_visitor = delegate_methods(name, &input.data);

    let generated = quote! {
        unsafe impl #impl_generics dumpster::Collectable for #name #ty_generics #where_clause {
            #[inline]
            fn accept<V: dumpster::Visitor>(&self, visitor: &mut V) -> std::result::Result<(), ()> {
                #do_visitor
            }
        }
    };

    generated.into()
}

/// Collect the trait bounds for some generic expression.
fn add_trait_bounds(mut generics: Generics) -> Generics {
    for param in &mut generics.params {
        if let GenericParam::Type(ref mut type_param) = *param {
            type_param.bounds.push(parse_quote!(heapsize::HeapSize));
        }
    }
    generics
}

#[allow(clippy::too_many_lines)]
/// Generate method implementations for [`Collectable`] for some data type.
fn delegate_methods(name: &Ident, data: &Data) -> TokenStream {
    match data {
        Data::Struct(data) => match data.fields {
            Fields::Named(ref f) => {
                let delegate_visit = f.named.iter().map(|f| {
                    let name = &f.ident;
                    quote_spanned! {f.span() =>
                        dumpster::Collectable::accept(
                            &self.#name,
                            visitor
                        )?;
                    }
                });

                quote! { #(#delegate_visit)* std::result::Result::Ok(()) }
            }
            Fields::Unnamed(ref f) => {
                let delegate_visit = f.unnamed.iter().enumerate().map(|(i, f)| {
                    let index = Index::from(i);
                    quote_spanned! {f.span() =>
                        dumpster::Collectable::accept(
                            &self.#index,
                            visitor
                        )?;
                    }
                });

                quote! { #(#delegate_visit)* std::result::Result::Ok(()) }
            }
            Fields::Unit => quote! { std::result::Result::Ok(()) },
        },
        Data::Enum(e) => {
            let mut delegate_visit = TokenStream::new();
            for var in &e.variants {
                let var_name = &var.ident;

                match &var.fields {
                    Fields::Named(n) => {
                        let mut binding = TokenStream::new();
                        let mut execution_visit = TokenStream::new();
                        let mut execution_destroy = TokenStream::new();
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
                                dumpster::Collectable::accept(
                                    #field_name,
                                    visitor
                                )?;
                            });

                            execution_destroy.extend(quote! {
                                dumpster::Collectable::destroy_gcs(
                                    #field_name, destroyer
                                );
                            });
                        }

                        delegate_visit.extend(
                            quote! {#name::#var_name{#binding} => {#execution_visit std::result::Result::Ok(())},},
                        );
                    }
                    Fields::Unnamed(u) => {
                        let mut binding = TokenStream::new();
                        let mut execution_visit = TokenStream::new();
                        let mut execution_destroy = TokenStream::new();
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
                                dumpster::Collectable::accept(
                                    #field_name,
                                    visitor
                                )?;
                            });

                            execution_destroy.extend(quote! {
                                dumpster::Collectable::destroy_gcs(#field_name, destroyer);
                            });
                        }

                        delegate_visit.extend(
                            quote! {#name::#var_name(#binding) => {#execution_visit std::result::Result::Ok(())},},
                        );
                    }
                    Fields::Unit => {
                        delegate_visit
                            .extend(quote! {#name::#var_name => std::result::Result::Ok(()),});
                    }
                }
            }

            quote! {match self {#delegate_visit}}
        }
        Data::Union(u) => {
            quote_spanned! {
                u.union_token.span => compile_error!("`Collectable` must be manually implemented for unions");
            }
        }
    }
}
