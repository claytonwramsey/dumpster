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

use proc_macro2::TokenStream;
use quote::{quote, quote_spanned};
use syn::{
    parse_macro_input, parse_quote, spanned::Spanned, Data, DeriveInput, Fields, GenericParam,
    Generics, Ident, Index,
};

#[proc_macro_derive(Collectable)]
/// The macro for implementing [`dumpster::Collectable`] on an arbitrary type.
/// This implementation assumes that all fields of the structure or enum deriving Collectable have
/// also implemented Collectable.
pub fn derive_collectable(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let input = parse_macro_input!(input as DeriveInput);

    // name of the type being implemented
    let name = &input.ident;

    // generic parameters of the type being implemented
    let generics = add_trait_bounds(input.generics);
    let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

    let generate_graph = delegate_graph_fields(name, &input.data);

    let generated = quote! {
        unsafe impl #impl_generics dumpster::Collectable for #name #ty_generics #where_clause {
            fn add_to_ref_graph<const IS_ALLOCATION: bool>(
                &self,
                self_ref: dumpster::AllocationId,
                ref_graph: &mut dumpster::RefGraph,
            ) {
                if IS_ALLOCATION && ref_graph.mark_visited(self_ref) {
                    return;
                }
                #generate_graph
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

/// Generate an expression to delegate garbage collection to the fields of some data type.
fn delegate_graph_fields(name: &Ident, data: &Data) -> TokenStream {
    match data {
        Data::Struct(data) => match data.fields {
            Fields::Named(ref f) => {
                let recurse = f.named.iter().map(|f| {
                    let name = &f.ident;
                    quote_spanned! {f.span() =>
                        dumpster::Collectable::add_to_ref_graph::<false>(
                            &self.#name,
                            self_ref,
                            ref_graph
                        );
                    }
                });
                quote! {
                    #(#recurse)*
                }
            }
            Fields::Unnamed(ref f) => {
                let recurse = f.unnamed.iter().enumerate().map(|(i, f)| {
                    let index = Index::from(i);
                    quote_spanned! {f.span() =>
                        dumpster::Collectable::add_to_ref_graph::<false>(
                            &self.#index,
                            self_ref,
                            ref_graph
                        );
                    }
                });
                quote! {
                    #(#recurse)*
                }
            }
            Fields::Unit => quote! {},
        },
        Data::Enum(e) => {
            let cases = e.variants.iter().map(|var| {
                let var_name = &var.ident;

                match &var.fields {
                    Fields::Named(n) => {
                        let mut binding = TokenStream::new();
                        let mut execution = TokenStream::new();
                        for (i, name) in n.named.iter().enumerate() {
                            let field_name = format!("field{i}");
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

                            execution.extend(quote! {
                                dumpster::Collectable::add_to_ref_graph::<false>(
                                    #field_name,
                                    self_ref,
                                    ref_graph
                                );
                            })
                        }

                        todo!()
                    }
                    Fields::Unnamed(u) => {
                        let mut binding = TokenStream::new();
                        let mut execution = TokenStream::new();
                        for (i, _) in u.unnamed.iter().enumerate() {
                            let field_name = format!("field{i}");
                            if i == 0 {
                                binding.extend(quote! {
                                    #field_name
                                });
                            } else {
                                binding.extend(quote! {
                                    , #field_name
                                });
                            }

                            execution.extend(quote! {
                                dumpster::Collectable::add_to_ref_graph::<false>(
                                    #field_name,
                                    self_ref,
                                    ref_graph
                                );
                            })
                        }

                        quote_spanned! {var.span() => #name::#var_name(#binding) => {#execution},}
                    }
                    Fields::Unit => quote_spanned! {
                        var.span() => #name::#var_name => (),
                    },
                }
            });

            quote! {
                match self {
                    #(#cases)*
                }
            }
        }
        Data::Union(u) => {
            quote_spanned! {
                u.union_token.span => compile_error!("`Collectable` must be manually implemented for unions");
            }
        }
    }
}
