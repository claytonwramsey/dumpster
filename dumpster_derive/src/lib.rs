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

use proc_macro2::TokenStream;
use quote::quote;
use syn::{parse_quote, Path, Result};

synstructure::decl_derive!(
    [Trace, attributes(dumpster)] =>
    /// Derive `Trace` for a type.
    derive_trace
);

fn derive_trace(mut s: synstructure::Structure) -> Result<TokenStream> {
    let mut dumpster: Path = parse_quote!(::dumpster);

    // look for `crate` argument
    for attr in &s.ast().attrs {
        if !attr.path().is_ident("dumpster") {
            continue;
        }

        attr.parse_nested_meta(|meta| {
            if meta.path.is_ident("crate") {
                dumpster = meta.value()?.parse()?;
                Ok(())
            } else {
                Err(meta.error("unsupported attribute"))
            }
        })?;
    }

    // Every field must implement `Trace` (but the generics don't).
    s.add_bounds(synstructure::AddBounds::Fields);

    let contains_gcs_body = {
        let match_arms = s.each(|bi| {
            quote! {
                if #dumpster::ContainsGcs::contains_gcs(#bi, visitor) {
                    return true;
                }
            }
        });

        quote!(match *self { #match_arms })
    };

    let trace_with_body = {
        let match_arms = s.each(|bi| {
            quote! {
                #dumpster::TraceWith::accept(#bi, visitor)?;
            }
        });

        quote!(match *self { #match_arms })
    };

    Ok(s.gen_impl(quote! {
        gen impl #dumpster::ContainsGcs for @Self {
            #[inline]
            fn contains_gcs(&self, visitor: &mut #dumpster::ContainsGcsVisitor) -> bool {
                if visitor.consume_fuel().is_err() {
                    return true;
                }

                #contains_gcs_body

                false
            }
        }

        gen unsafe impl<__V: #dumpster::Visitor> #dumpster::TraceWith<__V> for @Self {
            #[inline]
            fn accept(&self, visitor: &mut __V) -> ::core::result::Result<(), ()> {
                #trace_with_body
                ::core::result::Result::Ok(())
            }
        }
    }))
}
