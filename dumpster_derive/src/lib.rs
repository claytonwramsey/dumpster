use proc_macro::TokenStream;
use syn::{parse_macro_input, DeriveInput};

#[proc_macro_derive(Collectable)]
/// The macro for implementing [`dumpster::Collectable`] on an arbitrary type.
/// This implementation assumes that all fields of the structure or enum deriving Collectable have
/// also implemented Collectable.
pub fn derive_collectable(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    todo!()
}
