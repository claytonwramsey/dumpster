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
