//! Deobfuscates Cloudflare challenge scripts in repeated rewrite rounds.
//!
//! Rewrites make further rewrites possible: decoding names allows helper inlining, which
//! reveals control flow and more calls. Each round runs the [`pipeline`] steps in order. A step
//! is skipped if it already left the current program unchanged. Rounds stop when all steps have
//! processed the current program or a whole round makes no net change. The final hygiene pass
//! resolves naming conflicts. Each rewrite module describes its transformation.

/// Fast hashing for the rewrites' identifier and node maps; no rewrite depends on their order.
type HashMap<K, V> = rustc_hash::FxHashMap<K, V>;
type HashSet<T> = rustc_hash::FxHashSet<T>;
/// A map by binding that can be probed with a borrowed [`IdRef`]: cloning an [`Id`] touches its
/// name's reference count, and these maps are probed once per identifier in the program.
type IdMap<V> = hashbrown::HashMap<swc_core::ecma::ast::Id, V, rustc_hash::FxBuildHasher>;

/// An [`Id`](swc_core::ecma::ast::Id) borrowed from its identifier.
#[derive(Clone, Copy)]
struct IdRef<'a>(&'a swc_core::atoms::Atom, swc_core::common::SyntaxContext);

impl<'a> From<&'a swc_core::ecma::ast::Ident> for IdRef<'a> {
    fn from(identifier: &'a swc_core::ecma::ast::Ident) -> Self {
        Self(&identifier.sym, identifier.ctxt)
    }
}

/// Hashes as the tuple does, so the two find the same entries.
impl std::hash::Hash for IdRef<'_> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.0.hash(state);
        self.1.hash(state);
    }
}

impl hashbrown::Equivalent<swc_core::ecma::ast::Id> for IdRef<'_> {
    fn equivalent(&self, key: &swc_core::ecma::ast::Id) -> bool {
        self.1 == key.1 && *self.0 == key.0
    }
}

impl From<&IdRef<'_>> for swc_core::ecma::ast::Id {
    fn from(id: &IdRef<'_>) -> Self {
        (id.0.clone(), id.1)
    }
}

mod analysis;
mod argument_arrays;
mod arrow_blocks;
mod bitwise;
mod blocks;
mod call_helpers;
mod control_flow;
mod copy_propagation;
mod dead_branches;
mod dead_properties;
mod dispatch;
mod encoded_strings;
mod function_lengths;
mod helper_objects;
mod int32_helpers;
mod literals;
mod loops;
mod memoized_strings;
mod merged_functions;
mod pipeline;
mod register_arrays;
mod removal;
mod state_machines;
mod statements;
mod static_members;
#[cfg(test)]
mod testing;
mod unused_bindings;

pub(crate) use encoded_strings::{Encoded, encode as encode_string, inline_strings};
pub use pipeline::Decoding;
pub use pipeline::{Deobfuscated, Unconverged, deobfuscate};
pub(crate) use pipeline::{deobfuscate_with, read_decoded};

#[cfg(test)]
mod tests {
    use swc_core::atoms::Atom;
    use swc_core::common::SyntaxContext;

    use super::{IdMap, IdRef};

    #[test]
    fn borrowed_ids_find_the_entries_of_owned_ones() {
        let name = Atom::from("a_name_too_long_to_store_inline");
        let context = SyntaxContext::empty();
        let mut map = IdMap::default();
        map.insert((name.clone(), context), 1);
        assert_eq!(map.get(&IdRef(&name, context)), Some(&1));
        *map.entry_ref(&IdRef(&name, context)).or_default() += 1;
        assert_eq!(map.len(), 1, "the same binding, so no second entry");
        assert_eq!(map[&(name, context)], 2);
    }
}
