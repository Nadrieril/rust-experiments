//! # Separation Logic In Rust Types
//!
//! This crate provides a safe API that can express complex pointer-based datastructures such as
//! doubly linked lists. It is based on the following ideas:
//! - A pointer type that carries fine-grained permission information at the type level;
//! - The use of GhostCell-like lifetime brands to indicate knowledge that two pointers are equal
//! (including provenance).
//!
//! The pointer type is `Ptr<Perm, T>`, where `Perm` is almost always `PointsTo<'this, Access, Ty>`.
//! - `'this` is the brand that we use to track pointer equality at the type level;
//! - `Access` specifies what access is allowed through this pointer. Typical values are `POwn`,
//! `PMut<'a>`, `PRead<'a>` and `()` (no access);
//! - `Ty` is an optional override of the pointed-to type.
//!
//! Because we track things at the type level, the API of this crate heavily features type-changing
//! pointer manipulation. This may create situations were several pointers pointing to the same
//! place disagree on the type of the pointee. This mostly happens to permissionless pointers and
//! is not an issue: the pointer(s) with at least read access to the pointee will always agree, and
//! have the correct pointee type. This is because full ownership is needed for nontrivial
//! type-changing operations.
//!
//! When we go beyond tree-shaped ownership, we start wanting ownership to evolve at runtime. For
//! example, when moving a cursor through a doubly-linked-list, one could say the cursor pointer
//! has ownership over the pointed-to list node, which then has ownership over the rest of the list
//! by following prev/next pointers. To represent this in types, we need type-changing operations:
//! a same node in memory may have different types at different moments to reflect that changing
//! ownership. We end up needing to change types between whole recursive datatypes; this is what
//! type overrides are for. See the doubly-linked list example for what this looks like.
//!
//! To manage ADTs that contain pointers see the `HasPermField` trait.
//!
//! Typical usage of this crate makes heavy use of the `ExistsLt` wrapper and macro, which express
//! the existential quantification of lifetimes.
//
// TODO: should only allow writes when there's no pointee predicate. in fact a pointee predicate is
// always unwrapped first before doing anything else. could express as an actual wrapper to make it
// harder to miss?
// Morally the pointer options are:
// - `NoPerm`: used as default in sth like `Node`;
// - `PointsTo<'this>`: used as anchor to move permissions to/from;
// - `PointsTo<'this, Access>`: used to read & write;
// - `PointsTo<'this, Access, Pred>`: moved around and packed-unpacked.
// If I use `'static` as the unknown pointer, could get rid of `NoPerm` and inline
// `PointsTo` inside `Ptr`. Ah but `'static` already means impossible.
// -> not sure enough of my API for that. need to try doubly-linked tree first.
// `Pred` is actually just an override of the pointee type :thinking:
//
// I think it's time to try the tree.
//
// TODO: we do variance wrong. maybe store the real type in the permission, and force the "layout"
// type to be `'static`.

mod adts;
mod brands;
pub mod list;
mod permissions;
mod predicates;
mod ptr;
pub mod tree;
mod vptr;
mod wand;

use adts::*;
use brands::*;
use permissions::*;
use predicates::*;
use ptr::*;
use vptr::*;
use wand::*;

pub use brands::PackLt;
