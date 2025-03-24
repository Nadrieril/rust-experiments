//! # Separation Logic In Rust Types
//!
//! This crate provides a safe API that can express complex pointer-based datastructures such as
//! doubly linked lists. It is based on the following ideas:
//! - A pointer type that carries fine-grained permission information at the type level;
//! - The use of GhostCell-like lifetime brands to indicate knowledge that two pointers are equal
//! (including provenance).
//!
//! The pointer type is `Ptr<Perm, T>`, where `Perm` is almost always `PointsTo<'this, Access, Pred>`.
//! - `'this` is the brand that we use to track pointer equality at the type level;
//! - `Access` specifies what access is allowed through this pointer. Typical values are `POwn`,
//! `PMut<'a>`, `PRead<'a>` and `()` (no access);
//! - `Pred` is an optional predicate on the pointed-to value.
//!
//! Because we track things at the type level, the API of this crate heavily features type-changing
//! pointer manipulation. This may create situations were several pointers pointing to the same
//! place disagree on the type of the pointee. This mostly happens to permissionless pointers and
//! is not an issue: the pointer(s) with at least read access to the pointee will always agree, and
//! have the correct pointee type. This is because full ownership is needed for nontrivial
//! type-changing operations.
//!
//! Predicates are how we encode complex datastructures. A typical predicate is a ZST implementing
//! `PackedPredicate`. Such a predicate stands for knowledge about the pointers inside the pointee.
//! See the doubly-linked list example for what this looks like.
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

mod adts;
mod brands;
pub mod list;
mod permissions;
mod predicates;
mod ptr;
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
