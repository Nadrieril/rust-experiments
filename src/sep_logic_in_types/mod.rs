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

mod fields;
pub mod list;
mod permissions;
mod predicates;
mod ptr;
mod vptr;
mod wand;
pub use higher_kinded_types::ForLt as PackLt;

use fields::*;
use permissions::*;
use predicates::*;
use ptr::*;
use std::marker::PhantomData;
use vptr::*;
use wand::*;

/// Represents `exists<'this> T::Of<'this>`.
#[repr(transparent)]
pub struct ExistsLt<T: PackLt> {
    /// The lifetime is a lie.
    inner: T::Of<'static>,
}

#[macro_export]
macro_rules! ExistsLt {
    (<$first_lt:lifetime, $($lts:lifetime)*> = $($tt:tt)*) => {
        ExistsLt!(<$first_lt> = ExistsLt!(<$($lts)*> = $($tt)*))
    };
    ($($tt:tt)*) => {
        ExistsLt<higher_kinded_types::ForLt!($($tt)*)>
    };
}

// TODO: implement generic pack/unpack with ForLt.
// oops: this isn't actually safe because it's not actually parametric because of associated types
// :'(
// I really want safe transmute
impl<T: PackLt> ExistsLt<T> {
    pub fn pack_lt(val: T::Of<'_>) -> Self {
        Self {
            inner: unsafe { std::mem::transmute(val) },
        }
    }
    pub fn pack_lt_ref<'a>(val: &'a T::Of<'_>) -> &'a Self {
        unsafe { std::mem::transmute(val) }
    }
    pub fn pack_lt_mut<'a>(val: &'a mut T::Of<'_>) -> &'a mut Self {
        unsafe { std::mem::transmute(val) }
    }

    pub fn unpack_lt<R>(self, f: impl for<'this> FnOnce(T::Of<'this>) -> R) -> R {
        f(unsafe { std::mem::transmute(self.inner) })
    }
    pub fn unpack_lt_ref<'a, R>(&'a self, f: impl for<'this> FnOnce(&'a T::Of<'this>) -> R) -> R {
        f(unsafe { std::mem::transmute(&self.inner) })
    }
    pub fn unpack_lt_mut<'a, R>(
        &'a mut self,
        f: impl for<'this> FnOnce(&'a mut T::Of<'this>) -> R,
    ) -> R {
        f(unsafe { std::mem::transmute(&mut self.inner) })
    }

    pub fn unpack_opt_lt<R>(
        opt_self: Option<Self>,
        f: impl for<'this> FnOnce(Option<T::Of<'this>>) -> R,
    ) -> R
    where
        T: PackLt,
    {
        match opt_self {
            None => f(None),
            Some(x) => x.unpack_lt(|x| f(Some(x))),
        }
    }
}

/// Witness that `'a` and `'b` are interchangeable, for an notion of "interchangeable" appropriate
/// to what the brands are used for.
#[derive(Debug, Clone, Copy)]
pub struct EqPredicate<'a, 'b>(InvariantLifetime<'a>, InvariantLifetime<'b>);

impl<'a> EqPredicate<'a, 'a> {
    pub fn refl() -> Self {
        Self(PhantomData, PhantomData)
    }
}
impl<'a, 'b> EqPredicate<'a, 'b> {
    /// Safety: the brands must be the same, for an appropriate notion of "same".
    pub unsafe fn make() -> Self {
        Self(PhantomData, PhantomData)
    }
    pub fn apply<T: PackLt>(self, x: T::Of<'a>) -> T::Of<'b> {
        // Safety: this can only be constructed when `'a == 'b`, and the lifetimes are invariant.
        // Hence the types are actually equal.
        unsafe { std::mem::transmute(x) }
    }
    pub fn flip(self) -> EqPredicate<'b, 'a> {
        EqPredicate(PhantomData, PhantomData)
    }
}
