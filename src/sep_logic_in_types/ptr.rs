use super::*;
use higher_kinded_types::ForLt as PackLt;
use std::{
    fmt::Debug,
    marker::PhantomData,
    mem::MaybeUninit,
    ops::{Deref, DerefMut},
    ptr::NonNull,
};

// Copied from `ghost_cell`.
pub type InvariantLifetime<'brand> = PhantomData<fn(&'brand ()) -> &'brand ()>;

/// A pointer to a `T` with permission `Perm` (either `PointsTo` or `Weak`).
/// Note: dropping this value may leak the target. To deallocate, call `into_inner`.
pub struct Ptr<Perm, T> {
    ptr: NonNull<T>,
    pred: PhantomData<Perm>,
}

impl<Perm, T> Ptr<Perm, T> {
    pub unsafe fn from_non_null(ptr: NonNull<T>) -> Self {
        Self {
            ptr,
            pred: PhantomData,
        }
    }
    pub fn as_non_null(&self) -> NonNull<T> {
        self.ptr
    }

    pub unsafe fn cast_perm<NewPerm>(self) -> Ptr<NewPerm, T> {
        Ptr {
            ptr: self.ptr,
            pred: PhantomData,
        }
    }

    pub unsafe fn cast_ty<U>(self) -> Ptr<Perm, U> {
        Ptr {
            ptr: self.ptr.cast(),
            pred: PhantomData,
        }
    }

    pub unsafe fn copy(&self) -> Self {
        Ptr {
            ptr: self.ptr,
            pred: PhantomData,
        }
    }

    pub fn weak_ref<'this>(&self) -> Ptr<Weak<'this>, T::Target>
    where
        Perm: HasWeak<'this>,
        T: EraseNestedPerms,
    {
        unsafe { self.copy().cast_perm() }.erase_target_perms()
    }

    pub fn noperm(&self) -> Ptr<(), T> {
        unsafe { self.copy().cast_perm() }
    }

    pub fn erase_target_perms(self) -> Ptr<Perm, T::Target>
    where
        T: EraseNestedPerms,
    {
        T::erase_nested_perms(self)
    }

    /// Give a name to the hidden lifetime in a pointer permissions.
    pub fn unpack_lt<R>(self, f: impl for<'this> FnOnce(Ptr<Perm::Of<'this>, T>) -> R) -> R
    where
        Perm: PackLt,
    {
        f(unsafe { self.cast_perm() })
    }
    /// Give a name to the hidden lifetime in a pointer permissions.
    pub fn with_lt_ref<'a, R>(
        &'a self,
        f: impl for<'this> FnOnce(Ptr<Read<'this, 'a>, T>) -> R,
    ) -> R
    where
        Perm: PackLt,
        for<'this> Perm::Of<'this>: HasRead<'this>,
    {
        f(unsafe { self.copy().cast_perm() })
    }
    /// Give a name to the hidden lifetime in a pointer permissions.
    pub fn with_lt_mut<'a, R>(
        &'a mut self,
        f: impl for<'this> FnOnce(Ptr<Mut<'this, 'a>, T>) -> R,
    ) -> R
    where
        Perm: PackLt,
        for<'this> Perm::Of<'this>: HasMut<'this>,
    {
        f(unsafe { self.copy().cast_perm() })
    }
}

/// Hide the lifetime in a pointer permissions.
pub fn pack_lt<'this, Perm: PackLt, T>(ptr: Ptr<Perm::Of<'this>, T>) -> Ptr<Perm, T> {
    unsafe { ptr.cast_perm() }
}

impl<Perm, T> Debug for Ptr<Perm, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", std::any::type_name::<Self>())
    }
}

/// Safety: `Self` and `Target` are the same modulo predicates in `Ptr`, and the predicates in
/// `Self` imply the corresponding predicates in `Target`.
pub unsafe trait EraseNestedPerms: Sized {
    type Target;
    fn erase_nested_perms<Perm>(ptr: Ptr<Perm, Self>) -> Ptr<Perm, Self::Target> {
        // Safety: ok by the precondition.
        unsafe { ptr.cast_ty() }
    }
}

/// A predicate on a value's fields. This allows packing a predicate on a value into a predicate on
/// the pointer to such a value. This makes it possible to build inductive predicates, with
/// `pack`/`unpack` acting as constructor/destructor.
pub trait PredOnFields<'this, Ty>: Sized {
    type Unpacked: EraseNestedPerms<Target = Ty>;
    /// Given a pointer with `Self` permission, turn it into a pointer to the type with permissions
    /// applied.
    fn unpack(ptr: Ptr<PointsTo<'this, Self>, Ty>) -> Ptr<PointsTo<'this>, Self::Unpacked> {
        // Safety: by the `EraseNestedPerms` precondition this only changes predicates (i.e. ghost
        // types) so the two types are layout-compatible. Since the definition of `Self` as a
        // predicate is the effect of this function, this is definitionally a correct cast wrt
        // permissions.
        unsafe { ptr.cast_perm().cast_ty() }
    }
    /// Reverse `unpack`.
    fn pack(ptr: Ptr<PointsTo<'this>, Self::Unpacked>) -> Ptr<PointsTo<'this, Self>, Ty> {
        // Safety: by the `EraseNestedPerms` precondition this only changes predicates (i.e. ghost
        // types) so the two types are layout-compatible. Since the definition of `Self` as a
        // predicate is the effect of this function, this is definitionally a correct cast wrt
        // permissions.
        unsafe { ptr.cast_perm().cast_ty() }
    }
}
