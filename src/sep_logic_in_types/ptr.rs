use super::*;
use higher_kinded_types::ForLt as PackLt;
use std::{fmt::Debug, marker::PhantomData, ops::Receiver, ptr::NonNull};

// Copied from `ghost_cell`.
pub type InvariantLifetime<'brand> = PhantomData<fn(&'brand ()) -> &'brand ()>;

/// A pointer to a `T` with permission `Perm` (one of `Own`, `Mut`, etc).
/// Note: dropping this value may leak the target. To deallocate, call `into_inner`.
/// `Perm` will generally be either `PointsTo<...>` or `PackLt!(PointsTo<...>)`.
pub struct Ptr<Perm, T> {
    ptr: NonNull<T>,
    /// We're invariant in `T` to avoid surprises. We can only soundly be covariant in `T` for some
    /// values of `Perm`, which seems hard to express, if at all possible.
    phantom: PhantomData<(Perm, *mut T)>,
}

impl<Perm, T> Ptr<Perm, T> {
    pub unsafe fn from_non_null(ptr: NonNull<T>) -> Self {
        Self {
            ptr,
            phantom: PhantomData,
        }
    }
    pub fn as_non_null(&self) -> NonNull<T> {
        self.ptr
    }

    pub unsafe fn cast_perm<NewPerm>(self) -> Ptr<NewPerm, T> {
        Ptr {
            ptr: self.ptr,
            phantom: PhantomData,
        }
    }
    pub unsafe fn cast_ty<U>(self) -> Ptr<Perm, U> {
        Ptr {
            ptr: self.ptr.cast(),
            phantom: PhantomData,
        }
    }
    pub unsafe fn cast_access<'this, NewPerm>(self) -> Ptr<NewPerm, T>
    where
        Perm: IsPointsTo + HasWeak<'this>,
        NewPerm: IsPointsTo<Pred = Perm::Pred> + HasWeak<'this>,
    {
        unsafe { self.cast_perm() }
    }
    pub unsafe fn cast_pred<'this, NewPerm>(self) -> Ptr<NewPerm, T>
    where
        Perm: IsPointsTo + HasWeak<'this>,
        NewPerm: IsPointsTo<Access = Perm::Access> + HasWeak<'this>,
    {
        unsafe { self.cast_perm() }
    }

    pub unsafe fn unsafe_copy(&self) -> Self {
        Ptr {
            ptr: self.ptr,
            phantom: PhantomData,
        }
    }

    #[expect(unused)]
    pub fn copy_read<'this>(&self) -> Ptr<Read<'this, '_, Perm::Pred>, T>
    where
        Perm: HasRead<'this>,
    {
        unsafe { self.unsafe_copy().cast_access() }
    }

    #[expect(unused)]
    pub fn copy_mut<'this>(&mut self) -> Ptr<Mut<'this, '_, Perm::Pred>, T>
    where
        Perm: HasMut<'this>,
    {
        unsafe { self.unsafe_copy().cast_access() }
    }

    pub fn weak_ref_no_erase<'this>(&self) -> Ptr<Weak<'this, Perm::Pred>, T>
    where
        Perm: HasWeak<'this>,
    {
        unsafe { self.unsafe_copy().cast_access() }
    }

    pub fn weak_ref<'this>(&self) -> Ptr<Weak<'this, Perm::Pred>, T::Erased>
    where
        Perm: HasWeak<'this>,
        T: EraseNestedPerms,
    {
        self.weak_ref_no_erase().erase_target_perms()
    }

    pub fn erase_target_perms(self) -> Ptr<Perm, T::Erased>
    where
        T: EraseNestedPerms,
    {
        T::erase_nested_perms(self)
    }

    #[expect(unused)]
    pub fn erase_pred<'this>(self) -> Ptr<PointsTo<'this, Perm::Access>, T>
    where
        Perm: HasWeak<'this>,
    {
        unsafe { self.cast_pred() }
    }

    /// Give a name to the hidden lifetime in a pointer permissions.
    pub fn unpack_lt<R>(self, f: impl for<'this> FnOnce(Ptr<Perm::Of<'this>, T>) -> R) -> R
    where
        Perm: PackLt,
    {
        f(unsafe { self.cast_perm() })
    }
    /// Give a name to the hidden lifetime in a pointer permissions.
    pub fn unpack_lt_ref<'a, R>(
        &'a self,
        f: impl for<'this> FnOnce(Ptr<Read<'this, 'a, <Perm::Of<'this> as IsPointsTo>::Pred>, T>) -> R,
    ) -> R
    where
        Perm: PackLt,
        for<'this> Perm::Of<'this>: HasRead<'this>,
    {
        f(unsafe { self.unsafe_copy().cast_perm() })
    }
    /// Give a name to the hidden lifetime in a pointer permissions.
    pub fn unpack_lt_mut<'a, R>(
        &'a mut self,
        f: impl for<'this> FnOnce(Ptr<Mut<'this, 'a, <Perm::Of<'this> as IsPointsTo>::Pred>, T>) -> R,
    ) -> R
    where
        Perm: PackLt,
        for<'this> Perm::Of<'this>: HasMut<'this>,
    {
        f(unsafe { self.unsafe_copy().cast_perm() })
    }
}

impl<'this, P, T> Ptr<P, T> {
    /// Compare two pointers for equality. Because of the `HasAllocated` constraint, the target can
    /// never have been deallocated, so address equality implies that the pointers are
    /// interchangeable. The returned equality predicate is a witness of this interchangeability.
    /// This would not be the case with `HasWeak`, as two pointers can have the same address but
    /// different provenance.
    #[expect(unused)]
    pub fn eq<'other, Q, U>(&self, other: &Ptr<Q, U>) -> Option<EqPredicate<'this, 'other>>
    where
        P: HasAllocated<'this>,
        Q: HasAllocated<'other>,
    {
        if self.ptr.addr() == other.ptr.addr() {
            Some(unsafe { EqPredicate::make() })
        } else {
            None
        }
    }
}

/// Hide the lifetime in a pointer permissions.
pub fn pack_lt<'this, Perm: PackLt, T>(ptr: Ptr<Perm::Of<'this>, T>) -> Ptr<Perm, T> {
    unsafe { ptr.cast_perm() }
}

impl<Perm, T> Receiver for Ptr<Perm, T> {
    type Target = T;
}

impl<Perm, T> Debug for Ptr<Perm, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", std::any::type_name::<Self>())
    }
}
