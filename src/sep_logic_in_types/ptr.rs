use super::*;
use higher_kinded_types::ForLt as PackLt;
use std::{fmt::Debug, marker::PhantomData, ops::Receiver, ptr::NonNull};

// Copied from `ghost_cell`.
pub type InvariantLifetime<'brand> = PhantomData<fn(&'brand ()) -> &'brand ()>;

/// A pointer to a `T` with permission `Perm` (one of `Own`, `Mut`, etc).
/// Note: dropping this value may leak the target. To deallocate, call `into_inner`.
/// `Perm` will generally be either `PointsTo<...>` or `ExistsLt!(PointsTo<...>)`.
pub struct Ptr<Perm, T> {
    ptr: NonNull<T>,
    perm: PhantomData<Perm>,
    /// We're invariant in `T` to avoid surprises. We can only soundly be covariant in `T` for some
    /// values of `Perm`, which seems hard to express, if at all possible.
    phantom: PhantomData<*mut T>,
}

/// Permission token on a pointer.
/// Safety: must be transmutable with `PhantomData`.
pub unsafe trait PtrPerm: Sized {
    /// Unsafely create a new permission token.
    /// Safety: ensure the permission is correct.
    unsafe fn new() -> Self;
}

impl<Perm: PtrPerm, T> Ptr<Perm, T> {
    pub unsafe fn from_non_null(ptr: NonNull<T>) -> Self {
        Self {
            ptr,
            perm: PhantomData,
            phantom: PhantomData,
        }
    }
    pub fn as_non_null(&self) -> NonNull<T> {
        self.ptr
    }

    pub unsafe fn cast_perm<NewPerm>(self) -> Ptr<NewPerm, T> {
        Ptr {
            ptr: self.ptr,
            perm: PhantomData,
            phantom: PhantomData,
        }
    }
    pub unsafe fn cast_ty<U>(self) -> Ptr<Perm, U> {
        Ptr {
            ptr: self.ptr.cast(),
            perm: PhantomData,
            phantom: PhantomData,
        }
    }
    pub unsafe fn cast_access<'this, NewPerm>(self) -> Ptr<NewPerm, T>
    where
        Perm: IsPointsTo<'this>,
        NewPerm: IsPointsTo<'this, Pred = Perm::Pred>,
    {
        unsafe { self.cast_perm() }
    }
    pub unsafe fn cast_pred<'this, NewPerm>(self) -> Ptr<NewPerm, T>
    where
        Perm: IsPointsTo<'this>,
        NewPerm: IsPointsTo<'this, Access = Perm::Access>,
    {
        unsafe { self.cast_perm() }
    }

    pub unsafe fn unsafe_copy(&self) -> Self {
        Ptr {
            ptr: self.ptr,
            perm: PhantomData,
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

    /// Copy the pointer. The copied pointer has no permissions.
    pub fn copy<'this>(&self) -> Ptr<PointsTo<'this>, T>
    where
        Perm: IsPointsTo<'this>,
    {
        unsafe { self.unsafe_copy().cast_perm() }
    }

    pub fn weak_ref<'this>(&self) -> Ptr<PointsTo<'this>, T::Erased>
    where
        Perm: IsPointsTo<'this>,
        T: EraseNestedPerms,
    {
        self.copy().drop_target_perms()
    }

    pub fn drop_target_perms(self) -> Ptr<Perm, T::Erased>
    where
        T: EraseNestedPerms,
    {
        T::erase_nested_perms(self)
    }

    #[expect(unused)]
    pub fn erase_pred<'this>(self) -> Ptr<PointsTo<'this, Perm::Access>, T>
    where
        Perm: IsPointsTo<'this>,
    {
        unsafe { self.cast_pred() }
    }
}

impl<Perm, T> Ptr<ExistsLt<Perm>, T>
where
    Perm: PackLt,
    for<'a> Perm::Of<'a>: PtrPerm,
{
    /// Give a name to the hidden lifetime in a pointer permissions.
    pub fn unpack_lt<R>(self, f: impl for<'this> FnOnce(Ptr<Perm::Of<'this>, T>) -> R) -> R {
        f(unsafe { self.cast_perm() })
    }
    /// Give a name to the hidden lifetime in a pointer permissions.
    pub fn unpack_lt_ref<'a, R>(
        &'a self,
        f: impl for<'this> FnOnce(
            Ptr<Read<'this, 'a, <Perm::Of<'this> as IsPointsTo<'this>>::Pred>, T>,
        ) -> R,
    ) -> R
    where
        for<'this> Perm::Of<'this>: HasRead<'this>,
    {
        f(unsafe { self.unsafe_copy().cast_perm() })
    }
    /// Give a name to the hidden lifetime in a pointer permissions.
    pub fn unpack_lt_mut<'a, R>(
        &'a mut self,
        f: impl for<'this> FnOnce(
            Ptr<Mut<'this, 'a, <Perm::Of<'this> as IsPointsTo<'this>>::Pred>, T>,
        ) -> R,
    ) -> R
    where
        for<'this> Perm::Of<'this>: HasMut<'this>,
    {
        f(unsafe { self.unsafe_copy().cast_perm() })
    }
}

impl<Perm: PtrPerm, T> Ptr<Perm, ExistsLt<T>>
where
    T: PackLt,
{
    /// Give a name to the hidden lifetime in a pointer target.
    pub fn unpack_target_lt<R>(self, f: impl for<'this> FnOnce(Ptr<Perm, T::Of<'this>>) -> R) -> R {
        // Safety: `ExistsLt` is `repr(transparent)`
        f(unsafe { self.cast_ty() })
    }
}

impl<'this, P, T> Ptr<P, T> {
    /// Compare two pointers for equality. Because of the `HasAllocated` constraint, the target can
    /// never have been deallocated, so address equality implies that the pointers are
    /// interchangeable. The returned equality predicate is a witness of this interchangeability.
    /// This would not be the case with `IsPointsTo`, as two pointers can have the same address but
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

/// Give a name to the hidden lifetime in a pointer permissions.
pub fn unpack_opt_perm_lt<Perm, T, R>(
    ptr: Option<Ptr<ExistsLt<Perm>, T>>,
    f: impl for<'this> FnOnce(Option<Ptr<Perm::Of<'this>, T>>) -> R,
) -> R
where
    Perm: PackLt,
    for<'a> Perm::Of<'a>: PtrPerm,
{
    match ptr {
        None => f(None),
        Some(ptr) => ptr.unpack_lt(|ptr| f(Some(ptr))),
    }
}

/// Hide the lifetime in a pointer permissions.
pub fn pack_perm_lt<'this, Perm: PackLt, T>(ptr: Ptr<Perm::Of<'this>, T>) -> Ptr<ExistsLt<Perm>, T>
where
    for<'a> Perm::Of<'a>: PtrPerm,
{
    unsafe { ptr.cast_perm() }
}

/// Hide the lifetime in a pointer target.
pub fn pack_target_lt<'this, Perm: PtrPerm, T: PackLt>(
    ptr: Ptr<Perm, T::Of<'this>>,
) -> Ptr<Perm, ExistsLt<T>> {
    // Safety: `ExistsLt` is `repr(transparent)`
    unsafe { ptr.cast_ty() }
}

impl<Perm, T> Receiver for Ptr<Perm, T> {
    type Target = T;
}

impl<Perm, T> Debug for Ptr<Perm, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", std::any::type_name::<Self>())
    }
}
