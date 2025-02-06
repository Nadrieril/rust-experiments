use super::*;
use higher_kinded_types::ForLt as PackLt;
use std::{fmt::Debug, marker::PhantomData, ptr::NonNull};

// Copied from `ghost_cell`.
pub type InvariantLifetime<'brand> = PhantomData<fn(&'brand ()) -> &'brand ()>;

/// A pointer to a `T` with permission `Perm` (either `PointsTo` or `Weak`).
/// Note: dropping this value may leak the target. To deallocate, call `into_inner`.
/// `Perm` will generally be either `PointsTo<...>` or `PackLt!(PointsTo<...>)`.
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

    pub unsafe fn unsafe_copy(&self) -> Self {
        Ptr {
            ptr: self.ptr,
            pred: PhantomData,
        }
    }

    pub fn weak_ref_no_erase<'this>(&self) -> Ptr<Weak<'this>, T>
    where
        Perm: HasWeak<'this>,
    {
        unsafe { self.unsafe_copy().cast_perm() }
    }

    pub fn weak_ref<'this>(&self) -> Ptr<Weak<'this>, T::Erased>
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
        f(unsafe { self.unsafe_copy().cast_perm() })
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
        f(unsafe { self.unsafe_copy().cast_perm() })
    }
}

/// Hide the lifetime in a pointer permissions.
pub fn pack_lt<'this, Perm: PackLt, T>(ptr: Ptr<Perm::Of<'this>, T>) -> Ptr<Perm, T> {
    unsafe { ptr.cast_perm() }
}

/// Give a name to the hidden lifetime in a pointer permissions.
pub fn unpack_opt_lt<Perm, T, R>(
    ptr: Option<Ptr<Perm, T>>,
    f: impl for<'this> FnOnce(Option<Ptr<Perm::Of<'this>, T>>) -> R,
) -> R
where
    Perm: PackLt,
{
    f(ptr.map(|ptr| unsafe { ptr.cast_perm() }))
}

impl<Perm, T> Debug for Ptr<Perm, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", std::any::type_name::<Self>())
    }
}
