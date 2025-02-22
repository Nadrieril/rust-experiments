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
    perm: Perm,
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
    pub fn new(ptr: NonNull<T>, perm: Perm) -> Self {
        Self {
            ptr,
            perm,
            phantom: PhantomData,
        }
    }

    /// Split the pointer into a permissionless pointer and a permission.
    pub fn split<'this>(self) -> (Ptr<PointsTo<'this>, T>, Perm)
    where
        Perm: IsPointsTo<'this>,
    {
        let ptr = unsafe { self.cast_perm() };
        (ptr, unsafe { Perm::new() })
    }

    /// Sets the permission of a pointer if the brand match.
    pub fn set_perm<'this, NewPerm>(self, perm: NewPerm) -> Ptr<NewPerm, T>
    where
        Perm: IsPointsTo<'this>,
        NewPerm: IsPointsTo<'this>,
    {
        Ptr {
            ptr: self.ptr,
            perm,
            phantom: PhantomData,
        }
    }

    /// Transform the contained permission.
    pub fn map_perm<'this, NewPerm>(self, f: impl FnOnce(Perm) -> NewPerm) -> Ptr<NewPerm, T>
    where
        Perm: IsPointsTo<'this>,
        NewPerm: IsPointsTo<'this>,
    {
        let (ptr, perm) = self.split();
        ptr.set_perm(f(perm))
    }

    pub fn as_non_null(&self) -> NonNull<T> {
        self.ptr
    }
    pub fn perm(&self) -> &Perm {
        &self.perm
    }
    pub fn perm_mut(&mut self) -> &mut Perm {
        &mut self.perm
    }

    pub unsafe fn cast_perm<NewPerm: PtrPerm>(self) -> Ptr<NewPerm, T> {
        Ptr {
            ptr: self.ptr,
            perm: unsafe { NewPerm::new() },
            phantom: PhantomData,
        }
    }
    pub unsafe fn cast_ty<U>(self) -> Ptr<Perm, U> {
        Ptr {
            ptr: self.ptr.cast(),
            perm: self.perm,
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
        Ptr::new(self.ptr, unsafe { Perm::new() })
    }

    /// Copy the pointer. The copied pointer has no permissions.
    pub fn copy<'this>(&self) -> Ptr<PointsTo<'this>, T>
    where
        Perm: IsPointsTo<'this>,
    {
        Ptr::new(self.as_non_null(), self.perm.as_permissionless())
    }
    #[expect(unused)]
    pub fn copy_read<'this>(&self) -> Ptr<Read<'this, '_, Perm::Pred>, T>
    where
        Perm: HasRead<'this>,
    {
        self.copy().set_perm(self.perm().as_read())
    }

    #[expect(unused)]
    pub fn copy_mut<'this>(&mut self) -> Ptr<Mut<'this, '_, Perm::Pred>, T>
    where
        Perm: HasMut<'this>,
    {
        self.copy().set_perm(self.perm_mut().as_mut())
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
        let (ptr, perm) = self.split();
        ptr.set_perm(perm.drop_pred())
    }

    /// Compare two pointers for equality. Because of the `HasAllocated` constraint, the target can
    /// never have been deallocated, so address equality implies that the pointers are
    /// interchangeable. The returned equality predicate is a witness of this interchangeability.
    /// This would not be the case with `IsPointsTo`, as two pointers can have the same address but
    /// different provenance.
    #[expect(unused)]
    pub fn eq<'this, 'other, Q, U>(&self, other: &Ptr<Q, U>) -> Option<EqPredicate<'this, 'other>>
    where
        Perm: HasAllocated<'this>,
        Q: HasAllocated<'other>,
    {
        if self.ptr.addr() == other.ptr.addr() {
            Some(unsafe { EqPredicate::make() })
        } else {
            None
        }
    }
}

impl<OuterPerm, InnerPerm, T> Ptr<OuterPerm, Option<Ptr<InnerPerm, T>>> {
    /// Read a pointer behind a pointer, taking the permissions with it as much as possible.
    pub fn read_nested_ptr<'this, 'inner>(
        self,
    ) -> (
        Ptr<OuterPerm, Option<Ptr<PointsTo<'inner>, T>>>,
        Option<Ptr<AccessThroughType<'this, 'inner, OuterPerm, InnerPerm>, T>>,
    )
    where
        OuterPerm: HasRead<'this>,
        InnerPerm: IsPointsTo<'inner>,
        InnerPerm::Access: AccessThrough<OuterPerm::Access>,
    {
        // Safety: by the invariant of `AccessThrough`, it's ok to get that pointer out.
        let inner = self
            .deref()
            .as_ref()
            .map(|ptr| unsafe { ptr.unsafe_copy().cast_access() });
        // Safety: we're downgrading a `IsPointsTo<'a>` to a `PointsTo<'a>`, which is fine even without
        // any particular permissions on `ptr`.
        let ptr = unsafe { self.cast_ty() };
        (ptr, inner)
    }

    pub fn write_nested_ptr<'this, NewInnerPerm>(
        mut self,
        new: Option<Ptr<NewInnerPerm, T>>,
    ) -> Ptr<OuterPerm, Option<Ptr<NewInnerPerm, T>>>
    where
        OuterPerm: HasOwn<'this>,
        InnerPerm: PtrPerm,
        NewInnerPerm: PtrPerm,
    {
        *self.deref_mut() = new.map(|new| unsafe { new.cast_perm() });
        unsafe { self.cast_ty() }
    }

    /// Like `write_nested_ptr` but does not write to memory.
    pub fn write_nested_ptr_perm<'this, 'inner, NewInnerPerm>(
        self,
        _new: NewInnerPerm,
    ) -> Ptr<OuterPerm, Option<Ptr<NewInnerPerm, T>>>
    where
        OuterPerm: HasOwn<'this>,
        InnerPerm: IsPointsTo<'inner>,
        NewInnerPerm: IsPointsTo<'inner>,
    {
        unsafe { self.cast_ty() }
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
