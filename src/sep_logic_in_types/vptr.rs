use super::*;
use std::{marker::PhantomData, ops::Receiver};

/// Like `Ptr` but doesn't store an address. Used to manage permissions in ways unobservable at
/// runtime.
pub struct VPtr<Perm, T> {
    /// We store the permission directly instead of as a `PhantomData` to encourage linear usage.
    perm: Perm,
    /// We're invariant in `T` to avoid surprises. We can only soundly be covariant in `T` for some
    /// values of `Perm`, which seems hard to express, if at all possible.
    phantom: PhantomData<*mut T>,
}

impl<Perm: PtrPerm, T> VPtr<Perm, T> {
    pub unsafe fn new(perm: Perm) -> Self {
        Self {
            perm,
            phantom: PhantomData,
        }
    }
    /// Helper.
    unsafe fn with_perm<'this, NewPerm>(self, perm: NewPerm) -> VPtr<NewPerm, T>
    where
        Perm: IsPointsTo<'this>,
        NewPerm: IsPointsTo<'this>,
    {
        unsafe { VPtr::new(perm) }
    }

    pub unsafe fn cast_perm<NewPerm: PtrPerm>(self) -> VPtr<NewPerm, T> {
        unsafe { VPtr::new(NewPerm::new()) }
    }
    pub unsafe fn cast_ty<U>(self) -> VPtr<Perm, U> {
        unsafe { VPtr::new(self.perm) }
    }
    pub unsafe fn cast_access<'this, NewPerm>(self) -> VPtr<NewPerm, T>
    where
        Perm: IsPointsTo<'this>,
        NewPerm: IsPointsTo<'this, Pred = Perm::Pred>,
    {
        unsafe { self.cast_perm() }
    }
    pub unsafe fn cast_pred<'this, NewPerm>(self) -> VPtr<NewPerm, T>
    where
        Perm: IsPointsTo<'this>,
        NewPerm: IsPointsTo<'this, Access = Perm::Access>,
    {
        unsafe { self.cast_perm() }
    }

    /// Unsafely copy this pointer, duplicating its permission.
    pub unsafe fn unsafe_copy(&self) -> Self {
        unsafe { VPtr::new(Perm::new()) }
    }
    /// Copy the pointer. The copied pointer has no permissions.
    pub fn copy<'this>(&self) -> VPtr<PointsTo<'this>, T>
    where
        Perm: IsPointsTo<'this>,
    {
        unsafe { VPtr::new(self.perm.as_permissionless()) }
    }
    pub fn copy_read<'this, 'a>(&'a self) -> VPtr<Read<'this, 'a, Perm::Pred>, T>
    where
        Perm: HasRead<'this>,
    {
        unsafe { self.copy().with_perm(self.perm.as_read()) }
    }
    pub fn copy_mut<'this, 'a>(&'a mut self) -> VPtr<Mut<'this, 'a, Perm::Pred>, T>
    where
        Perm: HasMut<'this>,
    {
        unsafe { self.copy().with_perm(self.perm.as_mut()) }
    }

    /// Transform the contained permission.
    pub fn pack_perm<'this>(ptr: VPtr<PointsTo<'this, Perm::Access, Perm::Pred>, T>) -> Self
    where
        Perm: IsPointsTo<'this>,
    {
        unsafe { VPtr::new(Perm::from_points_to(ptr.perm)) }
    }

    pub fn drop_target_perms(self) -> VPtr<Perm, T::Erased>
    where
        T: EraseNestedPerms,
    {
        T::erase_nested_perms(self)
    }
}

impl<OuterPerm, InnerPerm, T> VPtr<OuterPerm, Option<Ptr<InnerPerm, T>>> {
    /// Take the permission from a pointer behind a (virtual) pointer. The permission that can be
    /// extracted that way is capped by the permission of the outer pointer; see the
    /// `AccessThrough` trait.
    pub fn read_nested_ptr<'this, 'inner>(
        self,
    ) -> (
        VPtr<OuterPerm, Option<Ptr<PointsTo<'inner>, T>>>,
        VPtr<AccessThroughType<'this, 'inner, OuterPerm, InnerPerm>, T>,
    )
    where
        OuterPerm: IsPointsTo<'this>,
        InnerPerm: IsPointsTo<'inner>,
        InnerPerm::Access: AccessThrough<OuterPerm::Access>,
    {
        // Safety: by the invariant of `AccessThrough`, it's ok to get that pointer out.
        let inner = unsafe { VPtr::new(<_>::new()) };
        // Safety: we're downgrading a `IsPointsTo<'a>` to a `PointsTo<'a>`, which is fine even
        // without any particular permissions on `ptr`.
        let ptr = unsafe { self.cast_ty() };
        (ptr, inner)
    }

    /// The opposite of `read_nested_ptr`: writes a permission to a pointer behind a (virtual)
    /// pointer. This does not write to memory, hence cannot be used to change the address of the
    /// inner pointer.
    // TODO: shouldn't this invalidate a potential pointee predicate in `OuterPerm`?
    pub fn write_nested_ptr_perm<'this, 'inner, NewInnerPerm>(
        self,
        _new: VPtr<NewInnerPerm, T>,
    ) -> VPtr<OuterPerm, Option<Ptr<NewInnerPerm, T>>>
    where
        OuterPerm: HasOwn<'this>,
        InnerPerm: IsPointsTo<'inner>,
        NewInnerPerm: IsPointsTo<'inner>,
    {
        unsafe { self.cast_ty() }
    }
}

impl<Perm, T> Receiver for VPtr<Perm, T> {
    type Target = T;
}
