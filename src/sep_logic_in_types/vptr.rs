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
unsafe impl<Perm: Phantom, T> Phantom for VPtr<Perm, T> {}

impl<Perm: PtrPerm, T> VPtr<Perm, T> {
    pub unsafe fn new(perm: Perm) -> Self {
        Self {
            perm,
            phantom: PhantomData,
        }
    }
    /// The `'static` brand corresponds to no possible pointer. We allow crafting arbitrary
    /// permissions to it to simplify wand usage.
    pub fn new_impossible() -> Self
    where
        Perm: IsPointsTo<'static>,
    {
        unsafe { Self::new(Perm::new()) }
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

    pub fn erase_target_perms(self) -> VPtr<Perm, T::Erased>
    where
        T: ErasePerms,
    {
        unsafe { self.cast_ty() }
    }
}

impl<'this, A: PtrAccess, T: PointeePred> VPtr<PointsTo<'this, A, T>, T::Erased>
where
    T: ErasePerms,
{
    /// Move a type from the permission to the pointer target.
    pub fn unpack_ty(self) -> VPtr<PointsTo<'this, A>, T> {
        Self::unpack_ty_wand().apply(self)
    }
    /// Move a type from the permission to the pointer target.
    pub fn unpack_ty_wand() -> Wand<Self, VPtr<PointsTo<'this, A>, T>> {
        unsafe {
            Wand::mimic_fn(|ptr| {
                // Safety: by the `EraseNestedPerms` precondition this only changes predicates (i.e. ghost
                // types) so the two types are layout-compatible. Since the definition of `Self` as a
                // predicate is the effect of this function, this is definitionally a correct cast wrt
                // permissions.
                ptr.cast_pred().cast_ty()
            })
        }
    }
}
impl<'this, A: PtrAccess, T: PointeePred> VPtr<PointsTo<'this, A>, T>
where
    T: ErasePerms,
{
    /// Reverse of `unpack_ty`.
    pub fn pack_ty(self) -> VPtr<PointsTo<'this, A, T>, T::Erased> {
        Self::pack_ty_wand().apply(self)
    }
    /// Reverse of `unpack_ty`.
    pub fn pack_ty_wand() -> Wand<Self, VPtr<PointsTo<'this, A, T>, T::Erased>> {
        unsafe {
            Wand::mimic_fn(|ptr| {
                // Safety: by the `EraseNestedPerms` precondition this only changes predicates (i.e. ghost
                // types) so the two types are layout-compatible. Since the definition of `Self` as a
                // predicate is the effect of this function, this is definitionally a correct cast wrt
                // permissions.
                ptr.cast_pred().cast_ty()
            })
        }
    }
}

impl<OuterPerm, InnerPerm, T> VPtr<OuterPerm, Option<Ptr<InnerPerm, T>>> {
    /// The opposite of `read_nested_ptr`: writes a permission to a pointer behind a (virtual)
    /// pointer. This does not write to memory, hence cannot be used to change the address of the
    /// inner pointer.
    // TODO: shouldn't this invalidate a potential pointee predicate in `OuterPerm`?
    pub fn write_opt_ptr_perm<'this, 'inner, NewInnerPerm>(
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

    /// `write_opt_ptr_perm` implemented as a wand.
    pub fn write_opt_ptr_perm_wand<'this, 'inner, NewInnerPerm>(
        self,
    ) -> Wand<VPtr<NewInnerPerm, T>, VPtr<OuterPerm, Option<Ptr<NewInnerPerm, T>>>>
    where
        OuterPerm: HasOwn<'this>,
        InnerPerm: IsPointsTo<'inner>,
        NewInnerPerm: IsPointsTo<'inner>,
    {
        unsafe { Wand::mimic_closure(|new| self.write_opt_ptr_perm(new)) }
    }
}

impl<'this, T> VPtr<PointsTo<'this>, T> {
    // TODO: use this more
    pub fn permissionless() -> Self {
        unsafe { VPtr::new(PointsTo::new()) }
    }
}

impl<Perm: PtrPerm, T> VPtr<Perm, ExistsLt<T>>
where
    T: PackLt,
{
    /// Give a name to the hidden lifetime in a pointer target.
    #[expect(unused)]
    pub fn unpack_target_lt<R>(
        self,
        f: impl for<'this> FnOnce(VPtr<Perm, T::Of<'this>>) -> R,
    ) -> R {
        // Safety: `ExistsLt` is `repr(transparent)`
        f(unsafe { self.cast_ty() })
    }
}

/// Hide the lifetime in a pointer target.
#[expect(unused)]
pub fn vpack_target_lt<'this, Perm: PtrPerm, T: PackLt>(
    ptr: VPtr<Perm, T::Of<'this>>,
) -> VPtr<Perm, ExistsLt<T>> {
    vpack_target_lt_wand().apply(ptr)
}

/// Hide the lifetime in a pointer target.
pub fn vpack_target_lt_wand<'this, Perm: PtrPerm, T: PackLt>(
) -> Wand<VPtr<Perm, T::Of<'this>>, VPtr<Perm, ExistsLt<T>>> {
    unsafe {
        Wand::mimic_fn(|ptr| {
            // Safety: `ExistsLt` is `repr(transparent)`
            ptr.cast_ty()
        })
    }
}

impl<Perm, T> Receiver for VPtr<Perm, T> {
    type Target = T;
}

/// The copyability of a pointer is constrained by the permission.
impl<Perm: Clone, T> Clone for VPtr<Perm, T> {
    fn clone(&self) -> Self {
        Self {
            perm: self.perm.clone(),
            phantom: self.phantom.clone(),
        }
    }
}
impl<Perm: Copy, T> Copy for VPtr<Perm, T> {}
