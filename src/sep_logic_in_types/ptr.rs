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
    /// Use a `VPtr` internally to track permissions.
    vptr: VPtr<Perm, T>,
}

/// Permission token on a pointer.
/// Safety: must be transmutable with `PhantomData`.
pub unsafe trait PtrPerm: Sized {
    /// Unsafely create a new permission token.
    /// Safety: ensure the permission is correct for the pointee it will get attached to.
    unsafe fn new() -> Self;
}

impl<Perm: PtrPerm, T> Ptr<Perm, T> {
    pub unsafe fn new_with_perm(ptr: NonNull<T>, perm: Perm) -> Self {
        unsafe { Self::new_with_vptr(ptr, VPtr::new(perm)) }
    }
    pub unsafe fn new_with_vptr(ptr: NonNull<T>, vptr: VPtr<Perm, T>) -> Self {
        Self { ptr, vptr }
    }

    /// Turn this into a virtual pointer with the same permission.
    pub fn into_virtual(self) -> VPtr<Perm, T> {
        self.vptr
    }
    /// Turn this into a virtual pointer with the same permission.
    pub fn as_virtual(&self) -> &VPtr<Perm, T> {
        &self.vptr
    }
    /// Turn this into a virtual pointer with the same permission.
    pub fn as_virtual_mut(&mut self) -> &mut VPtr<Perm, T> {
        &mut self.vptr
    }
    /// Replaces the permission of this pointer with that of the given virtual pointer.
    pub fn with_virtual<'this, NewPerm, U>(self, vptr: VPtr<NewPerm, U>) -> Ptr<NewPerm, U>
    where
        Perm: IsPointsTo<'this>,
        NewPerm: IsPointsTo<'this>,
    {
        // Using and casting this pointer is fine because `IsPointsTo` guarantees that both are
        // pointing to the same place.
        unsafe { Ptr::new_with_vptr(self.ptr.cast(), vptr) }
    }

    pub fn as_non_null(&self) -> NonNull<T> {
        self.ptr
    }

    pub unsafe fn cast_ty<U>(self) -> Ptr<Perm, U> {
        unsafe { Ptr::new_with_vptr(self.ptr.cast(), self.vptr.cast_ty()) }
    }
    pub unsafe fn cast_access<'this, NewPerm>(self) -> Ptr<NewPerm, T>
    where
        Perm: IsPointsTo<'this>,
        NewPerm: IsPointsTo<'this, Pred = Perm::Pred>,
    {
        self.map_virtual(|v| unsafe { v.cast_access() })
    }
    pub unsafe fn cast_pred<'this, NewPerm>(self) -> Ptr<NewPerm, T>
    where
        Perm: IsPointsTo<'this>,
        NewPerm: IsPointsTo<'this, Access = Perm::Access>,
    {
        self.map_virtual(|v| unsafe { v.cast_pred() })
    }

    /// Unsafely copy this pointer, duplicating its permission.
    #[expect(unused)]
    pub unsafe fn unsafe_copy<'this>(&self) -> Self
    where
        Perm: IsPointsTo<'this>,
    {
        self.map_virtual_ref(|v| unsafe { v.unsafe_copy() })
    }
    /// Copy the pointer. The copied pointer has no permissions.
    pub fn copy<'this>(&self) -> Ptr<PointsTo<'this>, T>
    where
        Perm: IsPointsTo<'this>,
    {
        // Note: can't implement on terms of `map_virtual_ref` because `map_virtual_ref` is
        // implemented in terms of `copy`.
        unsafe { Ptr::new_with_vptr(self.ptr, self.vptr.copy()) }
    }
    pub fn copy_read<'this, 'a>(&'a self) -> Ptr<Read<'this, 'a, Perm::Pred>, T>
    where
        Perm: HasRead<'this>,
    {
        self.map_virtual_ref(|v| v.copy_read())
    }
    pub fn copy_mut<'this, 'a>(&'a mut self) -> Ptr<Mut<'this, 'a, Perm::Pred>, T>
    where
        Perm: HasMut<'this>,
    {
        self.map_virtual_mut(|v| v.copy_mut())
    }

    pub fn drop_target_perms<'this>(self) -> Ptr<Perm, T::Erased>
    where
        Perm: IsPointsTo<'this>,
        T: EraseNestedPerms,
    {
        self.map_virtual(|v| v.drop_target_perms())
    }
    pub fn weak_ref<'this>(&self) -> Ptr<PointsTo<'this>, T::Erased>
    where
        Perm: IsPointsTo<'this>,
        T: EraseNestedPerms,
    {
        self.copy().drop_target_perms()
    }

    pub fn map_virtual<'this, NewPerm, U>(
        self,
        f: impl FnOnce(VPtr<Perm, T>) -> VPtr<NewPerm, U>,
    ) -> Ptr<NewPerm, U>
    where
        Perm: IsPointsTo<'this>,
        NewPerm: IsPointsTo<'this>,
    {
        self.copy().with_virtual(f(self.into_virtual()))
    }
    /// Transform the contained permission.
    pub fn map_virtual_ref<'this, 'a, NewPerm>(
        &'a self,
        f: impl FnOnce(&'a VPtr<Perm, T>) -> VPtr<NewPerm, T>,
    ) -> Ptr<NewPerm, T>
    where
        Perm: IsPointsTo<'this>,
        NewPerm: IsPointsTo<'this>,
    {
        self.copy().with_virtual(f(self.as_virtual()))
    }
    /// Transform the contained permission.
    pub fn map_virtual_mut<'this, 'a, NewPerm>(
        &'a mut self,
        f: impl FnOnce(&'a mut VPtr<Perm, T>) -> VPtr<NewPerm, T>,
    ) -> Ptr<NewPerm, T>
    where
        Perm: IsPointsTo<'this>,
        NewPerm: IsPointsTo<'this>,
    {
        self.copy().with_virtual(f(self.as_virtual_mut()))
    }

    /// Transform the contained permission.
    pub fn pack_perm<'this>(ptr: Ptr<PointsTo<'this, Perm::Access, Perm::Pred>, T>) -> Self
    where
        Perm: IsPointsTo<'this>,
    {
        ptr.map_virtual(|v| VPtr::pack_perm(v))
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
    /// Read a pointer behind a pointer. The permission that can be extracted that way is capped by
    /// the permission of the outer pointer; see the `AccessThrough` trait.
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
        // Copy the pointers.
        let inner = self.deref().as_ref().map(|ptr| ptr.copy());
        let permissionless_outer = self.copy();
        // Extract the permissions.
        let (vouter, vinner) = self.into_virtual().read_nested_ptr();
        // Reassemble.
        let inner = inner.map(|inner| inner.with_virtual(vinner));
        let ptr = permissionless_outer.with_virtual(vouter);
        (ptr, inner)
    }

    /// Write to a pointer behind a pointer.
    // TODO: shouldn't this invalidate a potential pointee predicate in `OuterPerm`?
    pub fn write_nested_ptr<'this, NewInnerPerm>(
        self,
        new: Option<Ptr<NewInnerPerm, T>>,
    ) -> Ptr<OuterPerm, Option<Ptr<NewInnerPerm, T>>>
    where
        OuterPerm: HasOwn<'this>,
        InnerPerm: PtrPerm,
        NewInnerPerm: PtrPerm,
    {
        let mut ptr = unsafe { self.cast_ty() };
        *ptr.deref_mut() = new;
        ptr
    }

    /// The opposite of `read_nested_ptr`: writes a permission to a pointer behind a pointer. This
    /// does not write to memory, hence cannot be used to change the address of the inner pointer.
    pub fn write_nested_ptr_perm<'this, 'inner, NewInnerPerm>(
        self,
        new: VPtr<NewInnerPerm, T>,
    ) -> Ptr<OuterPerm, Option<Ptr<NewInnerPerm, T>>>
    where
        OuterPerm: HasOwn<'this>,
        InnerPerm: IsPointsTo<'inner>,
        NewInnerPerm: IsPointsTo<'inner>,
    {
        self.map_virtual(|v| v.write_nested_ptr_perm(new))
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
