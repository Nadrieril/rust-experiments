use std::marker::PhantomData;

use super::*;

/// A predicate on a pointed-to value. It is defined by the fact that `Ptr<PointsTo<'this, Access,
/// Self>, Ty>` and `Ptr<PointsTo<'this, Access>, Self::Unpacked>` are interchangeable. This makes
/// it possible to represent inductive predicates, that are rolled/unrolled using the
/// `pack`/`unpack` methods.
pub trait PackedPredicate<'this, Ty>: PointeePred + Sized {
    type Unpacked: ErasePerms<Erased = Ty>;
    /// Given a pointer with `Self` permission, turn it into a pointer to the type with permissions
    /// applied.
    fn unpack<A: PtrAccess>(
        ptr: Ptr<PointsTo<'this, A, Self>, Ty>,
    ) -> Ptr<PointsTo<'this, A>, Self::Unpacked> {
        ptr.map_virtual(Self::unpack_virt)
    }
    /// Reverse of `unpack`.
    fn pack<A: PtrAccess>(
        ptr: Ptr<PointsTo<'this, A>, Self::Unpacked>,
    ) -> Ptr<PointsTo<'this, A, Self>, Ty> {
        ptr.map_virtual(Self::pack_virt)
    }
    /// Given a pointer with `Self` permission, turn it into a pointer to the type with permissions
    /// applied.
    fn unpack_virt<A: PtrAccess>(
        ptr: VPtr<PointsTo<'this, A, Self>, Ty>,
    ) -> VPtr<PointsTo<'this, A>, Self::Unpacked> {
        Self::unpack_wand().apply(ptr)
    }
    /// Reverse of `unpack`.
    fn pack_virt<A: PtrAccess>(
        ptr: VPtr<PointsTo<'this, A>, Self::Unpacked>,
    ) -> VPtr<PointsTo<'this, A, Self>, Ty> {
        Self::pack_wand().apply(ptr)
    }
    /// Given a pointer with `Self` permission, turn it into a pointer to the type with permissions
    /// applied.
    fn unpack_wand<A: PtrAccess>(
    ) -> Wand<VPtr<PointsTo<'this, A, Self>, Ty>, VPtr<PointsTo<'this, A>, Self::Unpacked>> {
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
    /// Reverse of `unpack`.
    fn pack_wand<A: PtrAccess>(
    ) -> Wand<VPtr<PointsTo<'this, A>, Self::Unpacked>, VPtr<PointsTo<'this, A, Self>, Ty>> {
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

/// A value of type `T`, associated with a ZST `X`.
#[repr(transparent)]
pub struct Tagged<T, X> {
    val: T,
    // Safety: we actually own an instance of `X` (hence it's safe to later recreate it with
    // `Phantom::new()`). We would store it as `X` if we could, but that undermines the
    // `repr(transparent)`.
    tag: PhantomData<X>,
}

impl<Perm: PtrPerm, T, X: Phantom> Ptr<Perm, Tagged<T, X>> {
    pub fn untag_target<'this>(self) -> (Ptr<Perm, T>, X)
    where
        Perm: HasOwn<'this>,
    {
        let this = self.copy();
        let (vptr, tag) = self.into_virtual().untag_target();
        (this.with_virtual(vptr), tag)
    }
}
impl<Perm: PtrPerm, T> Ptr<Perm, T> {
    pub fn tag_target<'this, X: Phantom>(self, x: X) -> Ptr<Perm, Tagged<T, X>>
    where
        Perm: HasOwn<'this>,
    {
        self.map_virtual(|ptr| ptr.tag_target(x))
    }
}
impl<Perm: PtrPerm, T, X: Phantom> VPtr<Perm, Tagged<T, X>> {
    pub fn untag_target<'this>(self) -> (VPtr<Perm, T>, X)
    where
        Perm: HasOwn<'this>,
    {
        // Safety: `repr(transparent)` allows the cast.
        let ptr = unsafe { self.cast_ty() };
        // Safety: we respect linearity so it's ok to recreate the value here.
        let tag = unsafe { Phantom::new() };
        (ptr, tag)
    }
}
impl<Perm: PtrPerm, T> VPtr<Perm, T> {
    pub fn tag_target<'this, X: Phantom>(self, x: X) -> VPtr<Perm, Tagged<T, X>>
    where
        Perm: HasOwn<'this>,
    {
        Self::tag_target_wand(x).apply(self)
    }
    pub fn tag_target_wand<'this, X: Phantom>(_x: X) -> Wand<Self, VPtr<Perm, Tagged<T, X>>>
    where
        Perm: HasOwn<'this>,
    {
        unsafe {
            Wand::mimic_fn(|ptr| {
                // Safety: `repr(transparent)` allows the cast. We respect linearity.
                ptr.cast_ty()
            })
        }
    }
}

unsafe impl<T: ErasePerms, X> ErasePerms for Tagged<T, X> {
    type Erased = T::Erased;
}
