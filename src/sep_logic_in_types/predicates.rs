use std::marker::PhantomData;

use super::*;

/// A type that is just a `repr(transparent)` on `Self::Unwrapped`.
pub unsafe trait TransparentWrapper: Sized {
    type Unwrapped;
    fn unwrap_target<'this, Perm: IsPointsTo<'this>>(
        self: Ptr<Perm, Self>,
    ) -> Ptr<Perm, Self::Unwrapped> {
        self.map_virtual(Self::unwrap_target_virt)
    }
    fn wrap_target<'this, Perm: IsPointsTo<'this>>(
        ptr: Ptr<Perm, Self::Unwrapped>,
    ) -> Ptr<Perm, Self> {
        ptr.map_virtual(Self::wrap_target_virt)
    }
    fn unwrap_target_virt<Perm: PtrPerm>(self: VPtr<Perm, Self>) -> VPtr<Perm, Self::Unwrapped> {
        Self::unwrap_target_wand().apply(self)
    }
    fn wrap_target_virt<Perm: PtrPerm>(ptr: VPtr<Perm, Self::Unwrapped>) -> VPtr<Perm, Self> {
        Self::wrap_target_wand().apply(ptr)
    }
    fn unwrap_target_wand<Perm: PtrPerm>() -> Wand<VPtr<Perm, Self>, VPtr<Perm, Self::Unwrapped>> {
        unsafe { Wand::from_thin_air() }
    }
    fn wrap_target_wand<Perm: PtrPerm>() -> Wand<VPtr<Perm, Self::Unwrapped>, VPtr<Perm, Self>> {
        unsafe { Wand::from_thin_air() }
    }
    fn unwrap_wand() -> Wand<Self, Self::Unwrapped> {
        unsafe { Wand::from_thin_air() }
    }
    #[expect(unused)]
    fn wrap_wand() -> Wand<Self::Unwrapped, Self> {
        unsafe { Wand::from_thin_air() }
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
    #[expect(unused)]
    pub fn ignore_tag<'this>(self) -> Ptr<Perm, T>
    where
        Perm: IsPointsTo<'this>,
    {
        self.map_virtual(|ptr| ptr.ignore_tag())
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
    pub fn ignore_tag(self) -> VPtr<Perm, T> {
        // Safety: `repr(transparent)` allows the cast.
        unsafe { self.cast_ty() }
    }
}
impl<Perm: PtrPerm, T> VPtr<Perm, T> {
    pub fn tag_target<'this, X: Phantom>(self, x: X) -> VPtr<Perm, Tagged<T, X>>
    where
        Perm: HasOwn<'this>,
    {
        Self::tag_target_wand().apply((self, x))
    }
    pub fn tag_target_wand<'this, X: Phantom>() -> Wand<(Self, X), VPtr<Perm, Tagged<T, X>>>
    where
        Perm: HasOwn<'this>,
    {
        unsafe {
            Wand::mimic_fn(|(ptr, _x)| {
                // Safety: `repr(transparent)` allows the cast. We respect linearity.
                ptr.cast_ty()
            })
        }
    }
}

unsafe impl<T: ErasePerms, X> ErasePerms for Tagged<T, X> {
    type Erased = T::Erased;
}

impl<T, X> std::ops::Deref for Tagged<T, X> {
    type Target = T;
    fn deref(&self) -> &Self::Target {
        &self.val
    }
}
impl<T, X> std::ops::DerefMut for Tagged<T, X> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.val
    }
}

/// Type-level wrapper type that can only be accessed if `'this` is a brand that corresponds to a
/// real pointer.
#[repr(transparent)]
pub struct IfReal<'this, T>(InvariantLifetime<'this>, T);

unsafe impl<'this, T: Phantom> Phantom for IfReal<'this, T> {}

impl<T: Phantom> IfReal<'static, T> {
    /// Since there is no real pointer with the `'static` brand, we can create this fake value,
    /// knowing it won't ever be accessed.
    pub fn not_real() -> Self {
        Self(PhantomData, unsafe { T::new() })
    }
}
impl<'this, T: Phantom> IfReal<'this, T> {
    pub fn lock(x: T) -> Self {
        Self(PhantomData, x)
    }
    pub fn lock_wand() -> Wand<T, Self> {
        unsafe { Wand::mimic_fn(Self::lock) }
    }
    pub fn unlock<U>(self, _: Ptr<PointsTo<'this>, U>) -> T {
        self.1
    }
    #[expect(unused)]
    pub fn unlock_wand<U>(ptr: Ptr<PointsTo<'this>, U>) -> Wand<Self, T> {
        unsafe { Wand::mimic_closure(|this: Self| this.unlock(ptr)) }
    }
}
