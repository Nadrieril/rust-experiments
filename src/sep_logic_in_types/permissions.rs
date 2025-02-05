use super::ptr::*;
use higher_kinded_types::ForLt as PackLt;
use std::{
    fmt::Debug,
    marker::PhantomData,
    mem::MaybeUninit,
    ops::{Deref, DerefMut},
    ptr::NonNull,
};

/// The separation logic points-to (unique ownership), with a predicate on the pointed-to value.
/// The `'this` lifetime brand denotes the pointer address. This can be paired with some `Weak`
/// pointers with the same brand to statically track that they have the same address.
pub struct PointsTo<'this, Pred = ()>(PhantomData<Pred>, InvariantLifetime<'this>);

/// Read/write access, with a predicate on the pointed-to value. This allowd writing to the
/// underlying values but not changing types; in particular this can't change the list
/// structure.
pub struct Mut<'this, 'a, Pred = ()>(
    PhantomData<Pred>,
    PhantomData<&'a mut ()>,
    InvariantLifetime<'this>,
);

/// Read access, with a predicate on the pointed-to value.
pub struct Read<'this, 'a, Pred = ()>(
    PhantomData<Pred>,
    PhantomData<&'a ()>,
    InvariantLifetime<'this>,
);

/// A pointer with no permissions, known to be equal to 'this.
pub struct Weak<'this>(InvariantLifetime<'this>);

impl<T> Ptr<PackLt!(PointsTo<'_>), T> {
    pub fn new(val: T) -> Self {
        let non_null = Box::into_non_null(Box::new(val));
        unsafe { Ptr::from_non_null(non_null) }
    }
    pub fn into_inner(self) -> T {
        // Safety: we have points-to access.
        *unsafe { Box::from_non_null(self.as_non_null()) }
    }
}

impl<T, Perm> Ptr<PackLt!(PointsTo<'_, Perm>), T> {
    pub fn forget_permissions(self) -> Ptr<PackLt!(PointsTo<'_>), T> {
        unsafe { self.cast_perm() }
    }
}

/// A location that once written to we have ownership to.
pub struct UninitOwned<'this>(InvariantLifetime<'this>);

impl<T> Ptr<PackLt!(UninitOwned<'_>), T> {
    pub fn new_uninit() -> Self {
        let non_null = Box::into_non_null(Box::<MaybeUninit<T>>::new_uninit()).cast::<T>();
        unsafe { Self::from_non_null(non_null) }
    }
}

impl Ptr<(), ()> {
    /// Alloc a non-initialized location that can contain a pointer to itself. This
    /// self-reference will have to be hidden away before returning of course.
    pub fn new_uninit_cyclic<T: PackLt, R>(
        f: impl for<'this> FnOnce(Ptr<UninitOwned<'this>, T::Of<'this>>) -> R,
    ) -> R {
        let non_null =
            Box::into_non_null(Box::<MaybeUninit<T::Of<'_>>>::new_uninit()).cast::<T::Of<'_>>();
        let ptr = unsafe { Ptr::from_non_null(non_null) };
        f(ptr)
    }
}

impl<'this, T> Ptr<UninitOwned<'this>, T> {
    pub fn write(self, val: T) -> Ptr<PointsTo<'this>, T> {
        unsafe { self.as_non_null().write(val) };
        unsafe { self.cast_perm() }
    }
}

pub unsafe trait HasPointsTo<'this> {}
unsafe impl<'this, Perm> HasPointsTo<'this> for PointsTo<'this, Perm> {}

pub unsafe trait HasMut<'this> {}
unsafe impl<'this, T: HasPointsTo<'this>> HasMut<'this> for T {}
unsafe impl<'this, Perm> HasMut<'this> for Mut<'this, '_, Perm> {}

impl<'this, 'a, Perm, T> Ptr<Mut<'this, 'a, Perm>, T> {
    pub fn into_deref_mut(mut self) -> &'a mut T {
        // Safety: we have `Mut` permission for `'a`.
        unsafe { self.as_non_null().as_mut() }
    }
}
impl<'this, Perm: HasMut<'this>, T> DerefMut for Ptr<Perm, T> {
    fn deref_mut(&mut self) -> &mut T {
        // Safety: we have at least `Mut` permission.
        unsafe { self.as_non_null().as_mut() }
    }
}

pub unsafe trait HasRead<'this> {}
unsafe impl<'this, T: HasMut<'this>> HasRead<'this> for T {}
unsafe impl<'this, Perm> HasRead<'this> for Read<'this, '_, Perm> {}

impl<'this, 'a, Perm, T> Ptr<Read<'this, 'a, Perm>, T> {
    pub fn deref(&self) -> &'a T {
        // Safety: we have `Read` permission for `'a`.
        unsafe { self.as_non_null().as_ref() }
    }
}
impl<'this, Perm: HasRead<'this>, T> Deref for Ptr<Perm, T> {
    type Target = T;
    fn deref(&self) -> &T {
        // Safety: we have at least `Read` permission.
        unsafe { self.as_non_null().as_ref() }
    }
}

pub unsafe trait HasWeak<'this>: Sized {
    fn weaken<T>(ptr: &Ptr<Self, T>) -> Ptr<Weak<'this>, T> {
        unsafe { ptr.copy().cast_perm() }
    }
}
unsafe impl<'this, T: HasRead<'this>> HasWeak<'this> for T {}
unsafe impl<'this> HasWeak<'this> for Weak<'this> {}
unsafe impl<'this> HasWeak<'this> for UninitOwned<'this> {}
