use super::ptr::*;
use higher_kinded_types::ForLt as PackLt;
use std::{
    marker::PhantomData,
    mem::MaybeUninit,
    ops::{Deref, DerefMut},
};

/// A predicate applied to a pointer.
/// `Perm` indicates what kind of accesses this pointer is allowed to do.
/// `Pred` is a predicate on the pointed-to-value.
/// `'this` is a lifetime brand that is used to identify pointers known to have the same address.
pub struct PointsTo<'this, Perm, Pred = ()>(
    PhantomData<Perm>,
    PhantomData<Pred>,
    InvariantLifetime<'this>,
);

/// The separation logic points-to (unique ownership). This can read/write, modify permissions, and
/// deallocate its target.
pub struct POwn;
pub type Own<'this, Pred = ()> = PointsTo<'this, POwn, Pred>;

/// Read/write access. This allows writing to the underlying values but not changing
/// types/permissions.
pub struct PMut<'a>(PhantomData<&'a mut ()>);
pub type Mut<'this, 'a, Pred = ()> = PointsTo<'this, PMut<'a>, Pred>;

/// Read access
pub struct PRead<'a>(PhantomData<&'a ()>);
pub type Read<'this, 'a, Pred = ()> = PointsTo<'this, PRead<'a>, Pred>;

/// No access.
pub struct PNone;
pub type Weak<'this, Pred = ()> = PointsTo<'this, PNone, Pred>;

impl<T> Ptr<PackLt!(Own<'_>), T> {
    #[expect(unused)]
    pub fn new(val: T) -> Self {
        let non_null = Box::into_non_null(Box::new(val));
        unsafe { Ptr::from_non_null(non_null) }
    }
    #[expect(unused)]
    pub fn into_inner(self) -> T {
        // Safety: we have points-to access.
        *unsafe { Box::from_non_null(self.as_non_null()) }
    }
}

/// A location that once written to we have ownership to.
pub struct UninitOwned<'this>(InvariantLifetime<'this>);

impl<T> Ptr<PackLt!(UninitOwned<'_>), T> {
    #[expect(unused)]
    pub fn new_uninit() -> Self {
        Ptr::new_uninit_cyclic::<PackLt!(T), _>(|ptr| pack_lt(ptr))
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
    pub fn write(self, val: T) -> Ptr<Own<'this>, T> {
        unsafe { self.as_non_null().write(val) };
        unsafe { self.cast_perm() }
    }
}

pub unsafe trait HasPointsTo<'this> {}
unsafe impl<'this, Perm> HasPointsTo<'this> for Own<'this, Perm> {}

pub unsafe trait HasMut<'this> {}
unsafe impl<'this, T: HasPointsTo<'this>> HasMut<'this> for T {}
unsafe impl<'this, Perm> HasMut<'this> for Mut<'this, '_, Perm> {}

impl<'this, 'a, Perm, T> Ptr<Mut<'this, 'a, Perm>, T> {
    pub fn into_deref_mut(self) -> &'a mut T {
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

pub unsafe trait HasWeak<'this>: Sized {}
unsafe impl<'this, T: HasRead<'this>> HasWeak<'this> for T {}
unsafe impl<'this> HasWeak<'this> for Weak<'this> {}
unsafe impl<'this> HasWeak<'this> for UninitOwned<'this> {}
