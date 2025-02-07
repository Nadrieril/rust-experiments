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

/// Full ownership to a location with uninitialized data. Can be written to to get a normal owned
/// pointer.
pub struct PUninitOwned;
pub type UninitOwned<'this, Pred = ()> = PointsTo<'this, PUninitOwned, Pred>;

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
        unsafe { self.cast_access() }
    }
}

pub unsafe trait IsPointsTo: Sized {
    type Pred;
    type Access;
}
unsafe impl<'this, Access, Pred> IsPointsTo for PointsTo<'this, Access, Pred> {
    type Pred = Pred;
    type Access = Access;
}

pub unsafe trait HasOwn<'this>: HasWeak<'this> {}
unsafe impl<'this, Pred> HasOwn<'this> for Own<'this, Pred> {}

pub unsafe trait HasMut<'this>: HasWeak<'this> {}
unsafe impl<'this, T: HasOwn<'this>> HasMut<'this> for T {}
unsafe impl<'this, Pred> HasMut<'this> for Mut<'this, '_, Pred> {}

pub unsafe trait HasRead<'this>: HasWeak<'this> {}
unsafe impl<'this, T: HasMut<'this>> HasRead<'this> for T {}
unsafe impl<'this, Pred> HasRead<'this> for Read<'this, '_, Pred> {}

pub unsafe trait HasWeak<'this>: IsPointsTo {}
unsafe impl<'this, Access, Pred> HasWeak<'this> for PointsTo<'this, Access, Pred> {}

/// Describes the behavior of nested permissions. Namely, a `Ptr<Outer, Ptr<Self, T>>` can be
/// turned into `(Ptr<Outer, Ptr<Weak, T>>, Ptr<Output, T>)`.
pub unsafe trait AccessThrough<Outer>: IsPointsTo {
    type AccessThrough: IsPointsTo<Pred = Self::Pred>;
}
mod access_through_impls {
    use super::*;
    /// `Own` gives full access to inner permissions.
    unsafe impl<'this, Pred, Perm: IsPointsTo> AccessThrough<Own<'this, Pred>> for Perm {
        type AccessThrough = Perm;
    }
    /// `Mut` gives at most `Mut` access.
    unsafe impl<'outer, 'inner, 'a, 'b, OuterPred, InnerPred>
        AccessThrough<Mut<'outer, 'a, OuterPred>> for Own<'inner, InnerPred>
    {
        type AccessThrough = Mut<'inner, 'a, InnerPred>;
    }
    unsafe impl<'outer, 'inner, 'a, 'b, OuterPred, InnerPred>
        AccessThrough<Mut<'outer, 'a, OuterPred>> for Mut<'inner, 'b, InnerPred>
    {
        type AccessThrough = Mut<'inner, 'a, InnerPred>;
    }
    unsafe impl<'outer, 'inner, 'a, 'b, OuterPred, InnerPred>
        AccessThrough<Mut<'outer, 'a, OuterPred>> for Read<'inner, 'b, InnerPred>
    {
        type AccessThrough = Read<'inner, 'b, InnerPred>;
    }
    unsafe impl<'outer, 'inner, 'a, OuterPred, InnerPred> AccessThrough<Mut<'outer, 'a, OuterPred>>
        for Weak<'inner, InnerPred>
    {
        type AccessThrough = Weak<'inner, InnerPred>;
    }
    /// `Read` gives at most `Read` access.
    unsafe impl<'outer, 'inner, 'a, 'b, OuterPred, InnerPred>
        AccessThrough<Read<'outer, 'a, OuterPred>> for Own<'inner, InnerPred>
    {
        type AccessThrough = Read<'inner, 'a, InnerPred>;
    }
    unsafe impl<'outer, 'inner, 'a, 'b, OuterPred, InnerPred>
        AccessThrough<Read<'outer, 'a, OuterPred>> for Mut<'inner, 'b, InnerPred>
    {
        type AccessThrough = Read<'inner, 'b, InnerPred>;
    }
    unsafe impl<'outer, 'inner, 'a, 'b, OuterPred, InnerPred>
        AccessThrough<Read<'outer, 'a, OuterPred>> for Read<'inner, 'b, InnerPred>
    {
        type AccessThrough = Read<'inner, 'b, InnerPred>;
    }
    unsafe impl<'outer, 'inner, 'a, OuterPred, InnerPred> AccessThrough<Read<'outer, 'a, OuterPred>>
        for Weak<'inner, InnerPred>
    {
        type AccessThrough = Weak<'inner, InnerPred>;
    }
}

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
