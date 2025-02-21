use super::ptr::*;
use higher_kinded_types::ForLt as PackLt;
use std::{marker::PhantomData, mem::MaybeUninit};

/// Token that grants no permissions to a pointer.
pub struct NoPerm(PhantomData<()>);
unsafe impl PtrPerm for NoPerm {}

unsafe impl<T: PackLt> PtrPerm for T where for<'a> T::Of<'a>: PtrPerm {}

/// A predicate meant for a pointer.
/// `Perm` indicates what kind of accesses this pointer is allowed to do.
/// `Pred` is a predicate on the pointed-to-value.
/// `'this` is a lifetime brand that is used to identify pointers known to have the same address.
///
/// A plain `PointsTo<'this>` has no access and only records the address this points to.
pub struct PointsTo<'this, Access: PtrAccess = (), Pred: PointeePred = ()>(
    PhantomData<Access>,
    PhantomData<Pred>,
    InvariantLifetime<'this>,
);

unsafe impl<'this, Access: PtrAccess, Pred: PointeePred> PtrPerm for PointsTo<'this, Access, Pred> {}

/// An access permission through a pointer.
pub trait PtrAccess {}
impl PtrAccess for () {}

/// A predicate on a pointed-to value.
pub trait PointeePred {}
impl PointeePred for () {}

/// The separation logic points-to (unique ownership). This can read/write, modify permissions, and
/// deallocate its target.
pub struct POwn;
impl PtrAccess for POwn {}
pub type Own<'this, Pred = ()> = PointsTo<'this, POwn, Pred>;

/// Read/write access. This allows writing to the underlying values but not changing
/// types/permissions.
pub struct PMut<'a>(PhantomData<&'a mut ()>);
impl PtrAccess for PMut<'_> {}
pub type Mut<'this, 'a, Pred = ()> = PointsTo<'this, PMut<'a>, Pred>;

/// Read access
pub struct PRead<'a>(PhantomData<&'a ()>);
impl PtrAccess for PRead<'_> {}
pub type Read<'this, 'a, Pred = ()> = PointsTo<'this, PRead<'a>, Pred>;

/// Full ownership to a location with uninitialized data. Can be written to to get a normal owned
/// pointer.
pub struct PUninitOwned;
impl PtrAccess for PUninitOwned {}
pub type UninitOwned<'this, Pred = ()> = PointsTo<'this, PUninitOwned, Pred>;

impl<T> Ptr<PackLt!(Own<'_>), T> {
    #[expect(unused)]
    pub fn new(val: T) -> Self {
        let non_null = Box::into_non_null(Box::new(val));
        unsafe { Ptr::from_non_null(non_null) }
    }
}
impl<'this, Pred: PointeePred, T> Ptr<Own<'this, Pred>, T> {
    pub fn into_inner(self) -> T {
        // Safety: we have full ownership.
        *unsafe { Box::from_non_null(self.as_non_null()) }
    }
}

impl<T> Ptr<PackLt!(UninitOwned<'_>), T> {
    #[expect(unused)]
    pub fn new_uninit() -> Self {
        Ptr::new_uninit_cyclic::<PackLt!(T), _>(|ptr| pack_perm_lt(ptr))
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

pub unsafe trait IsPointsTo<'this>: PtrPerm + Sized {
    type Access: PtrAccess;
    type Pred: PointeePred;
}
unsafe impl<'this, Access, Pred> IsPointsTo<'this> for PointsTo<'this, Access, Pred>
where
    Access: PtrAccess,
    Pred: PointeePred,
{
    type Pred = Pred;
    type Access = Access;
}

pub unsafe trait HasOwn<'this>: IsPointsTo<'this> {}
unsafe impl<'this, Pred: PointeePred> HasOwn<'this> for Own<'this, Pred> {}

pub unsafe trait HasMut<'this>: IsPointsTo<'this> {}
unsafe impl<'this, T: HasOwn<'this>> HasMut<'this> for T {}
unsafe impl<'this, Pred: PointeePred> HasMut<'this> for Mut<'this, '_, Pred> {}

pub unsafe trait HasRead<'this>: IsPointsTo<'this> {}
unsafe impl<'this, T: HasMut<'this>> HasRead<'this> for T {}
unsafe impl<'this, Pred: PointeePred> HasRead<'this> for Read<'this, '_, Pred> {}

/// The target is guaranteed to stay allocated as long as the permission exists.
pub unsafe trait HasAllocated<'this>: IsPointsTo<'this> {}
unsafe impl<'this, T: HasRead<'this>> HasAllocated<'this> for T {}

/// Describes the behavior of nested permissions. Namely, a `Ptr<Outer, Ptr<Self, T>>` can be
/// turned into `(Ptr<Outer, Ptr<PointsTo, T>>, Ptr<Output, T>)`.
pub unsafe trait AccessThrough<Outer: PtrAccess>: PtrAccess {
    type AccessThrough: PtrAccess;
}

/// Helper trait that constructs the through-permission for a given pair.
pub trait AccessThroughHelper<'inner, 'outer, Outer>: IsPointsTo<'inner> {
    type AccessThrough: IsPointsTo<'inner, Pred = Self::Pred>;
}
impl<'inner, 'outer, InnerPerm, OuterPerm> AccessThroughHelper<'inner, 'outer, OuterPerm>
    for InnerPerm
where
    OuterPerm: IsPointsTo<'outer>,
    InnerPerm: IsPointsTo<'inner>,
    InnerPerm::Access: AccessThrough<OuterPerm::Access>,
{
    type AccessThrough = PointsTo<
        'inner,
        <InnerPerm::Access as AccessThrough<OuterPerm::Access>>::AccessThrough,
        InnerPerm::Pred,
    >;
}

mod access_through_impls {
    use super::*;
    /// `Own` gives full access to inner permissions.
    unsafe impl<Perm: PtrAccess> AccessThrough<POwn> for Perm {
        type AccessThrough = Perm;
    }
    /// `Mut` gives at most `Mut` access.
    unsafe impl<'a, 'b> AccessThrough<PMut<'a>> for POwn {
        type AccessThrough = PMut<'a>;
    }
    unsafe impl<'a, 'b> AccessThrough<PMut<'a>> for PMut<'b> {
        type AccessThrough = PMut<'a>;
    }
    unsafe impl<'a, 'b> AccessThrough<PMut<'a>> for PRead<'b> {
        type AccessThrough = PRead<'b>;
    }
    unsafe impl<'a> AccessThrough<PMut<'a>> for () {
        type AccessThrough = ();
    }
    /// `Read` gives at most `Read` access.
    unsafe impl<'a, 'b> AccessThrough<PRead<'a>> for POwn {
        type AccessThrough = PRead<'a>;
    }
    unsafe impl<'a, 'b> AccessThrough<PRead<'a>> for PMut<'b> {
        type AccessThrough = PRead<'b>;
    }
    unsafe impl<'a, 'b> AccessThrough<PRead<'a>> for PRead<'b> {
        type AccessThrough = PRead<'b>;
    }
    unsafe impl<'a> AccessThrough<PRead<'a>> for () {
        type AccessThrough = ();
    }
}

impl<'this, 'a, Perm: PointeePred, T> Ptr<Mut<'this, 'a, Perm>, T> {
    pub fn into_deref_mut(self) -> &'a mut T {
        // Safety: we have `Mut` permission for `'a`.
        unsafe { self.as_non_null().as_mut() }
    }
}
impl<'this, Perm: HasMut<'this>, T> Ptr<Perm, T> {
    pub fn deref_mut(&mut self) -> &mut T {
        // Safety: we have at least `Mut` permission.
        unsafe { self.as_non_null().as_mut() }
    }
}

impl<'this, 'a, Perm: PointeePred, T> Ptr<Read<'this, 'a, Perm>, T> {
    /// Like `deref` but get a more precise lifetime.
    pub fn deref_exact(&self) -> &'a T {
        // Safety: we have `Read` permission for `'a`.
        unsafe { self.as_non_null().as_ref() }
    }
}
impl<'this, Perm: HasRead<'this>, T> Ptr<Perm, T> {
    pub fn deref(&self) -> &T {
        // Safety: we have `Read` permission.
        unsafe { self.as_non_null().as_ref() }
    }
}
