use super::{ptr::*, ExistsLt};
use crate::ExistsLt;
use higher_kinded_types::ForLt as PackLt;
use std::{marker::PhantomData, mem::MaybeUninit};

/// Token that grants no permissions to a pointer.
pub struct NoPerm(PhantomData<()>);
unsafe impl PtrPerm for NoPerm {
    unsafe fn new() -> Self {
        NoPerm(PhantomData)
    }
}

unsafe impl<T: PackLt> PtrPerm for ExistsLt<T>
where
    for<'a> T::Of<'a>: PtrPerm,
{
    unsafe fn new() -> Self {
        ExistsLt::pack_lt(unsafe { <T::Of<'static>>::new() })
    }
}

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

unsafe impl<'this, Access: PtrAccess, Pred: PointeePred> PtrPerm for PointsTo<'this, Access, Pred> {
    unsafe fn new() -> Self {
        Self(PhantomData, PhantomData, InvariantLifetime::default())
    }
}

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

impl<T> Ptr<ExistsLt!(Own<'_>), T> {
    #[expect(unused)]
    pub fn new_owned(val: T) -> Self {
        let non_null = Box::into_non_null(Box::new(val));
        Ptr::new(non_null, unsafe { <_>::new() })
    }
}
impl<'this, Pred: PointeePred, T> Ptr<Own<'this, Pred>, T> {
    pub fn into_inner(self) -> T {
        // Safety: we have full ownership.
        *unsafe { Box::from_non_null(self.as_non_null()) }
    }
}

impl<T> Ptr<ExistsLt!(UninitOwned<'_>), T> {
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
        let ptr = Ptr::new(non_null, unsafe { <_>::new() });
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
    fn from_points_to(x: PointsTo<'this, Self::Access, Self::Pred>) -> Self;
    #[expect(unused)]
    fn into_points_to(self) -> PointsTo<'this, Self::Access, Self::Pred>;

    fn as_permissionless(&self) -> PointsTo<'this> {
        unsafe { <_>::new() }
    }
    #[expect(unused)]
    fn drop_access(self) -> PointsTo<'this, (), Self::Pred> {
        unsafe { PointsTo::new() }
    }
    fn drop_pred(self) -> PointsTo<'this, Self::Access, ()> {
        unsafe { PointsTo::new() }
    }
}
unsafe impl<'this, Access, Pred> IsPointsTo<'this> for PointsTo<'this, Access, Pred>
where
    Access: PtrAccess,
    Pred: PointeePred,
{
    type Pred = Pred;
    type Access = Access;
    fn into_points_to(self) -> Self {
        self
    }
    fn from_points_to(x: Self) -> Self {
        x
    }
}

pub unsafe trait AtLeastOwn: PtrAccess {}
unsafe impl AtLeastOwn for POwn {}

pub unsafe trait AtLeastMut: PtrAccess {}
unsafe impl<T: AtLeastOwn> AtLeastMut for T {}
unsafe impl AtLeastMut for PMut<'_> {}

pub unsafe trait AtLeastRead: PtrAccess {}
unsafe impl<T: AtLeastMut> AtLeastRead for T {}
unsafe impl AtLeastRead for PRead<'_> {}

pub unsafe trait AtLeastAllocated: PtrAccess {}
unsafe impl<T: AtLeastRead> AtLeastAllocated for T {}

pub trait HasOwn<'this> = IsPointsTo<'this, Access: AtLeastOwn>;

pub trait HasMut<'this>: IsPointsTo<'this, Access: AtLeastMut> {
    fn as_mut(&mut self) -> Mut<'this, '_, Self::Pred> {
        unsafe { <_>::new() }
    }
}
impl<'this, T> HasMut<'this> for T where T: IsPointsTo<'this, Access: AtLeastMut> {}

pub trait HasRead<'this>: IsPointsTo<'this, Access: AtLeastRead> {
    fn as_read(&self) -> Read<'this, '_, Self::Pred> {
        unsafe { <_>::new() }
    }
}
impl<'this, T> HasRead<'this> for T where T: IsPointsTo<'this, Access: AtLeastRead> {}

/// The target is guaranteed to stay allocated as long as the permission exists.
pub trait HasAllocated<'this> = IsPointsTo<'this, Access: AtLeastAllocated>;

/// Describes the behavior of nested permissions. Namely, a `Ptr<Outer, Ptr<Self, T>>` can be
/// turned into `(Ptr<Outer, Ptr<PointsTo, T>>, Ptr<Output, T>)`.
pub unsafe trait AccessThrough<Outer: PtrAccess>: PtrAccess {
    type AccessThrough: PtrAccess;
}

/// Helper type that constructs the through-permission for a given pair of permissions.
#[allow(type_alias_bounds)]
pub type AccessThroughType<'outer, 'inner, OuterPerm, InnerPerm>
where
    OuterPerm: IsPointsTo<'outer>,
    InnerPerm: IsPointsTo<'inner, Access: AccessThrough<OuterPerm::Access>>,
= PointsTo<
    'inner,
    <InnerPerm::Access as AccessThrough<OuterPerm::Access>>::AccessThrough,
    InnerPerm::Pred,
>;

mod access_through_impls {
    use super::*;
    /// `Own` gives full access to inner permissions.
    unsafe impl<Perm: PtrAccess, Access: AtLeastOwn> AccessThrough<Access> for Perm {
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
