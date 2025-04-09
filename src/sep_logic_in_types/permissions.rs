use super::*;
use std::marker::PhantomData;

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
unsafe impl<'this, Access: PtrAccess, Pred: PointeePred> Phantom for PointsTo<'this, Access, Pred> {}
unsafe impl<'this, Access: PtrAccess, Pred: PointeePred> PtrPerm for PointsTo<'this, Access, Pred> {}

/// An access permission through a pointer.
pub trait PtrAccess {}
impl PtrAccess for () {}

/// A predicate on a pointed-to value.
/// TODO: remove this and redocument in terms of type overrides
pub trait PointeePred {}
impl PointeePred for () {}

pub unsafe trait HasAccess: PtrPerm + Sized {
    type Access: PtrAccess;
}
pub unsafe trait IsPointsTo<'this>: HasAccess {
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
    #[expect(unused)]
    fn drop_pred(self) -> PointsTo<'this, Self::Access, ()> {
        unsafe { PointsTo::new() }
    }
}
unsafe impl<'this, Access, Pred> HasAccess for PointsTo<'this, Access, Pred>
where
    Access: PtrAccess,
    Pred: PointeePred,
{
    type Access = Access;
}
unsafe impl<'this, Access, Pred> IsPointsTo<'this> for PointsTo<'this, Access, Pred>
where
    Access: PtrAccess,
    Pred: PointeePred,
{
    type Pred = Pred;
    fn into_points_to(self) -> Self {
        self
    }
    fn from_points_to(x: Self) -> Self {
        x
    }
}

/// Describes the behavior of nested permissions. Namely, a `Ptr<Outer, Ptr<Self, T>>` can be
/// turned into `(Ptr<Outer, Ptr<PointsTo, T>>, Ptr<Output, T>)`.
pub unsafe trait AccessThrough<Outer: PtrAccess>: PtrAccess {
    type AccessThrough: PtrAccess;
}

/// Helper type that constructs the through-permission for a given pair of permissions.
#[allow(type_alias_bounds)]
pub type AccessThroughType<'inner, OuterPerm, InnerPerm>
where
    OuterPerm: HasAccess,
    InnerPerm: IsPointsTo<'inner, Access: AccessThrough<OuterPerm::Access>>,
= PointsTo<
    'inner,
    <InnerPerm::Access as AccessThrough<OuterPerm::Access>>::AccessThrough,
    InnerPerm::Pred,
>;

impl<OuterPerm, InnerPerm, T> VPtr<OuterPerm, Ptr<InnerPerm, T>> {
    /// Take the permission from a pointer behind a (virtual) pointer. The permission that can be
    /// extracted that way is capped by the permission of the outer pointer; see the
    /// `AccessThrough` trait.
    pub fn read_nested_ptr<'this, 'inner>(
        self,
    ) -> (
        VPtr<OuterPerm, Ptr<PointsTo<'inner>, T>>,
        VPtr<AccessThroughType<'inner, OuterPerm, InnerPerm>, T>,
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

    #[expect(unused)]
    // TODO: how sound is this?
    pub fn write_nested_ptr<'this, 'inner, NewInnerPerm>(
        self,
        vptr: VPtr<AccessThroughType<'inner, OuterPerm, NewInnerPerm>, T>,
    ) -> VPtr<OuterPerm, Ptr<NewInnerPerm, T>>
    where
        OuterPerm: IsPointsTo<'this>,
        InnerPerm: IsPointsTo<'inner>,
        NewInnerPerm: IsPointsTo<'inner>,
        NewInnerPerm::Access: AccessThrough<OuterPerm::Access>,
    {
        self.write_nested_ptr_wand().apply(vptr)
    }

    pub fn write_nested_ptr_wand<'this, 'inner, NewInnerPerm>(
        self,
    ) -> Wand<
        VPtr<AccessThroughType<'inner, OuterPerm, NewInnerPerm>, T>,
        VPtr<OuterPerm, Ptr<NewInnerPerm, T>>,
    >
    where
        OuterPerm: IsPointsTo<'this>,
        InnerPerm: IsPointsTo<'inner>,
        NewInnerPerm: IsPointsTo<'inner>,
        NewInnerPerm::Access: AccessThrough<OuterPerm::Access>,
    {
        unsafe { Wand::from_thin_air() }
    }
}

pub use noperm::*;
mod noperm {
    use super::super::brands::Phantom;
    use super::super::ptr::*;
    use std::marker::PhantomData;

    /// Token that grants no permissions to a pointer.
    #[derive(Clone, Copy)]
    pub struct NoPerm(PhantomData<()>);
    unsafe impl Phantom for NoPerm {}
    unsafe impl PtrPerm for NoPerm {}
}

pub use own::*;
mod own {
    use super::super::{adts::*, ptr::*, ExistsLt};
    use super::*;
    use crate::ExistsLt;

    /// The separation logic points-to (unique ownership). This can read/write, modify permissions, and
    /// deallocate its target.
    pub struct POwn;
    impl PtrAccess for POwn {}
    pub type Own<'this, Pred = ()> = PointsTo<'this, POwn, Pred>;

    pub unsafe trait AtLeastOwn: PtrAccess {}
    unsafe impl AtLeastOwn for POwn {}

    pub trait HasOwn<'this> = IsPointsTo<'this, Access: AtLeastOwn>;

    /// `Own` gives full access to inner permissions.
    unsafe impl<Perm: PtrAccess, Access: AtLeastOwn> AccessThrough<Access> for Perm {
        type AccessThrough = Perm;
    }

    impl<'this, Perm: HasOwn<'this>, T> Ptr<Perm, T> {
        pub fn move_out(self) -> (Ptr<UninitOwned<'this>, T>, T) {
            let ret = unsafe { self.as_non_null().read() };
            let ptr = unsafe { self.cast_perm() };
            (ptr, ret)
        }
        pub fn into_inner(self) -> T {
            let (ptr, ret) = self.move_out();
            ptr.dealloc();
            ret
        }

        /// Write to the pointer in a way that can change its type. For non-type-changing writes,
        /// use `deref_mut`.
        // TODO: shouldn't this invalidate a pointee predicate?
        pub fn write<U>(self, new: U) -> Ptr<Perm, U>
        where
            Perm: HasOwn<'this>,
            T: ErasePerms,
            U: ErasePerms<Erased = T::Erased>,
        {
            // Drop the old value.
            let (ptr, _) = self.move_out();
            let ptr = unsafe { ptr.cast_ty() };
            let ptr = ptr.write(new);
            // FIXME: we restore the pointee predicate here but we shouldn't.
            unsafe { ptr.cast_perm() }
        }
    }
    impl Ptr<(), ()> {
        #[expect(unused)]
        pub fn new_owned<T>(val: T) -> ExistsLt!(Ptr<Own<'_>, T>) {
            let non_null = Box::into_non_null(Box::new(val));
            let ptr = unsafe { Ptr::new_with_perm(non_null, Own::new()) };
            ExistsLt::pack_lt(ptr)
        }
    }
}

pub use mutate::*;
mod mutate {
    use super::super::ptr::*;
    use super::*;
    use std::marker::PhantomData;

    /// Read/write access. This allows writing to the underlying values but not changing
    /// types/permissions.
    pub struct PMut<'a>(PhantomData<&'a mut ()>);
    impl PtrAccess for PMut<'_> {}
    pub type Mut<'this, 'a, Pred = ()> = PointsTo<'this, PMut<'a>, Pred>;

    pub unsafe trait AtLeastMut: PtrAccess {}
    unsafe impl<T: AtLeastOwn> AtLeastMut for T {}
    unsafe impl AtLeastMut for PMut<'_> {}

    pub trait HasMut<'this>: IsPointsTo<'this, Access: AtLeastMut> {
        fn as_mut(&mut self) -> Mut<'this, '_, Self::Pred> {
            unsafe { <_>::new() }
        }
    }
    impl<'this, T> HasMut<'this> for T where T: IsPointsTo<'this, Access: AtLeastMut> {}

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

    impl<'this, 'a, T> Ptr<Mut<'this, 'a>, T> {
        pub fn from_mut(r: &'a mut T) -> Self {
            unsafe { Ptr::new_with_perm(r.into(), Mut::new()) }
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
            self.copy_mut().into_deref_mut()
        }
    }
}

pub use read::*;
mod read {
    use super::super::ptr::*;
    use super::*;
    use std::marker::PhantomData;

    /// Read access
    #[derive(Clone, Copy)]
    pub struct PRead<'a>(PhantomData<&'a ()>);
    impl PtrAccess for PRead<'_> {}
    pub type Read<'this, 'a, Pred = ()> = PointsTo<'this, PRead<'a>, Pred>;

    pub unsafe trait AtLeastRead: PtrAccess {}
    unsafe impl<T: AtLeastMut> AtLeastRead for T {}
    unsafe impl AtLeastRead for PRead<'_> {}

    pub trait HasRead<'this>: IsPointsTo<'this, Access: AtLeastRead> {
        fn as_read(&self) -> Read<'this, '_, Self::Pred> {
            unsafe { <_>::new() }
        }
    }
    impl<'this, T> HasRead<'this> for T where T: IsPointsTo<'this, Access: AtLeastRead> {}

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

    impl<'this, 'a, T> Ptr<Read<'this, 'a>, T> {
        pub fn from_ref(r: &'a T) -> Self {
            unsafe { Ptr::new_with_perm(r.into(), Read::new()) }
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
            self.copy_read().deref_exact()
        }
    }
}

pub use uninit_owned::*;
mod uninit_owned {
    use super::super::{ptr::*, ExistsLt};
    use super::*;
    use crate::ExistsLt;
    use higher_kinded_types::ForLt as PackLt;
    use std::mem::MaybeUninit;

    /// Full ownership to a location with uninitialized data. Can be written to to get a normal owned
    /// pointer.
    pub struct PUninitOwned;
    impl PtrAccess for PUninitOwned {}
    pub type UninitOwned<'this, Pred = ()> = PointsTo<'this, PUninitOwned, Pred>;

    impl Ptr<(), ()> {
        /// Alloc a non-initialized location that can contain a pointer to itself.
        pub fn new_uninit<T: PackLt>() -> ExistsLt!(Ptr<UninitOwned<'_>, T::Of<'_>>) {
            let b: Box<MaybeUninit<T::Of<'_>>> = Box::new_uninit();
            let non_null = Box::into_non_null(b).cast::<T::Of<'_>>();
            let ptr = unsafe { Ptr::new_with_perm(non_null, UninitOwned::new()) };
            ExistsLt::pack_lt(ptr)
        }
    }

    impl<'this, T> Ptr<UninitOwned<'this>, T> {
        pub fn dealloc(self) {
            let b: Box<MaybeUninit<T>> = unsafe { Box::from_non_null(self.as_non_null().cast()) };
            drop(b);
        }
        pub fn write(self, val: T) -> Ptr<Own<'this>, T> {
            unsafe { self.as_non_null().write(val) };
            unsafe { self.cast_access() }
        }
    }
}

pub use allocated::*;
mod allocated {
    use super::*;

    pub unsafe trait AtLeastAllocated: PtrAccess {}
    unsafe impl<T: AtLeastRead> AtLeastAllocated for T {}
    unsafe impl AtLeastAllocated for PUninitOwned {}

    /// The target is guaranteed to stay allocated as long as the permission exists.
    pub trait HasAllocated<'this> = IsPointsTo<'this, Access: AtLeastAllocated>;
}

/// The copyability of a pointer is constrained by the access granted by this pointer.
impl<'this, Access: PtrAccess + Clone, Pred: PointeePred> Clone for PointsTo<'this, Access, Pred> {
    fn clone(&self) -> Self {
        Self(self.0, self.1, self.2)
    }
}
impl<'this, Access: PtrAccess + Copy, Pred: PointeePred> Copy for PointsTo<'this, Access, Pred> {}
