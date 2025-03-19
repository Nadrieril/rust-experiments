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
    perm: Perm,
    /// We're invariant in `T` to avoid surprises. We can only soundly be covariant in `T` for some
    /// values of `Perm`, which seems hard to express, if at all possible.
    phantom: PhantomData<*mut T>,
}

/// Like `Ptr` but doesn't store an address. Used to manage permissions in ways unobservable at
/// runtime.
pub struct VPtr<Perm, T> {
    /// We store the permission directly instead of as a `PhantomData` to encourage linear usage.
    perm: Perm,
    /// We're invariant in `T` to avoid surprises. We can only soundly be covariant in `T` for some
    /// values of `Perm`, which seems hard to express, if at all possible.
    phantom: PhantomData<*mut T>,
}

/// Permission token on a pointer.
/// Safety: must be transmutable with `PhantomData`.
pub unsafe trait PtrPerm: Sized {
    /// Unsafely create a new permission token.
    /// Safety: ensure the permission is correct.
    unsafe fn new() -> Self;
}

impl<Perm: PtrPerm, T> Ptr<Perm, T> {
    pub unsafe fn new(ptr: NonNull<T>, perm: Perm) -> Self {
        Self {
            ptr,
            perm,
            phantom: PhantomData,
        }
    }

    /// Helper.
    unsafe fn with_perm<'this, NewPerm>(self, perm: NewPerm) -> Ptr<NewPerm, T>
    where
        Perm: IsPointsTo<'this>,
        NewPerm: IsPointsTo<'this>,
    {
        unsafe { Ptr::new(self.ptr, perm) }
    }

    /// Turn this into a virtual pointer with the same permission.
    pub fn into_virtual(self) -> VPtr<Perm, T> {
        unsafe { VPtr::new(self.perm) }
    }
    // /// Turn this into a virtual pointer with the same permission.
    // pub fn as_virtual(&self) -> &VPtr<Perm, T> {
    //     unsafe { VPtr::new() }
    // }

    /// Transform the contained permission.
    pub fn pack_perm<'this>(ptr: Ptr<PointsTo<'this, Perm::Access, Perm::Pred>, T>) -> Self
    where
        Perm: IsPointsTo<'this>,
    {
        unsafe { Ptr::new(ptr.ptr, Perm::from_points_to(ptr.perm)) }
    }

    pub fn as_non_null(&self) -> NonNull<T> {
        self.ptr
    }

    pub unsafe fn cast_perm<NewPerm: PtrPerm>(self) -> Ptr<NewPerm, T> {
        Ptr {
            ptr: self.ptr,
            perm: unsafe { NewPerm::new() },
            phantom: PhantomData,
        }
    }
    pub unsafe fn cast_ty<U>(self) -> Ptr<Perm, U> {
        Ptr {
            ptr: self.ptr.cast(),
            perm: self.perm,
            phantom: PhantomData,
        }
    }
    pub unsafe fn cast_access<'this, NewPerm>(self) -> Ptr<NewPerm, T>
    where
        Perm: IsPointsTo<'this>,
        NewPerm: IsPointsTo<'this, Pred = Perm::Pred>,
    {
        unsafe { self.cast_perm() }
    }
    pub unsafe fn cast_pred<'this, NewPerm>(self) -> Ptr<NewPerm, T>
    where
        Perm: IsPointsTo<'this>,
        NewPerm: IsPointsTo<'this, Access = Perm::Access>,
    {
        unsafe { self.cast_perm() }
    }

    pub unsafe fn unsafe_copy(&self) -> Self {
        unsafe { Ptr::new(self.ptr, Perm::new()) }
    }

    /// Copy the pointer. The copied pointer has no permissions.
    pub fn copy<'this>(&self) -> Ptr<PointsTo<'this>, T>
    where
        Perm: IsPointsTo<'this>,
    {
        unsafe { Ptr::new(self.as_non_null(), self.perm.as_permissionless()) }
    }
    pub fn copy_read<'this, 'a>(&'a self) -> Ptr<Read<'this, 'a, Perm::Pred>, T>
    where
        Perm: HasRead<'this>,
    {
        unsafe { self.copy().with_perm(self.perm.as_read()) }
    }
    pub fn copy_mut<'this, 'a>(&'a mut self) -> Ptr<Mut<'this, 'a, Perm::Pred>, T>
    where
        Perm: HasMut<'this>,
    {
        unsafe { self.copy().with_perm(self.perm.as_mut()) }
    }

    pub fn weak_ref<'this>(&self) -> Ptr<PointsTo<'this>, T::Erased>
    where
        Perm: IsPointsTo<'this>,
        T: EraseNestedPerms,
    {
        self.copy().drop_target_perms()
    }

    pub fn drop_target_perms(self) -> Ptr<Perm, T::Erased>
    where
        T: EraseNestedPerms,
    {
        T::erase_nested_perms(self)
    }

    #[expect(unused)]
    pub fn erase_pred<'this>(self) -> Ptr<PointsTo<'this, Perm::Access>, T>
    where
        Perm: IsPointsTo<'this>,
    {
        let (ptr, perm) = self.split();
        ptr.set_perm(perm.drop_pred())
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
    /// Read a pointer behind a pointer, taking the permissions with it as much as possible.
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
        // Safety: by the invariant of `AccessThrough`, it's ok to get that pointer out.
        let inner = self
            .deref()
            .as_ref()
            .map(|ptr| unsafe { ptr.unsafe_copy().cast_access() });
        // Safety: we're downgrading a `IsPointsTo<'a>` to a `PointsTo<'a>`, which is fine even without
        // any particular permissions on `ptr`.
        let ptr = unsafe { self.cast_ty() };
        (ptr, inner)
    }

    /// Write to a pointer behind a pointer.
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

    /// Like `write_nested_ptr` but does not write to memory. For that reason, there is an
    /// additional constraint that the virtual pointer must point to the same thing as the pointer
    /// it is replacing.
    pub fn write_nested_ptr_perm<'this, 'inner, NewInnerPerm>(
        self,
        _new: VPtr<NewInnerPerm, T>,
    ) -> Ptr<OuterPerm, Option<Ptr<NewInnerPerm, T>>>
    where
        OuterPerm: HasOwn<'this>,
        InnerPerm: IsPointsTo<'inner>,
        NewInnerPerm: IsPointsTo<'inner>,
    {
        unsafe { self.cast_ty() }
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

impl<Perm: PtrPerm, T> VPtr<Perm, T> {
    pub unsafe fn new(perm: Perm) -> Self {
        Self {
            perm,
            phantom: PhantomData,
        }
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
