#![allow(unused)]
use higher_kinded_types::ForLt as PackLt;
use std::{
    marker::PhantomData,
    ops::{Deref, DerefMut},
    ptr::NonNull,
};

// Stolen from `ghost_cell`.
type InvariantLifetime<'brand> = PhantomData<fn(&'brand ()) -> &'brand ()>;

use sep_logic_ptr::*;
mod sep_logic_ptr {
    use super::InvariantLifetime;
    use higher_kinded_types::ForLt as PackLt;
    use std::{
        fmt::Debug,
        marker::PhantomData,
        mem::MaybeUninit,
        ops::{Deref, DerefMut},
        ptr::NonNull,
    };

    /// A pointer to a `T` with permission `Perm` (either `PointsTo` or `Weak`).
    /// Note: dropping this value may leak the target. To deallocate, call `into_inner`.
    pub struct Ptr<Perm, T> {
        ptr: NonNull<T>,
        pred: PhantomData<Perm>,
    }

    impl<Perm, T> Ptr<Perm, T> {
        pub unsafe fn cast_perm<NewPerm>(self) -> Ptr<NewPerm, T> {
            Ptr {
                ptr: self.ptr,
                pred: PhantomData,
            }
        }

        pub unsafe fn cast_ty<U>(self) -> Ptr<Perm, U> {
            Ptr {
                ptr: self.ptr.cast(),
                pred: PhantomData,
            }
        }

        pub unsafe fn copy(&self) -> Self {
            Ptr {
                ptr: self.ptr,
                pred: PhantomData,
            }
        }

        pub fn alias<'this>(&self) -> Ptr<Weak<'this>, T::Target>
        where
            Perm: HasWeak<'this>,
            T: EraseNestedPerms,
        {
            unsafe { self.copy().cast_perm() }.erase_target_perms()
        }

        pub fn noperm(&self) -> Ptr<(), T> {
            unsafe { self.copy().cast_perm() }
        }

        pub fn erase_target_perms(self) -> Ptr<Perm, T::Target>
        where
            T: EraseNestedPerms,
        {
            T::erase_nested_perms(self)
        }

        /// Give a name to the hidden lifetime in a pointer permissions.
        pub fn with_lt<R>(self, f: impl for<'this> FnOnce(Ptr<Perm::Of<'this>, T>) -> R) -> R
        where
            Perm: PackLt,
        {
            f(unsafe { self.cast_perm() })
        }
        /// Give a name to the hidden lifetime in a pointer permissions.
        pub fn with_lt_ref<'a, R>(
            &'a self,
            f: impl for<'this> FnOnce(Ptr<Read<'this, 'a>, T>) -> R,
        ) -> R
        where
            Perm: PackLt,
            for<'this> Perm::Of<'this>: HasRead<'this>,
        {
            f(unsafe { self.copy().cast_perm() })
        }
        /// Give a name to the hidden lifetime in a pointer permissions.
        pub fn with_lt_mut<'a, R>(
            &'a mut self,
            f: impl for<'this> FnOnce(Ptr<Mut<'this, 'a>, T>) -> R,
        ) -> R
        where
            Perm: PackLt,
            for<'this> Perm::Of<'this>: HasMut<'this>,
        {
            f(unsafe { self.copy().cast_perm() })
        }
    }

    /// Hide the lifetime in a pointer permissions.
    pub fn pack_lt<'this, Perm: PackLt, T>(ptr: Ptr<Perm::Of<'this>, T>) -> Ptr<Perm, T> {
        unsafe { ptr.cast_perm() }
    }

    pub unsafe trait EraseNestedPerms: Sized {
        type Target;
        fn erase_nested_perms<Perm>(ptr: Ptr<Perm, Self>) -> Ptr<Perm, Self::Target> {
            unsafe { ptr.cast_ty() }
        }
    }

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
            Self {
                ptr: Box::into_non_null(Box::new(val)),
                pred: PhantomData,
            }
        }
        pub fn into_inner(self) -> T {
            // Safety: we have points-to access.
            *unsafe { Box::from_non_null(self.ptr) }
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
            Self {
                ptr: Box::into_non_null(Box::<MaybeUninit<T>>::new_uninit()).cast::<T>(),
                pred: PhantomData,
            }
        }
    }

    impl Ptr<(), ()> {
        /// Alloc a non-initialized location that can contain a pointer to itself. This
        /// self-reference will have to be hidden away before returning of course.
        pub fn new_uninit_cyclic<T: PackLt, R>(
            f: impl for<'this> FnOnce(Ptr<UninitOwned<'this>, T::Of<'this>>) -> R,
        ) -> R {
            f(Ptr {
                ptr: Box::into_non_null(Box::<MaybeUninit<T::Of<'_>>>::new_uninit())
                    .cast::<T::Of<'_>>(),
                pred: PhantomData,
            })
        }
    }

    impl<'this, T> Ptr<UninitOwned<'this>, T> {
        pub fn write(self, val: T) -> Ptr<PointsTo<'this>, T> {
            unsafe { self.ptr.write(val) };
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
            unsafe { self.ptr.as_mut() }
        }
    }
    impl<'this, Perm: HasMut<'this>, T> DerefMut for Ptr<Perm, T> {
        fn deref_mut(&mut self) -> &mut T {
            // Safety: we have at least `Mut` permission.
            unsafe { self.ptr.as_mut() }
        }
    }

    pub unsafe trait HasRead<'this> {}
    unsafe impl<'this, T: HasMut<'this>> HasRead<'this> for T {}
    unsafe impl<'this, Perm> HasRead<'this> for Read<'this, '_, Perm> {}

    impl<'this, 'a, Perm, T> Ptr<Read<'this, 'a, Perm>, T> {
        pub fn deref(&self) -> &'a T {
            // Safety: we have `Read` permission for `'a`.
            unsafe { self.ptr.as_ref() }
        }
    }
    impl<'this, Perm: HasRead<'this>, T> Deref for Ptr<Perm, T> {
        type Target = T;
        fn deref(&self) -> &T {
            // Safety: we have at least `Read` permission.
            unsafe { self.ptr.as_ref() }
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

    impl<Perm, T> Debug for Ptr<Perm, T> {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            write!(f, "{}", std::any::type_name::<Self>())
        }
    }
}

/// A predicate on a value's fields. This allows packing a predicate on a value into a predicate on
/// the pointer to such a value. This makes it possible to build inductive predicates, with
/// `pack`/`unpack` acting as constructor/destructor.
/// Safety: `Unpacked` must be the same type as `Ty` modulo predicates, and have strictly stronger
/// predicates.
unsafe trait PredOnFields<'this, Ty>: Sized {
    type Unpacked;
    /// Given a pointer with `Self` permission, turn it into a pointer to the type with permissions
    /// applied.
    fn unpack(ptr: Ptr<PointsTo<'this, Self>, Ty>) -> Ptr<PointsTo<'this>, Self::Unpacked> {
        // Safety: by the trait precondition this only changes predicates (i.e. ghost types) so
        // this is layout-compatible. Since the definition of `Self` as a predicate is the effect
        // of this function, this is definitionally a correct cast.
        unsafe { ptr.cast_perm().cast_ty() }
    }
    /// Reverse `unpack`.
    fn pack(ptr: Ptr<PointsTo<'this>, Self::Unpacked>) -> Ptr<PointsTo<'this, Self>, Ty> {
        // Safety: by the trait precondition this only changes predicates (i.e. ghost types) so
        // this is layout-compatible. Since the definition of `Self` as a predicate is the effect
        // of this function, this is definitionally a correct cast.
        unsafe { ptr.cast_perm().cast_ty() }
    }
}

/// `Prev` and `Next` are permissions
// The point of generic permissions is to make sense of the general pattern of moving permissions
// for a single field around. A derive would provide the helper functions to manage the permissions
// of each field.
pub struct Node<Prev = (), Next = ()> {
    val: usize,
    prev: Option<Ptr<Prev, Node>>,
    next: Option<Ptr<Next, Node>>,
}

unsafe impl<Prev, Next> EraseNestedPerms for Node<Prev, Next> {
    type Target = Node;
}

/// Writes the given pointer into `ptr.next`.
fn write_next<'this, Perm: HasPointsTo<'this>, Prev, OldNext, Next>(
    mut ptr: Ptr<Perm, Node<Prev, OldNext>>,
    next: Ptr<Next, Node>,
) -> (Ptr<Perm, Node<Prev, Next>>, Option<Ptr<OldNext, Node>>) {
    let old_next = ptr.next.as_ref().map(|next| unsafe { next.copy() });
    ptr.next = Some(unsafe { next.cast_perm() });
    let new_ptr = unsafe { ptr.cast_ty() };
    (new_ptr, old_next)
}
/// Writes the given pointer into `ptr.prev`.
fn write_prev<'this, Perm: HasPointsTo<'this>, OldPrev, Prev, Next>(
    mut ptr: Ptr<Perm, Node<OldPrev, Next>>,
    prev: Ptr<Prev, Node>,
) -> (Ptr<Perm, Node<Prev, Next>>, Option<Ptr<OldPrev, Node>>) {
    let old_prev = ptr.prev.as_ref().map(|prev| unsafe { prev.copy() });
    ptr.prev = Some(unsafe { prev.cast_perm() });
    let new_ptr = unsafe { ptr.cast_ty() };
    (new_ptr, old_prev)
}
/// If we have a points-to to a `Node`, we can extract a points-to from one of its fields, leaving
/// a `Weak` permission in its place.
fn extract_next_ownership<'this, 'next, Prev, Next>(
    ptr: Ptr<PointsTo<'this>, Node<Prev, PointsTo<'next, Next>>>,
) -> (
    Ptr<PointsTo<'this>, Node<Prev, Weak<'next>>>,
    Option<Ptr<PointsTo<'next, Next>, Node>>,
) {
    // Safety: we're copying a `PointsTo`, which is fine because we remove it from the type on the
    // next line.
    let next_ptr = unsafe { ptr.next.as_ref().map(|next| next.copy()) };
    // Safety: we're casting between types that differ only in ghost types, which preserves layout.
    // We're downgrading a `PointsTo` to the corresponding `Weak` permission, which is
    // allowed.
    let ptr = unsafe { ptr.cast_ty() };
    (ptr, next_ptr)
}
/// Reverse of `extract_next_ownership`. Does not touch memory, only moves ghost ownership around.
fn insert_next_ownership<'this, 'next, Perm: HasPointsTo<'this>, Prev, Next>(
    ptr: Ptr<Perm, Node<Prev, Weak<'next>>>,
    _next: Ptr<PointsTo<'next, Next>, Node>,
) -> Ptr<Perm, Node<Prev, PointsTo<'next, Next>>> {
    unsafe { ptr.cast_ty() }
}
/// Like of `extract_next_ownership`.
fn extract_prev_ownership<'this, 'prev, Prev, Next>(
    ptr: Ptr<PointsTo<'this>, Node<PointsTo<'prev, Prev>, Next>>,
) -> (
    Ptr<PointsTo<'this>, Node<Weak<'prev>, Next>>,
    Option<Ptr<PointsTo<'prev, Prev>, Node>>,
) {
    // Safety: we're copying a `PointsTo`, which is fine because we remove it from the type on the
    // next line.
    let next_ptr = unsafe { ptr.prev.as_ref().map(|prev| prev.copy()) };
    // Safety: we're casting between types that differ only in ghost types, which preserves layout.
    // We're downgrading a `PointsTo` to the corresponding `Weak` permission, which is
    // allowed.
    let ptr = unsafe { ptr.cast_ty() };
    (ptr, next_ptr)
}
/// Reverse of `extract_prev_ownership`.
fn insert_prev_ownership<'this, 'prev, Prev, Next>(
    ptr: Ptr<PointsTo<'this>, Node<Weak<'prev>, Next>>,
    _prev: Ptr<PointsTo<'prev, Prev>, Node>,
) -> Ptr<PointsTo<'this>, Node<PointsTo<'prev, Prev>, Next>> {
    unsafe { ptr.cast_ty() }
}
/// Give a name to the hidden lifetime in the permission of the `next` field.
fn with_next_lt<'this, Perm: HasPointsTo<'this>, Prev, Next: PackLt, R>(
    ptr: Ptr<Perm, Node<Prev, Next>>,
    f: impl for<'next> FnOnce(Ptr<Perm, Node<Prev, Next::Of<'next>>>) -> R,
) -> R {
    f(unsafe { ptr.cast_ty() })
}
/// Hide the name of the lifetime in the permission of the `next` field.
fn hide_next_lt<'this, 'next, Perm: HasPointsTo<'this>, Prev, Next: PackLt>(
    ptr: Ptr<Perm, Node<Prev, Next::Of<'next>>>,
) -> Ptr<Perm, Node<Prev, Next>> {
    unsafe { ptr.cast_ty() }
}
/// Give a name to the hidden lifetime in the permission of the `prev` field.
fn with_prev_lt<'this, Perm: HasPointsTo<'this>, Prev: PackLt, Next, R>(
    ptr: Ptr<Perm, Node<Prev, Next>>,
    f: impl for<'prev> FnOnce(Ptr<Perm, Node<Prev::Of<'prev>, Next>>) -> R,
) -> R {
    f(unsafe { ptr.cast_ty() })
}
/// Hide the name of the lifetime in the permission of the `prev` field.
fn hide_prev_lt<'this, 'prev, Perm: HasPointsTo<'this>, Prev: PackLt, Next>(
    ptr: Ptr<Perm, Node<Prev::Of<'prev>, Next>>,
) -> Ptr<Perm, Node<Prev, Next>> {
    unsafe { ptr.cast_ty() }
}

/// A linked list with backward pointers, with ownership that follows the forward pointers.
pub struct NodeStateFwd<'this, 'prev>(InvariantLifetime<'this>, InvariantLifetime<'prev>);
unsafe impl<'this, 'prev> PredOnFields<'this, Node> for NodeStateFwd<'this, 'prev> {
    type Unpacked = Node<Weak<'prev>, PackLt!(PointsTo<'_, NodeStateFwd<'_, 'this>>)>;
}

/// Like `NodeStateFwd` except flipping the fields of `Node` (the "forward" pointer is in the
/// `Node.prev` field instead).
pub struct NodeStateBwd<'this, 'next>(InvariantLifetime<'this>, InvariantLifetime<'next>);
unsafe impl<'this, 'next> PredOnFields<'this, Node> for NodeStateBwd<'this, 'next> {
    type Unpacked = Node<PackLt!(PointsTo<'_, NodeStateBwd<'_, 'this>>), Weak<'next>>;
}

/// A Node whose `prev` and `next` fields are each a forward-owned linked list with back-edges.
/// This functions as a doubly-linked-list zipper.
pub struct NodeStateCentral<'this>(InvariantLifetime<'this>);
unsafe impl<'this> PredOnFields<'this, Node> for NodeStateCentral<'this> {
    type Unpacked = Node<
        PackLt!(PointsTo<'_, NodeStateBwd<'_, 'this>>),
        PackLt!(PointsTo<'_, NodeStateFwd<'_, 'this>>),
    >;
}

#[derive(Debug)]
struct ListCursor(Ptr<PackLt!(PointsTo<'_, NodeStateCentral<'_>>), Node>);

impl ListCursor {
    pub fn new(val: usize) -> Self {
        Ptr::new_uninit_cyclic::<
            PackLt!(<NodeStateCentral<'_> as PredOnFields<'_, Node>>::Unpacked),
            _,
        >(|ptr| {
            let ptr = ptr.write(Node {
                val,
                prev: None,
                next: None,
            });
            let ptr = NodeStateCentral::pack(ptr);
            Self(pack_lt(ptr))
        })
    }

    fn val(&self) -> &usize {
        self.0.with_lt_ref(|ptr| &ptr.deref().val)
    }
    fn val_mut(&mut self) -> &mut usize {
        self.0.with_lt_mut(|ptr| &mut ptr.into_deref_mut().val)
    }

    fn insert_after(self, val: usize) -> Self {
        // self: Ptr<PackLt!(PointsTo<'_, NodeStateCentral<'_>>), Node>
        // Expand the lifetime
        self.0.with_lt(|ptr| {
            // ptr: Ptr<PointsTo<'this, NodeStateCentral<'this>>, Node>
            // Expand the permissions to the fields of `Node`
            let ptr = NodeStateCentral::unpack(ptr);
            // Expand the lifetime
            with_next_lt(ptr, |ptr| {
                // ptr: Ptr<
                //     PointsTo<'this>,
                //     Node<
                //         PackLt!(PointsTo<'_, NodeStateBwd<'_, 'this>>),
                //         PointsTo<'next, NodeStateFwd<'next, 'this>>,
                //     >,
                // >
                // Extract the ownership in `next` (and get a copy of that pointer).
                let (ptr, next) = extract_next_ownership(ptr);
                // We need to allocate a new node at address `'new` that can have `'new` in
                // its type, hence the need for a closure like this. We must pack the `'new`
                // brand before returning.
                type ToAlloc<'prev> =
                    PackLt!(<NodeStateFwd<'_, 'prev> as PredOnFields<'_, Node>>::Unpacked);
                let ptr = Ptr::new_uninit_cyclic::<ToAlloc<'_>, _>(|new| {
                    // Update `next.prev` to point to `new`.
                    let next = next.map(|next| {
                        let next = NodeStateFwd::unpack(next);
                        let (next, _) = write_prev(next, new.alias());
                        let next = NodeStateFwd::pack(next);
                        pack_lt(next)
                    });
                    // Allocate a new node whose `prev` field is `ptr` and `next` field is
                    // `next`.
                    let new = NodeStateFwd::pack(new.write(Node {
                        val,
                        prev: Some(ptr.alias()),
                        next,
                    }));
                    // Update `ptr.next`.
                    let (ptr, _) = write_next(ptr, new);
                    // Pack the `'new` lifetime
                    hide_next_lt::<_, PackLt!(<'a> = PointsTo<'a, NodeStateBwd<'a, '_>>), _>(ptr)
                });
                // Unexpand permissions
                let ptr = NodeStateCentral::pack(ptr);
                // ptr: Ptr<PointsTo<'next, NodeStateCentral<'next>>, Node>
                // Pack lifetime
                let ptr = pack_lt(ptr);
                // ptr: Ptr<PackLt!(PointsTo<'_, NodeStateCentral<'_>>), Node>
                Self(ptr)
            })
        })
    }

    /// Advance the cursor. Returns `Err(self)` if the cursor could not be advanced.
    fn next(self) -> Result<Self, Self> {
        if self.0.with_lt_ref(|ptr| ptr.next.is_none()) {
            return Err(self);
        };
        // self: Ptr<PackLt!(PointsTo<'_, NodeStateCentral<'_>>), Node>
        // Expand the lifetime
        self.0.with_lt(|ptr| {
            // ptr: Ptr<PointsTo<'this, NodeStateCentral<'this>>, Node>
            // Expand the permissions to the fields of `Node`
            let ptr = NodeStateCentral::unpack(ptr);
            // ptr: Ptr<
            //     PointsTo<'this>,
            //     Node<
            //         PackLt!(PointsTo<'_, NodeStateBwd<'_, 'this>>),
            //         PackLt!(PointsTo<'_, NodeStateFwd<'_, 'this>>),
            //     >,
            // >
            // Expand the lifetime
            with_next_lt(ptr, |ptr| {
                // ptr: Ptr<
                //     PointsTo<'this>,
                //     Node<
                //         PackLt!(PointsTo<'_, NodeStateBwd<'_, 'this>>),
                //         PointsTo<'next, NodeStateFwd<'next, 'this>>,
                //     >,
                // >
                // Extract the ownership in `next` (and get a copy of that pointer).
                let (ptr, next) = extract_next_ownership(ptr);
                // `unwrap` is ok because we checked earlier.
                let next = next.unwrap();
                // ptr: Ptr<
                //     PointsTo<'this>,
                //     Node<
                //         PackLt!(PointsTo<'_, NodeStateBwd<'_, 'this>>),
                //         Weak<'next>,
                //     >,
                // >
                // next: Ptr<PointsTo<'next, NodeStateFwd<'next, 'this>>, Node>
                // Unexpand the permissions
                let ptr = NodeStateBwd::pack(ptr);
                // ptr: Ptr<PointsTo<'this, NodeStateBwd<'this, 'next>>, Node>
                // Expand the permissions
                let next = NodeStateFwd::unpack(next);
                // next: Ptr<PointsTo<'next>,
                //    Node<
                //      Weak<'this>,
                //      PackLt!(PointsTo<'_, NodeStateFwd<'_, 'next>>),
                //    >,
                // >
                // Insert ownership
                let ptr = insert_prev_ownership(next, ptr);
                // ptr: Ptr<PointsTo<'next>,
                //    Node<
                //      PointsTo<'this, NodeStateBwd<'this, 'next>>,
                //      PackLt!(PointsTo<'_, NodeStateFwd<'_, 'next>>),
                //    >>
                // >
                // Pack lifetime
                let ptr =
                    hide_prev_lt::<_, PackLt!(<'a> = PointsTo<'a, NodeStateBwd<'a, '_>>), _>(ptr);
                // ptr: Ptr<PointsTo<'next>,
                //    Node<
                //      PackLt!(PointsTo<'_, NodeStateBwd<'_, 'next>>),
                //      PackLt!(PointsTo<'_, NodeStateFwd<'_, 'next>>),
                //    >>
                // >
                // Unexpand permissions
                let ptr = NodeStateCentral::pack(ptr);
                // ptr: Ptr<PointsTo<'next, NodeStateCentral<'next>>, Node>
                // Pack lifetime
                let ptr = pack_lt(ptr);
                // ptr: Ptr<PackLt!(PointsTo<'_, NodeStateCentral<'_>>), Node>
                Ok(Self(ptr))
            })
        })
    }

    /// Move the cursor backwards. Returns `Err(self)` if the cursor could not be moved.
    fn prev(self) -> Result<Self, Self> {
        if self.0.with_lt_ref(|ptr| ptr.prev.is_none()) {
            return Err(self);
        };
        // Expand the lifetime
        self.0.with_lt(|ptr| {
            // Expand the permissions to the fields of `Node`
            let ptr = NodeStateCentral::unpack(ptr);
            // Expand the lifetime
            with_prev_lt(ptr, |ptr| {
                // Extract the ownership in `prev` (and get a copy of that pointer).
                let (ptr, prev) = extract_prev_ownership(ptr);
                // `unwrap` is ok because we checked earlier.
                let prev = prev.unwrap();
                // Unexpand the permissions
                let ptr = NodeStateFwd::pack(ptr);
                // Expand the permissions
                let prev = NodeStateBwd::unpack(prev);
                // Insert ownership
                let ptr = insert_next_ownership(prev, ptr);
                // Pack lifetime
                let ptr =
                    hide_next_lt::<_, _, PackLt!(<'a> = PointsTo<'a, NodeStateFwd<'a, '_>>)>(ptr);
                // Unexpand permissions
                let ptr = NodeStateCentral::pack(ptr);
                // Pack lifetime
                let ptr = pack_lt(ptr);
                Ok(Self(ptr))
            })
        })
    }
}

pub fn main() {
    let cursor = ListCursor::new(0)
        .insert_after(1)
        .next()
        .unwrap()
        .insert_after(2)
        .prev()
        .unwrap();
    println!("{}", cursor.val());
    let cursor = cursor.next().unwrap();
    println!("{}", cursor.val());
    let cursor = cursor.next().unwrap();
    println!("{}", cursor.val());
    let cursor = cursor.prev().unwrap();
    println!("{}", cursor.val());
    let cursor = cursor.prev().unwrap();
    println!("{}", cursor.val());
    // TODO: drop
}
