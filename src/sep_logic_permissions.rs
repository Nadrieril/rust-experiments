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
        marker::PhantomData,
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

        // TODO: Shouldn't have an unbound lifetime.
        pub fn alias___<'a>(&self) -> Ptr<Weak<'a>, T> {
            unsafe { self.copy().cast_perm() }
        }

        /// Give a name to the hidden lifetime in a pointer permissions.
        pub fn with_lt<R>(self, f: impl for<'this> FnOnce(Ptr<Perm::Of<'this>, T>) -> R) -> R
        where
            Perm: PackLt,
        {
            f(unsafe { self.cast_perm() })
        }
    }

    /// Hide the lifetime in a pointer permissions.
    pub fn pack_lt<'this, Perm: PackLt, T>(ptr: Ptr<Perm::Of<'this>, T>) -> Ptr<Perm, T> {
        unsafe { ptr.cast_perm() }
    }

    /// The separation logic points-to (unique ownership), with a predicate on the pointed-to value.
    /// The `'this` lifetime brand denotes the pointer address. This can be paired with some `Weak`
    /// pointers with the same brand to statically track that they have the same address.
    pub struct PointsTo<'this, Pred = ()>(PhantomData<Pred>, InvariantLifetime<'this>);

    /// Read/write access, with a predicate on the pointed-to value.
    pub struct Mut<'this, Pred = ()>(PhantomData<Pred>, InvariantLifetime<'this>);

    /// Read access, with a predicate on the pointed-to value.
    pub struct Read<'this, Pred = ()>(PhantomData<Pred>, InvariantLifetime<'this>);

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

    unsafe trait HasPointsTo {}
    unsafe impl<'this, Perm> HasPointsTo for PointsTo<'this, Perm> {}

    unsafe trait HasMut {}
    unsafe impl<T: HasPointsTo> HasMut for T {}
    unsafe impl<'this, Perm> HasMut for Mut<'this, Perm> {}

    unsafe trait HasRead {}
    unsafe impl<T: HasMut> HasRead for T {}
    unsafe impl<'this, Perm> HasRead for Read<'this, Perm> {}

    impl<'this, Perm: HasRead, T> Deref for Ptr<Perm, T> {
        type Target = T;
        fn deref(&self) -> &T {
            // Safety: we have at least `Read` permission.
            unsafe { self.ptr.as_ref() }
        }
    }
    impl<'this, Perm: HasMut, T> DerefMut for Ptr<Perm, T> {
        fn deref_mut(&mut self) -> &mut T {
            // Safety: we have at least `Mut` permission.
            unsafe { self.ptr.as_mut() }
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
fn with_next_lt<'this, Prev, Next: PackLt, R>(
    ptr: Ptr<PointsTo<'this>, Node<Prev, Next>>,
    f: impl for<'next> FnOnce(Ptr<PointsTo<'this>, Node<Prev, Next::Of<'next>>>) -> R,
) -> R {
    f(unsafe { ptr.cast_ty() })
}
/// Hide the name of the lifetime in the permission of the `next` field.
fn hide_next_lt<'this, 'next, Prev, Next: PackLt, R>(
    ptr: Ptr<PointsTo<'this>, Node<Prev, Next::Of<'next>>>,
) -> Ptr<PointsTo<'this>, Node<Prev, Next>> {
    unsafe { ptr.cast_ty() }
}
/// Hide the name of the lifetime in the permission of the `prev` field.
fn hide_prev_lt<'this, 'prev, Prev: PackLt, Next>(
    ptr: Ptr<PointsTo<'this>, Node<Prev::Of<'prev>, Next>>,
) -> Ptr<PointsTo<'this>, Node<Prev, Next>> {
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

type ListCursor = Ptr<PackLt!(PointsTo<'_, NodeStateCentral<'_>>), Node>;

// TODO: handle null pointers
// TODO: alloc/dealloc ptrs
// TODO: create a simple list
impl ListCursor {
    // fn val(&self) -> &usize {
    //     self.
    // }
    /// Advance the cursor. Returns `Err(self)` if the cursor could not be advanced.
    fn next(self) -> Result<Self, Self> {
        // self: Ptr<PackLt!(PointsTo<'_, NodeStateCentral<'_>>), Node>
        // Expand the lifetime
        self.with_lt(|ptr| {
            // ptr: Ptr<PointsTo<'this, NodeStateCentral<'this>>, Node>
            if ptr.next.is_none() {
                let ptr = pack_lt(ptr);
                return Err(ptr);
            };
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
                    hide_prev_lt::<PackLt!(<'a> = PointsTo<'a, NodeStateBwd<'a, '_>>), _>(ptr);
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
                Ok(ptr)
            })
        })
    }
}

fn main() {
    let node1: Ptr<_, Node> = Ptr::new(Node {
        val: 0,
        prev: None,
        next: None,
    });
    let node2: Ptr<_, Node> = Ptr::new(Node {
        val: 1,
        prev: None,
        next: None,
    });
    let (node1, node2) = node1.with_lt(|node1| {
        node2.with_lt(|node2| {
            let node1_alias = node1.alias___();
            let node2_alias = node2.alias___();
            let mut node1: Ptr<_, Node<(), Weak<'_>>> = unsafe { node1.cast_ty() };
            let mut node2: Ptr<_, Node<Weak<'_>, ()>> = unsafe { node2.cast_ty() };
            node1.next = Some(node2_alias);
            node2.prev = Some(node1_alias);
            (pack_lt(node1), pack_lt(node2))
        })
    });
    // TODO: how to turn into a list??
    let _ = node1.into_inner();
    let _ = node2.into_inner();
}
