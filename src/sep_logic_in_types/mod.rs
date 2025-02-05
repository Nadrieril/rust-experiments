#![allow(unused)]
use higher_kinded_types::ForLt as PackLt;
use std::{
    marker::PhantomData,
    ops::{Deref, DerefMut},
    ptr::NonNull,
};

mod permissions;
mod ptr;
use permissions::*;
use ptr::*;

/// `Prev` and `Next` are permissions
// The permissions are in generics to be able to move permissions around easily. A derive could in
// principle provide most of the helper functions to manage the permissions of each field, removing
// the need for users to write unsafe code themselves.
pub struct Node<Prev = (), Next = ()> {
    val: usize,
    prev: Option<Ptr<Prev, Node>>,
    next: Option<Ptr<Next, Node>>,
}

/// Helpers to manipulate permissions in `Node`. This should be made more abstract to clarify the
/// `unsafe` uses. Ideally a user would have to write none of that.
mod node_helpers {
    use super::permissions::*;
    use super::ptr::*;
    use super::Node;
    use higher_kinded_types::ForLt as PackLt;
    use std::{
        marker::PhantomData,
        ops::{Deref, DerefMut},
        ptr::NonNull,
    };

    unsafe impl<Prev, Next> EraseNestedPerms for Node<Prev, Next> {
        type Target = Node;
    }

    /// Writes the given pointer into `ptr.next`.
    pub fn write_next<'this, Perm: HasPointsTo<'this>, Prev, OldNext, Next>(
        mut ptr: Ptr<Perm, Node<Prev, OldNext>>,
        next: Ptr<Next, Node>,
    ) -> (Ptr<Perm, Node<Prev, Next>>, Option<Ptr<OldNext, Node>>) {
        let old_next = ptr.next.as_ref().map(|next| unsafe { next.copy() });
        ptr.next = Some(unsafe { next.cast_perm() });
        let new_ptr = unsafe { ptr.cast_ty() };
        (new_ptr, old_next)
    }
    /// Writes the given pointer into `ptr.prev`.
    pub fn write_prev<'this, Perm: HasPointsTo<'this>, OldPrev, Prev, Next>(
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
    pub fn extract_next_ownership<'this, 'next, Prev, Next>(
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
    pub fn insert_next_ownership<'this, 'next, Perm: HasPointsTo<'this>, Prev, Next>(
        ptr: Ptr<Perm, Node<Prev, Weak<'next>>>,
        _next: Ptr<PointsTo<'next, Next>, Node>,
    ) -> Ptr<Perm, Node<Prev, PointsTo<'next, Next>>> {
        unsafe { ptr.cast_ty() }
    }
    /// Like of `extract_next_ownership`.
    pub fn extract_prev_ownership<'this, 'prev, Prev, Next>(
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
    pub fn insert_prev_ownership<'this, 'prev, Prev, Next>(
        ptr: Ptr<PointsTo<'this>, Node<Weak<'prev>, Next>>,
        _prev: Ptr<PointsTo<'prev, Prev>, Node>,
    ) -> Ptr<PointsTo<'this>, Node<PointsTo<'prev, Prev>, Next>> {
        unsafe { ptr.cast_ty() }
    }
    /// Give a name to the hidden lifetime in the permission of the `next` field.
    pub fn with_next_lt<'this, Perm: HasPointsTo<'this>, Prev, Next: PackLt, R>(
        ptr: Ptr<Perm, Node<Prev, Next>>,
        f: impl for<'next> FnOnce(Ptr<Perm, Node<Prev, Next::Of<'next>>>) -> R,
    ) -> R {
        f(unsafe { ptr.cast_ty() })
    }
    /// Hide the name of the lifetime in the permission of the `next` field.
    pub fn hide_next_lt<'this, 'next, Perm: HasPointsTo<'this>, Prev, Next: PackLt>(
        ptr: Ptr<Perm, Node<Prev, Next::Of<'next>>>,
    ) -> Ptr<Perm, Node<Prev, Next>> {
        unsafe { ptr.cast_ty() }
    }
    /// Give a name to the hidden lifetime in the permission of the `prev` field.
    pub fn with_prev_lt<'this, Perm: HasPointsTo<'this>, Prev: PackLt, Next, R>(
        ptr: Ptr<Perm, Node<Prev, Next>>,
        f: impl for<'prev> FnOnce(Ptr<Perm, Node<Prev::Of<'prev>, Next>>) -> R,
    ) -> R {
        f(unsafe { ptr.cast_ty() })
    }
    /// Hide the name of the lifetime in the permission of the `prev` field.
    pub fn hide_prev_lt<'this, 'prev, Perm: HasPointsTo<'this>, Prev: PackLt, Next>(
        ptr: Ptr<Perm, Node<Prev::Of<'prev>, Next>>,
    ) -> Ptr<Perm, Node<Prev, Next>> {
        unsafe { ptr.cast_ty() }
    }
}

/// A linked list with backward pointers, with ownership that follows the forward pointers.
pub struct NodeStateFwd<'this, 'prev>(InvariantLifetime<'this>, InvariantLifetime<'prev>);
impl<'this, 'prev> PredOnFields<'this, Node> for NodeStateFwd<'this, 'prev> {
    type Unpacked = Node<Weak<'prev>, PackLt!(PointsTo<'_, NodeStateFwd<'_, 'this>>)>;
}

/// Like `NodeStateFwd` except flipping the fields of `Node` (the "forward" pointer is in the
/// `Node.prev` field instead).
pub struct NodeStateBwd<'this, 'next>(InvariantLifetime<'this>, InvariantLifetime<'next>);
impl<'this, 'next> PredOnFields<'this, Node> for NodeStateBwd<'this, 'next> {
    type Unpacked = Node<PackLt!(PointsTo<'_, NodeStateBwd<'_, 'this>>), Weak<'next>>;
}

/// A Node whose `prev` and `next` fields are each a forward-owned linked list with back-edges.
/// This functions as a doubly-linked-list zipper.
pub struct NodeStateCentral<'this>(InvariantLifetime<'this>);
impl<'this> PredOnFields<'this, Node> for NodeStateCentral<'this> {
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
            node_helpers::with_next_lt(ptr, |ptr| {
                // ptr: Ptr<
                //     PointsTo<'this>,
                //     Node<
                //         PackLt!(PointsTo<'_, NodeStateBwd<'_, 'this>>),
                //         PointsTo<'next, NodeStateFwd<'next, 'this>>,
                //     >,
                // >
                // Extract the ownership in `next` (and get a copy of that pointer).
                let (ptr, next) = node_helpers::extract_next_ownership(ptr);
                // We need to allocate a new node at address `'new` that can have `'new` in
                // its type, hence the need for a closure like this. We must pack the `'new`
                // brand before returning.
                type ToAlloc<'prev> =
                    PackLt!(<NodeStateFwd<'_, 'prev> as PredOnFields<'_, Node>>::Unpacked);
                let ptr = Ptr::new_uninit_cyclic::<ToAlloc<'_>, _>(|new| {
                    // Update `next.prev` to point to `new`.
                    let next = next.map(|next| {
                        let next = NodeStateFwd::unpack(next);
                        let (next, _) = node_helpers::write_prev(next, new.alias());
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
                    let (ptr, _) = node_helpers::write_next(ptr, new);
                    // Pack the `'new` lifetime
                    node_helpers::hide_next_lt::<
                        _,
                        PackLt!(<'a> = PointsTo<'a, NodeStateBwd<'a, '_>>),
                        _,
                    >(ptr)
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
            node_helpers::with_next_lt(ptr, |ptr| {
                // ptr: Ptr<
                //     PointsTo<'this>,
                //     Node<
                //         PackLt!(PointsTo<'_, NodeStateBwd<'_, 'this>>),
                //         PointsTo<'next, NodeStateFwd<'next, 'this>>,
                //     >,
                // >
                // Extract the ownership in `next` (and get a copy of that pointer).
                let (ptr, next) = node_helpers::extract_next_ownership(ptr);
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
                let ptr = node_helpers::insert_prev_ownership(next, ptr);
                // ptr: Ptr<PointsTo<'next>,
                //    Node<
                //      PointsTo<'this, NodeStateBwd<'this, 'next>>,
                //      PackLt!(PointsTo<'_, NodeStateFwd<'_, 'next>>),
                //    >>
                // >
                // Pack lifetime
                let ptr = node_helpers::hide_prev_lt::<
                    _,
                    PackLt!(<'a> = PointsTo<'a, NodeStateBwd<'a, '_>>),
                    _,
                >(ptr);
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
            node_helpers::with_prev_lt(ptr, |ptr| {
                // Extract the ownership in `prev` (and get a copy of that pointer).
                let (ptr, prev) = node_helpers::extract_prev_ownership(ptr);
                // `unwrap` is ok because we checked earlier.
                let prev = prev.unwrap();
                // Unexpand the permissions
                let ptr = NodeStateFwd::pack(ptr);
                // Expand the permissions
                let prev = NodeStateBwd::unpack(prev);
                // Insert ownership
                let ptr = node_helpers::insert_next_ownership(prev, ptr);
                // Pack lifetime
                let ptr = node_helpers::hide_next_lt::<
                    _,
                    _,
                    PackLt!(<'a> = PointsTo<'a, NodeStateFwd<'a, '_>>),
                >(ptr);
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
    // TODO: iter_mut
}
