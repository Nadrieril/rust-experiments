#![allow(unused)]
use higher_kinded_types::ForLt as PackLt;
use std::{
    marker::PhantomData,
    ops::{Deref, DerefMut},
    ptr::NonNull,
};

mod fields;
mod permissions;
mod ptr;
use fields::*;
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

// All of the unsafe for `Node` is in these three declarations.
unsafe impl<Prev, Next> EraseNestedPerms for Node<Prev, Next> {
    type Erased = Node;
}

unsafe impl<Prev, Next> HasPermField<0, Prev> for Node<Prev, Next> {
    type FieldTy = Node;
    type ChangePerm<NewPrev> = Node<NewPrev, Next>;
    fn field_ref(&self) -> &Option<Ptr<Prev, Self::FieldTy>> {
        &self.prev
    }
    fn field_mut(&mut self) -> &mut Option<Ptr<Prev, Self::FieldTy>> {
        &mut self.prev
    }
}
unsafe impl<Prev, Next> HasPermField<1, Next> for Node<Prev, Next> {
    type FieldTy = Node;
    type ChangePerm<NewNext> = Node<Prev, NewNext>;
    fn field_ref(&self) -> &Option<Ptr<Next, Self::FieldTy>> {
        &self.next
    }
    fn field_mut(&mut self) -> &mut Option<Ptr<Next, Self::FieldTy>> {
        &mut self.next
    }
}

/// Helpers that wrap `HasPermField` methods.
mod node_helpers {
    use super::fields::*;
    use super::permissions::*;
    use super::ptr::*;
    use super::Node;
    use higher_kinded_types::ForLt as PackLt;
    use std::{
        marker::PhantomData,
        ops::{Deref, DerefMut},
        ptr::NonNull,
    };

    /// Writes the given pointer into `ptr.next`.
    pub fn write_next<'this, Perm: HasMut<'this>, Prev, OldNext, Next>(
        mut ptr: Ptr<Perm, Node<Prev, OldNext>>,
        next: Ptr<Next, Node>,
    ) -> (Ptr<Perm, Node<Prev, Next>>, Option<Ptr<OldNext, Node>>) {
        Node::write_field(ptr, next)
    }
    /// Writes the given pointer into `ptr.prev`.
    pub fn write_prev<'this, Perm: HasMut<'this>, OldPrev, Prev, Next>(
        mut ptr: Ptr<Perm, Node<OldPrev, Next>>,
        prev: Ptr<Prev, Node>,
    ) -> (Ptr<Perm, Node<Prev, Next>>, Option<Ptr<OldPrev, Node>>) {
        <Node<_, _> as HasPermField<0, _>>::write_field(ptr, prev)
    }

    /// Like `write_next` but only moves permissions around. Does not write to memory.
    pub fn write_next_permission<'this, 'next, Perm, Prev, OldNext, Next>(
        ptr: Ptr<Perm, Node<Prev, OldNext>>,
        next: Ptr<Next, Node>,
    ) -> (Ptr<Perm, Node<Prev, Next>>, Option<Ptr<OldNext, Node>>)
    where
        Perm: HasMut<'this>,
        OldNext: HasWeak<'next>,
        Next: HasWeak<'next>,
    {
        <Node<_, _> as HasPermField<1, _>>::write_field_permission(ptr, next)
    }
    /// Like `write_prev` but only moves permissions around. Does not write to memory.
    pub fn write_prev_permission<'this, 'prev, Perm, OldPrev, Prev, Next>(
        ptr: Ptr<Perm, Node<OldPrev, Next>>,
        prev: Ptr<Prev, Node>,
    ) -> (Ptr<Perm, Node<Prev, Next>>, Option<Ptr<OldPrev, Node>>)
    where
        Perm: HasMut<'this>,
        OldPrev: HasWeak<'prev>,
        Prev: HasWeak<'prev>,
    {
        <Node<_, _> as HasPermField<0, _>>::write_field_permission(ptr, prev)
    }

    /// Downgrade the permission in `next`.
    pub fn downgrade_next_ownership<'this, 'next, Perm, Prev, Next>(
        ptr: Ptr<Perm, Node<Prev, Next>>,
    ) -> Ptr<Perm, Node<Prev, Weak<'next>>>
    where
        Next: HasWeak<'next>,
    {
        <Node<_, _> as HasPermField<1, _>>::downgrade_field_permission(ptr)
    }
    /// Downgrade the permission in `prev`.
    pub fn downgrade_prev_ownership<'this, 'next, Perm, Prev, Next>(
        ptr: Ptr<Perm, Node<Prev, Next>>,
    ) -> Ptr<Perm, Node<Weak<'next>, Next>>
    where
        Prev: HasWeak<'next>,
    {
        <Node<_, _> as HasPermField<0, _>>::downgrade_field_permission(ptr)
    }

    /// Give a name to the hidden lifetime in the permission of the `next` field.
    pub fn unpack_next_lt<'this, Perm, Prev, Next: PackLt, R>(
        ptr: Ptr<Perm, Node<Prev, Next>>,
        f: impl for<'next> FnOnce(Ptr<Perm, Node<Prev, Next::Of<'next>>>) -> R,
    ) -> R {
        <Node<_, _> as HasPermField<1, _>>::unpack_field_lt(ptr, f)
    }
    /// Hide the name of the lifetime in the permission of the `next` field.
    pub fn pack_next_lt<'this, 'next, Perm, Prev, Next: PackLt>(
        ptr: Ptr<Perm, Node<Prev, Next::Of<'next>>>,
    ) -> Ptr<Perm, Node<Prev, Next>> {
        <Node<_, _> as HasPermField<1, _>>::pack_field_lt(ptr)
    }
    /// Give a name to the hidden lifetime in the permission of the `prev` field.
    pub fn unpack_prev_lt<'this, Perm, Prev: PackLt, Next, R>(
        ptr: Ptr<Perm, Node<Prev, Next>>,
        f: impl for<'prev> FnOnce(Ptr<Perm, Node<Prev::Of<'prev>, Next>>) -> R,
    ) -> R {
        <Node<_, _> as HasPermField<0, _>>::unpack_field_lt(ptr, f)
    }
    /// Hide the name of the lifetime in the permission of the `prev` field.
    pub fn pack_prev_lt<'this, 'prev, Perm, Prev: PackLt, Next>(
        ptr: Ptr<Perm, Node<Prev::Of<'prev>, Next>>,
    ) -> Ptr<Perm, Node<Prev, Next>> {
        <Node<_, _> as HasPermField<0, _>>::pack_field_lt(ptr)
    }
}

/// A linked list with backward pointers, with ownership that follows the forward pointers.
pub struct NodeStateFwd<'this, 'prev>(InvariantLifetime<'this>, InvariantLifetime<'prev>);
impl<'this, 'prev> PackedPredicate<'this, Node> for NodeStateFwd<'this, 'prev> {
    type Unpacked = Node<Weak<'prev>, PackLt!(PointsTo<'_, NodeStateFwd<'_, 'this>>)>;
}

/// Like `NodeStateFwd` except flipping the fields of `Node` (the "forward" pointer is in the
/// `Node.prev` field instead).
pub struct NodeStateBwd<'this, 'next>(InvariantLifetime<'this>, InvariantLifetime<'next>);
impl<'this, 'next> PackedPredicate<'this, Node> for NodeStateBwd<'this, 'next> {
    type Unpacked = Node<PackLt!(PointsTo<'_, NodeStateBwd<'_, 'this>>), Weak<'next>>;
}

/// A Node whose `prev` and `next` fields are each a forward-owned linked list with back-edges.
/// This functions as a doubly-linked-list zipper.
pub struct NodeStateCentral<'this>(InvariantLifetime<'this>);
impl<'this> PackedPredicate<'this, Node> for NodeStateCentral<'this> {
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
            PackLt!(<NodeStateCentral<'_> as PackedPredicate<'_, Node>>::Unpacked),
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
        self.0.unpack_lt(|ptr| {
            // ptr: Ptr<PointsTo<'this, NodeStateCentral<'this>>, Node>
            // Expand the permissions to the fields of `Node`
            let ptr = NodeStateCentral::unpack(ptr);
            // Expand the lifetime
            node_helpers::unpack_next_lt(ptr, |ptr| {
                // ptr: Ptr<
                //     PointsTo<'this>,
                //     Node<
                //         PackLt!(PointsTo<'_, NodeStateBwd<'_, 'this>>),
                //         PointsTo<'next, NodeStateFwd<'next, 'this>>,
                //     >,
                // >
                // Extract the ownership in `next` (and get a copy of that pointer).
                let (ptr, next) = extract_field_permission(ptr);
                // We need to allocate a new node at address `'new` that can have `'new` in
                // its type, hence the need for a closure like this. We must pack the `'new`
                // brand before returning.
                type ToAlloc<'prev> =
                    PackLt!(<NodeStateFwd<'_, 'prev> as PackedPredicate<'_, Node>>::Unpacked);
                let ptr = Ptr::new_uninit_cyclic::<ToAlloc<'_>, _>(|new| {
                    // Update `next.prev` to point to `new`.
                    let next = next.map(|next| {
                        let next = NodeStateFwd::unpack(next);
                        let (next, _) = node_helpers::write_prev(next, new.weak_ref());
                        let next = NodeStateFwd::pack(next);
                        pack_lt(next)
                    });
                    // Allocate a new node whose `prev` field is `ptr` and `next` field is
                    // `next`.
                    let new = NodeStateFwd::pack(new.write(Node {
                        val,
                        prev: Some(ptr.weak_ref()),
                        next,
                    }));
                    // Update `ptr.next`.
                    let (ptr, _) = node_helpers::write_next(ptr, new);
                    // Pack the `'new` lifetime
                    node_helpers::pack_next_lt(ptr)
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
        self.0.unpack_lt(|ptr| {
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
            node_helpers::unpack_next_lt(ptr, |ptr| {
                // ptr: Ptr<
                //     PointsTo<'this>,
                //     Node<
                //         PackLt!(PointsTo<'_, NodeStateBwd<'_, 'this>>),
                //         PointsTo<'next, NodeStateFwd<'next, 'this>>,
                //     >,
                // >
                // Extract the ownership in `next` (and get a copy of that pointer).
                let (ptr, next) = extract_field_permission(ptr);
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
                let (ptr, _) = node_helpers::write_prev_permission(next, ptr);
                // ptr: Ptr<PointsTo<'next>,
                //    Node<
                //      PointsTo<'this, NodeStateBwd<'this, 'next>>,
                //      PackLt!(PointsTo<'_, NodeStateFwd<'_, 'next>>),
                //    >>
                // >
                // Pack lifetime
                let ptr = node_helpers::pack_prev_lt(ptr);
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
        self.0.unpack_lt(|ptr| {
            // Expand the permissions to the fields of `Node`
            let ptr = NodeStateCentral::unpack(ptr);
            // Expand the lifetime
            node_helpers::unpack_prev_lt(ptr, |ptr| {
                // Extract the ownership in `prev` (and get a copy of that pointer).
                let (ptr, prev) = extract_field_permission(ptr);
                // `unwrap` is ok because we checked earlier.
                let prev = prev.unwrap();
                // Unexpand the permissions
                let ptr = NodeStateFwd::pack(ptr);
                // Expand the permissions
                let prev = NodeStateBwd::unpack(prev);
                // Insert ownership
                let (ptr, _) = node_helpers::write_next_permission(prev, ptr);
                // Pack lifetime
                let ptr = node_helpers::pack_next_lt::<
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
