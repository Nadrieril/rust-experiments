use higher_kinded_types::ForLt as PackLt;

mod fields;
mod permissions;
mod ptr;
use fields::*;
use permissions::*;
use ptr::*;

/// `Prev` and `Next` are permissions
// The permissions are in generics to be able to move permissions around easily. The `HasPermField`
// trait helps manage these permissions.
struct Node<Prev = (), Next = ()> {
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

    /// Writes the given pointer into `ptr.next`.
    pub fn write_next<'this, Perm: HasOwn<'this>, Prev, OldNext, Next>(
        ptr: Ptr<Perm, Node<Prev, OldNext>>,
        next: Option<Ptr<Next, Node>>,
    ) -> (Ptr<Perm, Node<Prev, Next>>, Option<Ptr<OldNext, Node>>) {
        Node::write_field(ptr, next)
    }
    /// Writes the given pointer into `ptr.prev`.
    pub fn write_prev<'this, Perm: HasOwn<'this>, OldPrev, Prev, Next>(
        ptr: Ptr<Perm, Node<OldPrev, Next>>,
        prev: Option<Ptr<Prev, Node>>,
    ) -> (Ptr<Perm, Node<Prev, Next>>, Option<Ptr<OldPrev, Node>>) {
        <Node<_, _> as HasPermField<0, _>>::write_field(ptr, prev)
    }

    /// Like `write_next` but only moves permissions around. Does not write to memory.
    pub fn write_next_permission<'this, 'next, Perm, Prev, OldNext, Next>(
        ptr: Ptr<Perm, Node<Prev, OldNext>>,
        next: Ptr<Next, Node>,
    ) -> (Ptr<Perm, Node<Prev, Next>>, Option<Ptr<OldNext, Node>>)
    where
        Perm: HasOwn<'this>,
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
        Perm: HasOwn<'this>,
        OldPrev: HasWeak<'prev>,
        Prev: HasWeak<'prev>,
    {
        <Node<_, _> as HasPermField<0, _>>::write_field_permission(ptr, prev)
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
struct NodeStateFwd<'this, 'prev>(InvariantLifetime<'this>, InvariantLifetime<'prev>);
impl<'this, 'prev> PackedPredicate<'this, Node> for NodeStateFwd<'this, 'prev> {
    type Unpacked = Node<Weak<'prev>, PackLt!(Own<'_, NodeStateFwd<'_, 'this>>)>;
}

/// Like `NodeStateFwd` except flipping the fields of `Node` (the "forward" pointer is in the
/// `Node.prev` field instead).
struct NodeStateBwd<'this, 'next>(InvariantLifetime<'this>, InvariantLifetime<'next>);
impl<'this, 'next> PackedPredicate<'this, Node> for NodeStateBwd<'this, 'next> {
    type Unpacked = Node<PackLt!(Own<'_, NodeStateBwd<'_, 'this>>), Weak<'next>>;
}

/// A Node whose `prev` and `next` fields are each a forward-owned linked list with back-edges.
/// This functions as a doubly-linked-list zipper.
struct NodeStateCentral<'this>(InvariantLifetime<'this>);
impl<'this> PackedPredicate<'this, Node> for NodeStateCentral<'this> {
    type Unpacked =
        Node<PackLt!(Own<'_, NodeStateBwd<'_, 'this>>), PackLt!(Own<'_, NodeStateFwd<'_, 'this>>)>;
}

mod list_helpers {
    use super::fields::*;
    use super::permissions::*;
    use super::ptr::*;
    use super::Node;
    use super::*;
    use higher_kinded_types::ForLt as PackLt;

    /// Allocates a new node with the given value. This can either take a `next` node before
    /// which to insert the node, or a `prev` pointer to give to the new node. This ensures
    /// that proper `prev` discipline is preserved.
    pub fn prepend_inner<'this, 'prev>(
        next_or_prev: Result<
            Ptr<Own<'this, NodeStateFwd<'this, 'prev>>, Node>,
            Option<Ptr<Weak<'prev>, Node>>,
        >,
        val: usize,
    ) -> Ptr<PackLt!(Own<'_, NodeStateFwd<'_, 'prev>>), Node> {
        // We need to allocate a new node at address `'new` that can have `'new` in
        // its type, hence the need for a closure like this. We must pack the `'new`
        // brand before returning.
        type ToAlloc<'prev> =
            PackLt!(<NodeStateFwd<'_, 'prev> as PackedPredicate<'_, Node>>::Unpacked);
        Ptr::new_uninit_cyclic::<ToAlloc<'_>, _>(|new| {
            // Update `next.prev` to point to `new`.
            let (prev, next) = match next_or_prev {
                Ok(next) => {
                    let next = NodeStateFwd::unpack(next);
                    let (next, prev) = node_helpers::write_prev(next, Some(new.weak_ref()));
                    let next = NodeStateFwd::pack(next);
                    (prev, Some(pack_lt(next)))
                }
                Err(prev) => (prev, None),
            };
            // Allocate a new node whose `next` field is `next`.
            let new = NodeStateFwd::pack(new.write(Node { val, prev, next }));
            // Pack the `'new` lifetime
            pack_lt(new)
        })
    }
}

#[derive(Debug)]
pub struct List(Option<Ptr<PackLt!(Own<'_, NodeStateFwd<'_, 'static>>), Node>>);

impl List {
    pub fn new() -> Self {
        List(None)
    }

    /// Add a new element at the start of the list.
    pub fn prepend(&mut self, val: usize) {
        let ptr = self.0.take();
        let new = unpack_opt_lt(ptr, |ptr| {
            let next_or_prev = ptr.ok_or(None);
            list_helpers::prepend_inner(next_or_prev, val)
        });
        self.0 = Some(new);
    }

    pub fn cursor(&mut self) -> ListCursor<'_> {
        let ptr = self.0.take().map(|ptr| {
            ptr.unpack_lt(|ptr| {
                let ptr = NodeStateFwd::unpack(ptr);
                let (ptr, _) = node_helpers::write_prev(ptr, None);
                let ptr = NodeStateCentral::pack(ptr);
                pack_lt(ptr)
            })
        });
        ListCursor {
            ptr,
            list: Some(self),
        }
    }

    pub fn iter(&self) -> ListIter<'_> {
        ListIter(
            self.0
                .as_ref()
                .map(|ptr| ptr.unpack_lt_ref(|ptr| pack_lt(pack_lt(ptr)))),
        )
    }
}

// We existentially quantify two pointer tags: the current one and the previous one.
pub struct ListIter<'a>(
    Option<
        Ptr<
            PackLt!(<'prev> = PackLt!(<'this> = Read<'this, 'a, NodeStateFwd<'this, 'prev>>)),
            Node,
        >,
    >,
);

impl<'a> Iterator for ListIter<'a> {
    type Item = &'a usize;
    fn next(&mut self) -> Option<Self::Item> {
        fn advance<'this, 'prev, 'a>(
            ptr: Ptr<Read<'this, 'a, NodeStateFwd<'this, 'prev>>, Node>,
        ) -> Option<Ptr<PackLt!(Read<'_, 'a, NodeStateFwd<'_, 'this>>), Node>> {
            let ptr = NodeStateFwd::unpack(ptr);
            // ptr: Ptr<Read<'this, 'a>, Node<Weak<'prev>, PackLt!(Own<'_, NodeStateFwd<'_, 'this>>)>>
            node_helpers::unpack_next_lt(ptr, |ptr| {
                // ptr: Ptr<Read<'this, 'a>, Node<Weak<'prev>, Own<'next, NodeStateFwd<'next, 'this>>>>
                let next = <Node<_, _> as HasPermField<1, _>>::read_field(ptr)?;
                // next: Ptr<Read<'next, 'a, NodeStateFwd<'next, 'this>>, Node>
                Some(pack_lt(next))
            })
        }
        self.0.take()?.unpack_lt(|ptr| {
            ptr.unpack_lt(|ptr| {
                let val = &ptr.deref().val;
                self.0 = advance(ptr).map(pack_lt);
                Some(val)
            })
        })
    }
}

#[derive(Debug)]
pub struct ListCursor<'a> {
    ptr: Option<Ptr<PackLt!(Own<'_, NodeStateCentral<'_>>), Node>>,
    /// Borrow of the original list. While the cursor exists, the list thinks it's empty. Call
    /// `restore_list` to restore the list to the expected state.
    /// This is only `None` if we moved the value out, to prevent drop.
    list: Option<&'a mut List>,
}

impl ListCursor<'_> {
    pub fn val(&self) -> Option<&usize> {
        Some(self.ptr.as_ref()?.unpack_lt_ref(|ptr| &ptr.deref().val))
    }
    pub fn val_mut(&mut self) -> Option<&mut usize> {
        Some(
            self.ptr
                .as_mut()?
                .unpack_lt_mut(|ptr| &mut ptr.into_deref_mut().val),
        )
    }

    /// Restore the borrowed list after the cursor modifications.
    // TODO: avoid the backward-retraversal of the list.
    // I want to keep the first ptr around for when we're done with the cursor. Can only recover
    // usage of the first pointer if the current state is compatible: need a magic wand.
    pub fn restore_list(mut self) {
        let mut first = loop {
            match self.prev() {
                Ok(prev) => self = prev,
                Err(first) => break first,
            }
        };
        let Some(ptr) = first.ptr.take() else {
            return;
        };
        let Some(list) = first.list.take() else {
            return;
        };
        ptr.unpack_lt(|ptr| {
            let ptr = NodeStateCentral::unpack(ptr);
            let (ptr, _) = node_helpers::write_prev(ptr, None);
            let ptr = NodeStateFwd::pack(ptr);
            let ptr = pack_lt(ptr);
            list.0 = Some(ptr);
        });
    }

    pub fn insert_after(mut self, val: usize) -> Self {
        let Some(ptr) = self.ptr.take() else {
            // The original list was empty.
            let list = self.list.take().unwrap();
            list.prepend(val);
            return list.cursor();
        };
        // self: Ptr<PackLt!(PointsTo<'_, NodeStateCentral<'_>>), Node>
        // Expand the lifetime
        ptr.unpack_lt(|ptr| {
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
                let (ptr, next) = extract_field_permission::<1, _, _, _>(ptr);
                let next_or_prev = next.ok_or(Some(ptr.weak_ref()));
                let new = list_helpers::prepend_inner(next_or_prev, val);
                // Update `ptr.next`.
                let (ptr, _) = node_helpers::write_next(ptr, Some(new));
                // Unexpand permissions
                let ptr = NodeStateCentral::pack(ptr);
                // ptr: Ptr<PointsTo<'next, NodeStateCentral<'next>>, Node>
                // Pack lifetime
                let ptr = pack_lt(ptr);
                // ptr: Ptr<PackLt!(PointsTo<'_, NodeStateCentral<'_>>), Node>
                Self {
                    ptr: Some(ptr),
                    list: self.list.take(),
                }
            })
        })
    }

    /// Advance the cursor. Returns `Err(self)` if the cursor could not be advanced.
    pub fn next(mut self) -> Result<Self, Self> {
        let Some(ptr) = self.ptr.take() else {
            return Err(self);
        };
        if ptr.unpack_lt_ref(|ptr| ptr.next.is_none()) {
            self.ptr = Some(ptr);
            return Err(self);
        };
        // self: Ptr<PackLt!(PointsTo<'_, NodeStateCentral<'_>>), Node>
        // Expand the lifetime
        ptr.unpack_lt(|ptr| {
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
                Ok(Self {
                    ptr: Some(ptr),
                    list: self.list.take(),
                })
            })
        })
    }
    /// Move the cursor backwards. Returns `Err(self)` if the cursor could not be moved.
    pub fn prev(mut self) -> Result<Self, Self> {
        let Some(ptr) = self.ptr.take() else {
            return Err(self);
        };
        if ptr.unpack_lt_ref(|ptr| ptr.prev.is_none()) {
            self.ptr = Some(ptr);
            return Err(self);
        };
        // Expand the lifetime
        ptr.unpack_lt(|ptr| {
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
                    PackLt!(<'a> = Own<'a, NodeStateFwd<'a, '_>>),
                >(ptr);
                // Unexpand permissions
                let ptr = NodeStateCentral::pack(ptr);
                // Pack lifetime
                let ptr = pack_lt(ptr);
                Ok(Self {
                    ptr: Some(ptr),
                    list: self.list.take(),
                })
            })
        })
    }
}

impl Drop for ListCursor<'_> {
    fn drop(&mut self) {
        if self.list.is_none() {
            return;
        }
        take_mut::take(self, |this| {
            this.restore_list();
            ListCursor {
                ptr: None,
                list: None,
            }
        })
    }
}

#[test]
fn test() {
    let mut list = List::new();
    list.prepend(1);
    list.prepend(0);
    assert_eq!(list.iter().copied().collect::<Vec<_>>(), vec![0, 1]);

    let cursor = list.cursor();
    let cursor = cursor.next().unwrap().insert_after(2).prev().unwrap();
    assert_eq!(cursor.val().unwrap(), &0);
    let cursor = cursor.next().unwrap();
    assert_eq!(cursor.val().unwrap(), &1);
    let cursor = cursor.next().unwrap();
    assert_eq!(cursor.val().unwrap(), &2);
    let cursor = cursor.prev().unwrap();
    assert_eq!(cursor.val().unwrap(), &1);
    let cursor = cursor.prev().unwrap();
    assert_eq!(cursor.val().unwrap(), &0);
    let cursor = cursor.next().unwrap();
    drop(cursor);

    assert_eq!(list.iter().copied().collect::<Vec<_>>(), vec![0, 1, 2]);
    // TODO: list drop
    // TODO: iter_mut
}
