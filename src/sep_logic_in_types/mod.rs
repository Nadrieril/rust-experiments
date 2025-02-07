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

/// Type-level tokens that represent each field of `Node`.
#[derive(Clone, Copy)]
struct FPrev;
#[derive(Clone, Copy)]
struct FNext;

// All of the unsafe for `Node` is in these three declarations.
unsafe impl<Prev, Next> EraseNestedPerms for Node<Prev, Next> {
    type Erased = Node;
}

unsafe impl<Prev, Next> HasPermField<FPrev, Prev> for Node<Prev, Next> {
    type FieldTy = Node;
    type ChangePerm<NewPrev> = Node<NewPrev, Next>;
    fn field_ref(&self, _: FPrev) -> &Option<Ptr<Prev, Self::FieldTy>> {
        &self.prev
    }
    fn field_mut(&mut self, _: FPrev) -> &mut Option<Ptr<Prev, Self::FieldTy>> {
        &mut self.prev
    }
}
unsafe impl<Prev, Next> HasPermField<FNext, Next> for Node<Prev, Next> {
    type FieldTy = Node;
    type ChangePerm<NewNext> = Node<Prev, NewNext>;
    fn field_ref(&self, _: FNext) -> &Option<Ptr<Next, Self::FieldTy>> {
        &self.next
    }
    fn field_mut(&mut self, _: FNext) -> &mut Option<Ptr<Next, Self::FieldTy>> {
        &mut self.next
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
                    let (next, prev) = next.write_field(FPrev, Some(new.weak_ref()));
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
                let (ptr, _) = ptr.write_field(FPrev, None);
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
    pub fn iter_mut(&mut self) -> ListIterMut<'_> {
        ListIterMut(
            self.0
                .as_mut()
                .map(|ptr| ptr.unpack_lt_mut(|ptr| pack_lt(pack_lt(ptr)))),
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
            ptr.unpack_field_lt(FNext, |ptr| {
                // ptr: Ptr<Read<'this, 'a>, Node<Weak<'prev>, Own<'next, NodeStateFwd<'next, 'this>>>>
                let next = ptr.read_field(FNext).1?;
                // next: Ptr<Read<'next, 'a, NodeStateFwd<'next, 'this>>, Node>
                Some(pack_lt(next))
            })
        }
        self.0.take()?.unpack_lt(|ptr| {
            ptr.unpack_lt(|ptr| {
                let val = &ptr.deref_exact().val;
                self.0 = advance(ptr).map(pack_lt);
                Some(val)
            })
        })
    }
}

pub struct ListIterMut<'a>(
    Option<
        Ptr<PackLt!(<'prev> = PackLt!(<'this> = Mut<'this, 'a, NodeStateFwd<'this, 'prev>>)), Node>,
    >,
);

impl<'a> Iterator for ListIterMut<'a> {
    type Item = &'a mut usize;
    fn next(&mut self) -> Option<Self::Item> {
        fn advance<'this, 'prev, 'a>(
            ptr: Ptr<Mut<'this, 'a, NodeStateFwd<'this, 'prev>>, Node>,
        ) -> (
            Ptr<Mut<'this, 'a>, Node>,
            Option<Ptr<PackLt!(Mut<'_, 'a, NodeStateFwd<'_, 'this>>), Node>>,
        ) {
            let ptr = NodeStateFwd::unpack(ptr);
            // ptr: Ptr<Mut<'this, 'a>, Node<Weak<'prev>, PackLt!(Own<'_, NodeStateFwd<'_, 'this>>)>>
            ptr.unpack_field_lt(FNext, |ptr| {
                // ptr: Ptr<Mut<'this, 'a>, Node<Weak<'prev>, Own<'next, NodeStateFwd<'next, 'this>>>>
                let (ptr, next) = ptr.read_field(FNext);
                // ptr: Ptr<Mut<'this, 'a>, Node<Weak<'prev>, Weak<'next>>>
                // next: Ptr<Mut<'next, 'a, NodeStateFwd<'next, 'this>>, Node>
                let ptr = ptr.erase_target_perms();
                (ptr, next.map(pack_lt))
            })
        }
        self.0.take()?.unpack_lt(|ptr| {
            ptr.unpack_lt(|ptr| {
                let (ptr, next) = advance(ptr);
                self.0 = next.map(pack_lt);
                Some(&mut ptr.into_deref_mut().val)
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
        Some(
            self.ptr
                .as_ref()?
                .unpack_lt_ref(|ptr| &ptr.deref_exact().val),
        )
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
            let (ptr, _) = ptr.write_field(FPrev, None);
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
        // self: Ptr<PackLt!(Own<'_, NodeStateCentral<'_>>), Node>
        // Expand the lifetime
        ptr.unpack_lt(|ptr| {
            // ptr: Ptr<Own<'this, NodeStateCentral<'this>>, Node>
            // Expand the permissions to the fields of `Node`
            let ptr = NodeStateCentral::unpack(ptr);
            // Expand the lifetime
            ptr.unpack_field_lt(FNext, |ptr| {
                // ptr: Ptr<
                //     Own<'this>,
                //     Node<
                //         PackLt!(Own<'_, NodeStateBwd<'_, 'this>>),
                //         Own<'next, NodeStateFwd<'next, 'this>>,
                //     >,
                // >
                // Extract the ownership in `next` (and get a copy of that pointer).
                let (ptr, next) = extract_field_permission(ptr, FNext);
                let next_or_prev = next.ok_or(Some(ptr.weak_ref()));
                let new = list_helpers::prepend_inner(next_or_prev, val);
                // Update `ptr.next`.
                let (ptr, _) = ptr.write_field(FNext, Some(new));
                // Unexpand permissions
                let ptr = NodeStateCentral::pack(ptr);
                // ptr: Ptr<Own<'next, NodeStateCentral<'next>>, Node>
                // Pack lifetime
                let ptr = pack_lt(ptr);
                // ptr: Ptr<PackLt!(Own<'_, NodeStateCentral<'_>>), Node>
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
        if ptr.unpack_lt_ref(|ptr| ptr.deref().next.is_none()) {
            self.ptr = Some(ptr);
            return Err(self);
        };
        // self: Ptr<PackLt!(Own<'_, NodeStateCentral<'_>>), Node>
        // Expand the lifetime
        ptr.unpack_lt(|ptr| {
            // ptr: Ptr<Own<'this, NodeStateCentral<'this>>, Node>
            // Expand the permissions to the fields of `Node`
            let ptr = NodeStateCentral::unpack(ptr);
            // ptr: Ptr<
            //     Own<'this>,
            //     Node<
            //         PackLt!(Own<'_, NodeStateBwd<'_, 'this>>),
            //         PackLt!(Own<'_, NodeStateFwd<'_, 'this>>),
            //     >,
            // >
            // Expand the lifetime
            ptr.unpack_field_lt(FNext, |ptr| {
                // ptr: Ptr<
                //     Own<'this>,
                //     Node<
                //         PackLt!(Own<'_, NodeStateBwd<'_, 'this>>),
                //         Own<'next, NodeStateFwd<'next, 'this>>,
                //     >,
                // >
                // Extract the ownership in `next` (and get a copy of that pointer).
                let (ptr, next) = extract_field_permission(ptr, FNext);
                // `unwrap` is ok because we checked earlier.
                let next = next.unwrap();
                // ptr: Ptr<
                //     Own<'this>,
                //     Node<
                //         PackLt!(Own<'_, NodeStateBwd<'_, 'this>>),
                //         Weak<'next>,
                //     >,
                // >
                // next: Ptr<Own<'next, NodeStateFwd<'next, 'this>>, Node>
                // Unexpand the permissions
                let ptr = NodeStateBwd::pack(ptr);
                // ptr: Ptr<Own<'this, NodeStateBwd<'this, 'next>>, Node>
                // Expand the permissions
                let next = NodeStateFwd::unpack(next);
                // next: Ptr<Own<'next>,
                //    Node<
                //      Weak<'this>,
                //      PackLt!(Own<'_, NodeStateFwd<'_, 'next>>),
                //    >,
                // >
                // Insert ownership
                let (ptr, _) = next.write_field_permission(FPrev, ptr);
                // ptr: Ptr<Own<'next>,
                //    Node<
                //      Own<'this, NodeStateBwd<'this, 'next>>,
                //      PackLt!(Own<'_, NodeStateFwd<'_, 'next>>),
                //    >>
                // >
                // Pack lifetime
                let ptr = Node::pack_field_lt(ptr, FPrev);
                // ptr: Ptr<Own<'next>,
                //    Node<
                //      PackLt!(Own<'_, NodeStateBwd<'_, 'next>>),
                //      PackLt!(Own<'_, NodeStateFwd<'_, 'next>>),
                //    >>
                // >
                // Unexpand permissions
                let ptr = NodeStateCentral::pack(ptr);
                // ptr: Ptr<Own<'next, NodeStateCentral<'next>>, Node>
                // Pack lifetime
                let ptr = pack_lt(ptr);
                // ptr: Ptr<PackLt!(Own<'_, NodeStateCentral<'_>>), Node>
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
        if ptr.unpack_lt_ref(|ptr| ptr.deref().prev.is_none()) {
            self.ptr = Some(ptr);
            return Err(self);
        };
        // Expand the lifetime
        ptr.unpack_lt(|ptr| {
            // Expand the permissions to the fields of `Node`
            let ptr = NodeStateCentral::unpack(ptr);
            // Expand the lifetime
            ptr.unpack_field_lt(FPrev, |ptr| {
                // Extract the ownership in `prev` (and get a copy of that pointer).
                let (ptr, prev) = extract_field_permission(ptr, FPrev);
                // `unwrap` is ok because we checked earlier.
                let prev = prev.unwrap();
                // Unexpand the permissions
                let ptr = NodeStateFwd::pack(ptr);
                // Expand the permissions
                let prev = NodeStateBwd::unpack(prev);
                // Insert ownership
                let (ptr, _) = prev.write_field_permission(FNext, ptr);
                // Pack lifetime
                let ptr = Node::pack_field_lt(ptr, FNext);
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
    for x in list.iter_mut() {
        *x += 1;
    }
    assert_eq!(list.iter().copied().collect::<Vec<_>>(), vec![1, 2, 3]);
    // TODO: list drop
}
