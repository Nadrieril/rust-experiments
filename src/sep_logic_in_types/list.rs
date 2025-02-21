use super::{fields::*, permissions::*, ptr::*, ExistsLt, PackLt};
use crate::ExistsLt;

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
impl PointeePred for NodeStateFwd<'_, '_> {}
impl<'this, 'prev> PackedPredicate<'this, Node> for NodeStateFwd<'this, 'prev> {
    type Unpacked = Node<PointsTo<'prev>, PackLt!(Own<'_, NodeStateFwd<'_, 'this>>)>;
}

/// Like `NodeStateFwd` except flipping the fields of `Node` (the "forward" pointer is in the
/// `Node.prev` field instead).
struct NodeStateBwd<'this, 'next>(InvariantLifetime<'this>, InvariantLifetime<'next>);
impl PointeePred for NodeStateBwd<'_, '_> {}
impl<'this, 'next> PackedPredicate<'this, Node> for NodeStateBwd<'this, 'next> {
    type Unpacked = Node<PackLt!(Own<'_, NodeStateBwd<'_, 'this>>), PointsTo<'next>>;
}

/// A Node whose `prev` and `next` fields are each a forward-owned linked list with back-edges.
/// This functions as a doubly-linked-list zipper.
struct NodeStateCursor<'this>(InvariantLifetime<'this>);
impl PointeePred for NodeStateCursor<'_> {}
impl<'this> PackedPredicate<'this, Node> for NodeStateCursor<'this> {
    type Unpacked =
        Node<PackLt!(Own<'_, NodeStateBwd<'_, 'this>>), PackLt!(Own<'_, NodeStateFwd<'_, 'this>>)>;
}

use list_helpers::NonEmptyListInner;
mod list_helpers {
    use super::super::{fields::*, permissions::*, ptr::*, PackLt};
    use super::*;

    #[derive(Debug)]
    pub struct NonEmptyListInner<'prev>(Ptr<PackLt!(Own<'_, NodeStateFwd<'_, 'prev>>), Node>);

    impl<'prev> NonEmptyListInner<'prev> {
        pub fn new(val: usize, prev: Option<Ptr<PointsTo<'prev>, Node>>) -> Self {
            Self(prepend_inner(Err(prev), val))
        }
        pub fn from_ptr(ptr: Ptr<PackLt!(Own<'_, NodeStateFwd<'_, 'prev>>), Node>) -> Self {
            Self(ptr)
        }
        pub fn into_ptr(self) -> Ptr<PackLt!(Own<'_, NodeStateFwd<'_, 'prev>>), Node> {
            self.0
        }
        pub fn as_ptr(&self) -> &Ptr<PackLt!(Own<'_, NodeStateFwd<'_, 'prev>>), Node> {
            &self.0
        }
        pub fn as_ptr_mut(&mut self) -> &mut Ptr<PackLt!(Own<'_, NodeStateFwd<'_, 'prev>>), Node> {
            &mut self.0
        }

        pub fn prepend_inner(self, val: usize) -> Self {
            self.0.unpack_lt(|ptr| Self(prepend_inner(Ok(ptr), val)))
        }
        pub fn pop_front(self) -> (Option<Self>, Option<usize>) {
            self.into_ptr().unpack_lt(|ptr| {
                let ptr = NodeStateFwd::unpack(ptr);
                ptr.unpack_field_lt(FNext, |ptr| {
                    // ptr: Ptr<
                    //     Own<'this>,
                    //     Node<
                    //         PointsTo<'prev>,
                    //         Own<'next, NodeStateFwd<'next, 'this>>,
                    //     >,
                    // >
                    let (ptr, next) = ptr.read_field(FNext);
                    // ptr: Ptr<Own<'this>, Node<PointsTo<'prev>, PointsTo<'next>>>
                    let Node { prev, val, .. } = ptr.into_inner();
                    let list = next.map(|next| {
                        // next: Ptr<Own<'next, NodeStateFwd<'next, 'this>>, Node>
                        let next = NodeStateFwd::unpack(next);
                        let (next, _) = next.write_field(FPrev, prev);
                        let next = NodeStateFwd::pack(next);
                        // next: Ptr<Own<'next, NodeStateFwd<'next, 'prev>>, Node>
                        Self(pack_lt(next))
                    });
                    (list, Some(val))
                })
            })
        }
    }

    /// Allocates a new node with the given value. This can either take a `next` node before
    /// which to insert the node, or a `prev` pointer to give to the new node. This ensures
    /// that proper `prev` discipline is preserved.
    fn prepend_inner<'this, 'prev>(
        next_or_prev: Result<
            Ptr<Own<'this, NodeStateFwd<'this, 'prev>>, Node>,
            Option<Ptr<PointsTo<'prev>, Node>>,
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

// TODO: to represent pointer-to-last, let FwdList contain (ptr, wand<ptr, BwdList>) and vice-versa!
//
// problem: a ListFwd<'last> must guarantee ownership of `'last`. therefore the `next: None` must
// be proof-carrying.
// idea: Strong/Weak pair that together make a Own.
// wait no, to guarantee ownership _without a runtime check_ (as this would require
// going through the list looking for a ptr equal to `last`), the `None` must be
// proof-carrying.
//   -> wait no, the wand carries the proof
// impl<'this, 'prev, 'last> PackedPredicate<'this, Node> for NodeStateFwd<'this, 'prev, 'last> {
//     type Unpacked = Node<PointsTo<'prev>, (PackLt!(Own<'_, NodeStateFwd<'_, 'this, 'last>>, IfNull<Eq<'this, 'last>>))>;
// }
// this isn't enough, I need to know that from the current node I can deduce a `Own<'last, NodeStateBwd<'last, 'static>>`.
// need a wand. good thing: wand can be on permissions directly, no need for ptrs.
// Wand(Own<'this, NodeStateFwd<'this, 'static, 'last>) -> (Own<'last, NodeStateBwd<'last, 'static>>, same thing backwards)
// the `'static` is load-bearing: must be sure that we don't accidentally interpret a prev pointer
// as owning if we shouldn't.
// if the wand gave out a pointer, I would not need to track `'last` (maybe).
//
// two difficulties with wands:
// - what if I proved a wand through a node that has since been removed? said differently, how do I
// remove nodes while preserving wands?
// - how to handle existential (un)packing? once packed, the predicate is basically meaningless. is
// it enough to keep the `'this` unpacked?
//
// also starting to feel like I can move the permission tokens out of pointers.
// struct Node<'prev, 'next, PrevNone = (), NextNone = ()> {
//     prev: Result<Ptr<'prev, ExistsLt<'a, 'b> Node<'a, 'b>>, PrevNone>,
//     next: Result<Ptr<'next, ExistsLt<'a, 'b> Node<'a, 'b>>, NextNone>,
// }
// impl<'this, 'prev, 'next, 'last> PackedPredicate<'this, Node<'prev, 'next>> for NodeStateFwd<'this, 'prev, 'last> {
//     type Unpacked = Node<(), Eq<'this, 'last>>;
//     type ExtraPreds = Own<'next, NodeStateFwd<'next, 'this, 'last>>;
//     // IfNull<'next, Eq<'this, 'last>>
// }
// problem with this: no way to talk about a list of ptrs. need `Vec<Ptr<PackLt!()>>` to mean "for
// each ptr, exists a brand".
// -> tbh, could make `ErasedPtr` that can be unerased.
// ergo: keep current thing, but allow taking predicates directly.
// -> makes pairs of preds easy to handle
// make `NullablePtr` and `IfNull` predicate.
#[derive(Debug)]
pub struct List(Option<NonEmptyListInner<'static>>);

impl List {
    pub fn new() -> Self {
        List(None)
    }

    /// Add a new element at the start of the list.
    pub fn prepend(&mut self, val: usize) {
        let ptr = self.0.take();
        let new = match ptr {
            Some(list) => list.prepend_inner(val),
            None => NonEmptyListInner::new(val, None),
        };
        self.0 = Some(new);
    }
    pub fn pop_front(&mut self) -> Option<usize> {
        let list = self.0.take()?;
        let (list, val) = list.pop_front();
        self.0 = list;
        val
    }

    pub fn cursor(&mut self) -> ListCursor<'_> {
        let inner = self.0.take().map(|ptr| {
            ptr.into_ptr().unpack_lt(|ptr| {
                let ptr = NodeStateFwd::unpack(ptr);
                let (ptr, _) = ptr.write_field(FPrev, None);
                let ptr = NodeStateCursor::pack(ptr);
                ListCursorInner { ptr }.pack_lt()
            })
        });
        ListCursor {
            inner,
            list: Some(self),
        }
    }

    pub fn iter(&self) -> ListIter<'_> {
        ListIter(
            self.0
                .as_ref()
                .map(|ptr| ptr.as_ptr().unpack_lt_ref(|ptr| pack_lt(pack_lt(ptr)))),
        )
    }
    pub fn iter_mut(&mut self) -> ListIterMut<'_> {
        ListIterMut(
            self.0
                .as_mut()
                .map(|ptr| ptr.as_ptr_mut().unpack_lt_mut(|ptr| pack_lt(pack_lt(ptr)))),
        )
    }
}

impl Drop for List {
    fn drop(&mut self) {
        while self.pop_front().is_some() {}
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
            // ptr: Ptr<Read<'this, 'a>, Node<PointsTo<'prev>, PackLt!(Own<'_, NodeStateFwd<'_, 'this>>)>>
            ptr.unpack_field_lt(FNext, |ptr| {
                // ptr: Ptr<Read<'this, 'a>, Node<PointsTo<'prev>, Own<'next, NodeStateFwd<'next, 'this>>>>
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
            // ptr: Ptr<Mut<'this, 'a>, Node<PointsTo<'prev>, PackLt!(Own<'_, NodeStateFwd<'_, 'this>>)>>
            ptr.unpack_field_lt(FNext, |ptr| {
                // ptr: Ptr<Mut<'this, 'a>, Node<PointsTo<'prev>, Own<'next, NodeStateFwd<'next, 'this>>>>
                let (ptr, next) = ptr.read_field(FNext);
                // ptr: Ptr<Mut<'this, 'a>, Node<PointsTo<'prev>, PointsTo<'next>>>
                // next: Ptr<Mut<'next, 'a, NodeStateFwd<'next, 'this>>, Node>
                let ptr = ptr.drop_target_perms();
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

struct ListCursorInner<'this> {
    /// Pointer to a node.
    ptr: Ptr<Own<'this, NodeStateCursor<'this>>, Node>,
}

impl<'this> ListCursorInner<'this> {
    pub fn val(&self) -> &usize {
        &self.ptr.deref().val
    }
    pub fn val_mut(&mut self) -> &mut usize {
        &mut self.ptr.deref_mut().val
    }

    /// Helper.
    fn pack_lt(self) -> ExistsLt!(ListCursorInner<'_>) {
        ExistsLt::pack_lt(self)
    }

    /// Helper: split off the forward list that includes the current node and the rest.
    fn split<R>(
        ptr: Ptr<Own<'this, NodeStateCursor<'this>>, Node>,
        f: impl FnOnce(
            Ptr<Own<'this>, Node<PackLt!(Own<'_, NodeStateBwd<'_, 'this>>), PackLt!(PointsTo<'_>)>>,
            Option<NonEmptyListInner<'this>>,
        ) -> R,
    ) -> R {
        // ptr: Ptr<Own<'this, NodeStateCursor<'this>>, Node>
        // Expand the permissions to the fields of `Node`
        let ptr = NodeStateCursor::unpack(ptr);
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
            let (ptr, next) = ptr.read_field(FNext);
            let ptr = Node::pack_field_lt(ptr, FNext);
            let next = next.map(|next| NonEmptyListInner::from_ptr(pack_lt(next)));
            f(ptr, next)
        })
    }

    /// Helper: reverse `split`.
    fn unsplit(
        ptr: Ptr<
            Own<'this>,
            Node<PackLt!(Own<'_, NodeStateBwd<'_, 'this>>), PackLt!(PointsTo<'_>)>,
        >,
        next: Option<NonEmptyListInner<'this>>,
    ) -> Ptr<Own<'this, NodeStateCursor<'this>>, Node> {
        let next = next.map(|next| next.into_ptr());
        // Update `ptr.next`.
        let (ptr, _) = ptr.write_field(FNext, next);
        // Unexpand permissions
        NodeStateCursor::pack(ptr)
    }

    pub fn insert_after(self, val: usize) -> Self {
        Self::split(self.ptr, |ptr, next| {
            let next = match next {
                Some(next) => next.prepend_inner(val),
                None => NonEmptyListInner::new(val, Some(ptr.weak_ref())),
            };
            let ptr = Self::unsplit(ptr, Some(next));
            // ptr: Ptr<PackLt!(Own<'_, NodeStateCursor<'_>>), Node>
            Self { ptr }
        })
    }

    pub fn remove_after(self) -> (Self, Option<usize>) {
        Self::split(self.ptr, |ptr, next| {
            let (next, val) = match next {
                Some(next) => next.pop_front(),
                None => (None, None),
            };
            let ptr = Self::unsplit(ptr, next);
            let this = Self { ptr };
            (this, val)
        })
    }

    /// Advance the cursor. Returns `Err(self)` if the cursor could not be advanced.
    pub fn next(self) -> Result<ExistsLt!(ListCursorInner<'_>), Self> {
        if self.ptr.deref().next.is_none() {
            return Err(self);
        };
        let ptr = self.ptr;
        // ptr: Ptr<Own<'this, NodeStateCursor<'this>>, Node>
        // Expand the permissions to the fields of `Node`
        let ptr = NodeStateCursor::unpack(ptr);
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
            let (ptr, next) = ptr.read_field(FNext);
            // `unwrap` is ok because we checked earlier.
            let next = next.unwrap();
            // ptr: Ptr<
            //     Own<'this>,
            //     Node<
            //         PackLt!(Own<'_, NodeStateBwd<'_, 'this>>),
            //         PointsTo<'next>,
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
            //      PointsTo<'this>,
            //      PackLt!(Own<'_, NodeStateFwd<'_, 'next>>),
            //    >,
            // >
            // Insert ownership
            let (next, _) = next.write_field_permission(FPrev, ptr);
            // next: Ptr<Own<'next>,
            //    Node<
            //      Own<'this, NodeStateBwd<'this, 'next>>,
            //      PackLt!(Own<'_, NodeStateFwd<'_, 'next>>),
            //    >>
            // >
            // Pack lifetime
            let next = Node::pack_field_lt(next, FPrev);
            // TODO: here we lose info, lens should retain it.
            // but! after this, I could pass the bwd function a pointer with some other address!
            // can this break safety?
            // seems fine, the real problem would be if I write to prev. then first ptr may no
            // longer correspond. feels like I should track the brand of the first ptr. but if I
            // can write with extra brand, why couldn't I write without? can I make an API that
            // ensures things are appropriately branded? probably not.
            // for safety, going prev* should reach the first pointer. writing to prev would
            // therefore break safety.
            // feels like the wand should be in the prev permissions... but prev won't contain the
            // actual pointer, so I should have a `PointsTo<'first>` in the cursor, and a wand<_,
            // Own<'first>> in prev. madness.
            // that would be a permission attached to a different pointer than it applies to.
            // prev: Ptr<'prev, (Own<'prev, NodeStateBwd<'first>>, Wand<Own<'prev, NodeStateBwd<'first>>, Own<'first>>), Node>
            // that could be a lie: such a wand should contain all the missing permissions; if I
            // write to prev.prev then apply the wand I would duplicate permissions.
            // this should be a linear alternation probably.
            // when going forward, take the wand out to pass it to the new prev pointer.
            // TODO: do we need to put the `'first` constraint somewhere? is the wand enough?
            // problem: the first node doesn't have a prev, hence can't take the ownership out,
            // hence we must know that in that case the cursor pointer is `'first`.
            // could have an `EqPredicate<'this, 'first>` in the `None` somehow?
            // impl<'first, 'this, 'next> PackedPredicate<'this, Node> for NodeStateBwd<'first, 'this, 'next> {
            //     type Unpacked = Node<PackLt!(Own<'_, NodeStateBwd<'first, '_, 'this>>), PointsTo<'next>>;
            // }
            // impl<'first, 'this> PackedPredicate<'this, Node> for NodeStateCursor<'this> {
            //     type Unpacked =
            //         Node<PackLt!(Lens<Own<'_, NodeStateBwd<'first, '_, 'this>>, Own<'first>>), PackLt!(Own<'_, NodeStateFwd<'_, 'this>>)>;
            // }
            // doing all this so we can write to next freely. problem: won't work if we also want a
            // `'last` pointer. if we have a last pointer and trying to remove last node, then we
            // must update last pointer.seems ok as long as we rebuild a new cursor with correct
            // invariants. again, only constraint here is safety.
            //
            // next: Ptr<Own<'next>,
            //    Node<
            //      PackLt!(Own<'_, NodeStateBwd<'_, 'next>>),
            //      PackLt!(Own<'_, NodeStateFwd<'_, 'next>>),
            //    >>
            // >
            // Unexpand permissions
            let next = NodeStateCursor::pack(next);
            // next: Ptr<Own<'next, NodeStateCursor<'next>>, Node>
            Ok(ExistsLt::pack_lt(ListCursorInner { ptr: next }))
        })
    }
    /// Move the cursor backwards. Returns `Err(self)` if the cursor could not be moved.
    pub fn prev(self) -> Result<ExistsLt!(ListCursorInner<'_>), Self> {
        if self.ptr.deref().prev.is_none() {
            return Err(self);
        };
        let ptr = self.ptr;
        // Expand the permissions to the fields of `Node`
        let ptr = NodeStateCursor::unpack(ptr);
        // Expand the lifetime
        ptr.unpack_field_lt(FPrev, |ptr| {
            // Extract the ownership in `prev` (and get a copy of that pointer).
            let (ptr, prev) = ptr.read_field(FPrev);
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
            let ptr = NodeStateCursor::pack(ptr);
            // Pack lifetime
            Ok(ExistsLt::pack_lt(ListCursorInner { ptr }))
        })
    }

    /// Converts the current pointer into a list. Assumes that this is pointing to the first
    /// element; any elements before will be lost.
    pub fn into_list(self) -> List {
        let ptr = NodeStateCursor::unpack(self.ptr);
        let (ptr, _) = ptr.write_field(FPrev, None);
        let ptr = NodeStateFwd::pack(ptr);
        let ptr = pack_lt(ptr);
        List(Some(NonEmptyListInner::from_ptr(ptr)))
    }
}

pub struct ListCursor<'a> {
    inner: Option<ExistsLt!(ListCursorInner<'_>)>,
    /// Borrow of the original list. While the cursor exists, the list thinks it's empty. Call
    /// `restore_list` to restore the list to the expected state.
    /// This is only `None` if we moved the value out, to prevent drop.
    list: Option<&'a mut List>,
}

impl ListCursor<'_> {
    pub fn val(&self) -> Option<&usize> {
        self.inner
            .as_ref()
            .map(|inner| inner.unpack_lt_ref(|inner| inner.val()))
    }
    pub fn val_mut(&mut self) -> Option<&mut usize> {
        self.inner
            .as_mut()
            .map(|inner| inner.unpack_lt_mut(|inner| inner.val_mut()))
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
        let Some(inner) = first.inner.take() else {
            return;
        };
        let Some(list) = first.list.take() else {
            return;
        };
        inner.unpack_lt(|inner| {
            *list = inner.into_list();
        });
    }

    pub fn insert_after(mut self, val: usize) -> Self {
        if let Some(inner) = self.inner.take() {
            let inner = inner.unpack_lt(|inner| inner.insert_after(val).pack_lt());
            Self {
                inner: Some(inner),
                list: self.list.take(),
            }
        } else {
            // The original list was empty.
            let list = self.list.take().unwrap();
            list.prepend(val);
            list.cursor()
        }
    }

    pub fn remove_after(mut self) -> (Self, Option<usize>) {
        if let Some(inner) = self.inner.take() {
            inner.unpack_lt(|inner| {
                let (inner, val) = inner.remove_after();
                let this = Self {
                    inner: Some(inner.pack_lt()),
                    list: self.list.take(),
                };
                (this, val)
            })
        } else {
            (self, None)
        }
    }

    /// Advance the cursor. Returns `Err(self)` if the cursor could not be advanced.
    pub fn next(mut self) -> Result<Self, Self> {
        if let Some(inner) = self.inner.take() {
            inner.unpack_lt(|inner| match inner.next() {
                Ok(inner) => Ok(Self {
                    inner: Some(inner),
                    list: self.list.take(),
                }),
                Err(inner) => Err(Self {
                    inner: Some(inner.pack_lt()),
                    list: self.list.take(),
                }),
            })
        } else {
            Err(self)
        }
    }
    /// Move the cursor backwards. Returns `Err(self)` if the cursor could not be moved.
    pub fn prev(mut self) -> Result<Self, Self> {
        if let Some(inner) = self.inner.take() {
            inner.unpack_lt(|inner| match inner.prev() {
                Ok(inner) => Ok(Self {
                    inner: Some(inner),
                    list: self.list.take(),
                }),
                Err(inner) => Err(Self {
                    inner: Some(inner.pack_lt()),
                    list: self.list.take(),
                }),
            })
        } else {
            Err(self)
        }
    }
}

impl<'a> std::fmt::Debug for ListCursor<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ListCursor").finish()
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
                inner: None,
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
    let cursor = cursor.insert_after(42);
    let cursor = cursor.next().unwrap();
    assert_eq!(cursor.val().unwrap(), &42);
    // Does nothing.
    let (cursor, _) = cursor.remove_after();
    assert_eq!(cursor.val().unwrap(), &42);
    let cursor = cursor.prev().unwrap();
    let (cursor, _) = cursor.remove_after();
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
}
