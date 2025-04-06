use std::ptr::NonNull;

use super::*;
use crate::ExistsLt;

/// `Prev` and `Next` are permissions
// The permissions are in generics to be able to move permissions around easily. The `HasPermField`
// trait helps manage these permissions.
struct Node<Prev = NoPerm, Next = NoPerm> {
    val: usize,
    prev: Option<Ptr<Prev, Node>>,
    next: Option<Ptr<Next, Node>>,
}

/// Type-level tokens that represent each field of `Node`.
#[derive(Clone, Copy)]
struct FPrev;
#[derive(Clone, Copy)]
struct FNext;
#[derive(Clone, Copy)]
struct FVal;

// All of the unsafe for `Node` is in these three declarations.
unsafe impl<Prev, Next> ErasePerms for Node<Prev, Next> {
    type Erased = Node;
}

unsafe impl<Prev: PtrPerm, Next: PtrPerm> HasGenericPermField<FPrev, Prev> for Node<Prev, Next> {
    type FieldTy<FieldPerm: PtrPerm> = Option<Ptr<FieldPerm, Node>>;
    type ChangePerm<NewPrev: PtrPerm> = Node<NewPrev, Next>;
    unsafe fn field_raw(ptr: NonNull<Self>, _tok: FPrev) -> NonNull<Option<Ptr<Prev, Node>>> {
        unsafe { NonNull::new_unchecked(&raw mut (*ptr.as_ptr()).prev) }
    }
}
unsafe impl<Prev: PtrPerm, Next: PtrPerm> HasOptPtrField<FPrev, Prev> for Node<Prev, Next> {
    type PointeeTy = Node;
}
unsafe impl<Prev: PtrPerm, Next: PtrPerm> HasGenericPermField<FNext, Next> for Node<Prev, Next> {
    type FieldTy<FieldPerm: PtrPerm> = Option<Ptr<FieldPerm, Node>>;
    type ChangePerm<NewNext: PtrPerm> = Node<Prev, NewNext>;
    unsafe fn field_raw(ptr: NonNull<Self>, _tok: FNext) -> NonNull<Option<Ptr<Next, Node>>> {
        unsafe { NonNull::new_unchecked(&raw mut (*ptr.as_ptr()).next) }
    }
}
unsafe impl<Prev: PtrPerm, Next: PtrPerm> HasOptPtrField<FNext, Next> for Node<Prev, Next> {
    type PointeeTy = Node;
}
unsafe impl<Prev: PtrPerm, Next: PtrPerm, UnusedPerm: PtrPerm> HasGenericPermField<FVal, UnusedPerm>
    for Node<Prev, Next>
{
    type FieldTy<Perm: PtrPerm> = usize;
    type ChangePerm<NewPerm: PtrPerm> = Self;
    unsafe fn field_raw(ptr: NonNull<Self>, _tok: FVal) -> NonNull<Self::FieldTy<UnusedPerm>> {
        unsafe { NonNull::new_unchecked(&raw mut (*ptr.as_ptr()).val) }
    }
}

/// A linked list with backward pointers, with ownership that follows the forward pointers.
struct NodeStateFwd<'this, 'prev>(InvariantLifetime<'this>, InvariantLifetime<'prev>);
impl PointeePred for NodeStateFwd<'_, '_> {}
impl<'this, 'prev> PackedPredicate<'this, Node> for NodeStateFwd<'this, 'prev> {
    type Unpacked = ExistsLt!(<'next> =
        Node<PointsTo<'prev>, Own<'next, NodeStateFwd<'next, 'this>>>
    );
}

// struct FwdNode<'this, 'prev, 'last> {
//     val: usize,
//     prev: Option<Ptr<PointsTo<'prev>, Node>>,
//     next: Result<
//         ExistsLt!(<'next> = (
//             Ptr<Own<'next>, FwdNode<'next, 'this, 'last>>,
//             Wand<
//                 VPtr<Own<'next>, FwdNode<'next, 'this, 'last>>,
//                 VPtr<Own<'last>, Node>, // backward
//             >
//         )),
//         EqPredicate<'this, 'last>,
//     >,
//     // actually, why not a `Wand<VPtr<Own<'this>, Self>, ...>`?
// }
#[expect(unused)]
struct FwdNode<'this, 'prev, 'first, 'last>(
    ExistsLt!(<'next> = Node<
        PointsTo<'prev>,
        PointsTo<'next, (
            VPtr<Own<'next>, FwdNode<'next, 'this, 'first, 'last>>,
            Wand<VPtr<Own<'this>, Self>, ExistsLt!(<'nextlast> = VPtr<Own<'last>, BwdNode<'last, 'nextlast, 'first, 'last>>)>,
        )>,
    >),
);
#[expect(unused)]
// Maybe use a derive to prove `ErasePerms` of this into `Node`. Maybe `Node` is the "layout" that
// everything must erase to. This can also derive pack/unpack to allow safe transmutability with
// its contents.
struct BwdNode<'this, 'next, 'first, 'last>(
    ExistsLt!(<'prev> = Node<
        PointsTo<'prev, (
            VPtr<Own<'prev>, BwdNode<'prev, 'this, 'first, 'last>>,
            Wand<VPtr<Own<'this>, Self>, ExistsLt!(<'firstprev> = VPtr<Own<'first>, FwdNode<'first, 'firstprev, 'first, 'last>>)>,
        )>,
        PointsTo<'next>,
    >),
);

use list_helpers::NonEmptyList;
mod list_helpers {
    use super::*;

    pub struct NonEmptyList<'prev>(
        ExistsLt!(<'this> = Ptr<Own<'this, NodeStateFwd<'this, 'prev>>, Node>),
    );

    impl<'prev> NonEmptyList<'prev> {
        pub fn new(val: usize, prev: Option<Ptr<PointsTo<'prev>, Node>>) -> Self {
            prepend_inner(Err(prev), val)
        }
        pub fn from_ptr<'this>(ptr: Ptr<Own<'this, NodeStateFwd<'this, 'prev>>, Node>) -> Self {
            Self(ExistsLt::pack_lt(ptr))
        }
        pub fn into_ptr(
            self,
        ) -> ExistsLt!(<'this> = Ptr<Own<'this, NodeStateFwd<'this, 'prev>>, Node>) {
            self.0
        }
        pub fn as_ptr(
            &self,
        ) -> &ExistsLt!(<'this> = Ptr<Own<'this, NodeStateFwd<'this, 'prev>>, Node>) {
            &self.0
        }
        pub fn as_ptr_mut(
            &mut self,
        ) -> &mut ExistsLt!(<'this> = Ptr<Own<'this, NodeStateFwd<'this, 'prev>>, Node>) {
            &mut self.0
        }

        pub fn prepend_inner(self, val: usize) -> Self {
            self.0.unpack_lt(|ptr| prepend_inner(Ok(ptr), val))
        }
        pub fn pop_front(self) -> (Option<Self>, Option<usize>) {
            self.into_ptr().unpack_lt(|ptr| {
                let ptr = NodeStateFwd::unpack(ptr);
                ptr.unpack_target_lt(|ptr| {
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
                        next.unpack_target_lt(|next| {
                            let (next, _) = next.write_field(FPrev, prev);
                            let next = pack_target_lt(next);
                            let next = NodeStateFwd::pack(next);
                            // next: Ptr<Own<'next, NodeStateFwd<'next, 'prev>>, Node>
                            Self::from_ptr(next)
                        })
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
    ) -> NonEmptyList<'prev> {
        // We need to allocate a new node at address `'new` that can have `'new` in
        // its type, hence the need for a closure like this. We must pack the `'new`
        // brand before returning.
        type ToAlloc<'prev> =
            PackLt!(<NodeStateFwd<'_, 'prev> as PackedPredicate<'_, Node>>::Unpacked);
        Ptr::new_uninit::<ToAlloc<'_>>().unpack_lt(|new| {
            // Create a new node.
            let node = match next_or_prev {
                Ok(next) => {
                    let next = NodeStateFwd::unpack(next);
                    next.unpack_target_lt(|next| {
                        // Update `next.prev` to point to `new`.
                        let (next, prev) = next.write_field(FPrev, Some(new.weak_ref()));
                        let next = pack_target_lt(next);
                        let next = NodeStateFwd::pack(next);
                        // `'next` only exists in the current scope so we must pack the existential
                        // here.
                        ExistsLt::pack_lt(Node {
                            val,
                            prev,
                            next: Some(next),
                        })
                    })
                }
                Err(prev) => ExistsLt::pack_lt(Node {
                    val,
                    prev,
                    next: None,
                }),
            };
            // Write the new node to the newly-allocated place.
            let new = new.write(node);
            let new = NodeStateFwd::pack(new);
            // Pack the `'new` lifetime
            NonEmptyList::from_ptr(new)
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
// make `NullablePtr` and `IfNull` predicates?
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
pub struct List(Option<NonEmptyList<'static>>);

impl List {
    pub fn new() -> Self {
        List(None)
    }

    /// Add a new element at the start of the list.
    pub fn prepend(&mut self, val: usize) {
        let ptr = self.0.take();
        let new = match ptr {
            Some(list) => list.prepend_inner(val),
            None => NonEmptyList::new(val, None),
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
            ptr.into_ptr()
                .unpack_lt(|ptr| ListCursorInner::new(ptr).pack_lt())
        });
        ListCursor {
            inner,
            list: Some(self),
        }
    }

    pub fn iter(&self) -> ListIter<'_> {
        ListIter(self.0.as_ref().map(|nelist| {
            nelist.as_ptr().unpack_lt_ref(|ptr| {
                // ptr: &Ptr<Own<'_, NodeStateFwd<'_, '_>>, Node>
                let ptr = ptr.copy_read();
                // ptr: Ptr<Read<'_, '_, NodeStateFwd<'_, '_>>, Node>
                ExistsLt::pack_lt(ExistsLt::pack_lt(ptr))
            })
        }))
    }
    pub fn iter_mut(&mut self) -> ListIterMut<'_> {
        ListIterMut(self.0.as_mut().map(|nelist| {
            nelist.as_ptr_mut().unpack_lt_mut(|ptr| {
                // ptr: &mut Ptr<Own<'_, NodeStateFwd<'_, '_>>, Node>
                let ptr = ptr.copy_mut();
                // ptr: Ptr<Mut<'_, '_, NodeStateFwd<'_, '_>>, Node>
                ExistsLt::pack_lt(ExistsLt::pack_lt(ptr))
            })
        }))
    }
}

impl Drop for List {
    fn drop(&mut self) {
        while self.pop_front().is_some() {}
    }
}

// We existentially quantify two pointer tags: the current one and the previous one.
pub struct ListIter<'a>(
    Option<ExistsLt!(<'prev, 'this> = Ptr<Read<'this, 'a, NodeStateFwd<'this, 'prev>>, Node>)>,
);

impl<'a> Iterator for ListIter<'a> {
    type Item = &'a usize;
    fn next(&mut self) -> Option<Self::Item> {
        fn advance<'this, 'prev, 'a>(
            ptr: Ptr<Read<'this, 'a, NodeStateFwd<'this, 'prev>>, Node>,
        ) -> Option<ExistsLt!(Ptr<Read<'_, 'a, NodeStateFwd<'_, 'this>>, Node>)> {
            let ptr = NodeStateFwd::unpack(ptr);
            // ptr: Ptr<
            //    Read<'this, 'a>,
            //    ExistsLt!('next,
            //        Node<PointsTo<'prev>, Own<'next, NodeStateFwd<'next, 'this>>>
            //    )
            //  >
            ptr.unpack_target_lt(|ptr| {
                // ptr: Ptr<Read<'this, 'a>, Node<PointsTo<'prev>, Own<'next, NodeStateFwd<'next, 'this>>>>
                let next = ptr.read_field(FNext).1?;
                // next: Ptr<Read<'next, 'a, NodeStateFwd<'next, 'this>>, Node>
                Some(ExistsLt::pack_lt(next))
            })
        }
        self.0.take()?.unpack_lt(|ptr| {
            ptr.unpack_lt(|ptr| {
                let val = &ptr.deref_exact().val;
                self.0 = advance(ptr).map(ExistsLt::pack_lt);
                Some(val)
            })
        })
    }
}

pub struct ListIterMut<'a>(
    Option<ExistsLt!(<'prev, 'this> = Ptr<Mut<'this, 'a, NodeStateFwd<'this, 'prev>>, Node>)>,
);

impl<'a> Iterator for ListIterMut<'a> {
    type Item = &'a mut usize;
    fn next(&mut self) -> Option<Self::Item> {
        fn advance<'this, 'prev, 'a>(
            ptr: Ptr<Mut<'this, 'a, NodeStateFwd<'this, 'prev>>, Node>,
        ) -> (
            ExistsLt!(<'next> = Ptr<Mut<'this, 'a>, Node<PointsTo<'prev>, PointsTo<'next>>>),
            Option<ExistsLt!(Ptr<Mut<'_, 'a, NodeStateFwd<'_, 'this>>, Node>)>,
        ) {
            let ptr = NodeStateFwd::unpack(ptr);
            ptr.unpack_target_lt(|ptr| {
                // ptr: Ptr<Mut<'this, 'a>, Node<PointsTo<'prev>, Own<'next, NodeStateFwd<'next, 'this>>>>
                let (ptr, next) = ptr.read_field(FNext);
                // ptr: Ptr<Mut<'this, 'a>, Node<PointsTo<'prev>, PointsTo<'next>>>
                // next: Option<Ptr<Mut<'next, 'a, NodeStateFwd<'next, 'this>>, Node>>
                let ptr = ExistsLt::pack_lt(ptr);
                (ptr, next.map(ExistsLt::pack_lt))
            })
        }
        self.0.take()?.unpack_lt(|ptr| {
            ptr.unpack_lt(|ptr| {
                let (ptr, next) = advance(ptr);
                self.0 = next.map(ExistsLt::pack_lt);
                ptr.unpack_lt(|ptr| {
                    // Can't use `deref_mut` as this would create a `&'a mut Node<PointsTo<'prev>,
                    // PointsTo<'next>>` which implies `'prev: 'a`.
                    <Node<_, _> as HasGenericPermField<FVal, NoPerm>>::get_field::<_, NoPerm>(
                        ptr, FVal,
                    )
                    .unpack_lt(|(ptr_to_field, _)| Some(ptr_to_field.into_deref_mut()))
                })
            })
        })
    }
}

#[allow(unused)]
mod cursor_via_backard_list {
    use super::*;

    /// Like `NodeStateFwd` except flipping the fields of `Node` (the "forward" pointer is in the
    /// `Node.prev` field instead).
    struct NodeStateBwd<'this, 'next>(InvariantLifetime<'this>, InvariantLifetime<'next>);
    impl PointeePred for NodeStateBwd<'_, '_> {}
    impl<'this, 'next> PackedPredicate<'this, Node> for NodeStateBwd<'this, 'next> {
        // Question now: how to express nicely an extra wand.
        // Maybe express a pointee predicate as a VPtr<'this, NodeWithDifferentType> :thinking:.......
        // Maybe the real idea is a ptr-transmutable struct that expresses the actual recursive thing I
        // want?
        // -> no, I need to be able to express the in-between node type.
        type Unpacked = ExistsLt!(<'prev> =
            Node<Own<'prev, NodeStateBwd<'prev, 'this>>, PointsTo<'next>>
            // Node<
            //     WithSideData<
            //         Own<'prev, NodeStateBwd<'prev, 'this>>,
            //         Wand<
            //             VPtr<Own<'prev, NodeStateBwd<'prev, 'this>>, Node>,
            //             ExistsLt!(<'firstprev> = VPtr<Own<'first, NodeStateFwd<'first, 'firstprev>>, Node>),
            //         >,
            //     >,
            //     PointsTo<'next>,
            // >
            // Maybe add `IsPhantom` trait that guarantees transmutability. Impl for `PointsTo` and
            // `Wand`.
        );
    }

    /// A Node whose `prev` and `next` fields are each a forward-owned linked list with back-edges.
    /// This functions as a doubly-linked-list zipper.
    struct NodeStateCursor<'this>(InvariantLifetime<'this>);
    impl PointeePred for NodeStateCursor<'_> {}
    impl<'this> PackedPredicate<'this, Node> for NodeStateCursor<'this> {
        type Unpacked = ExistsLt!(<'prev, 'next> =
            Node<Own<'prev, NodeStateBwd<'prev, 'this>>, Own<'next, NodeStateFwd<'next, 'this>>>
        );
    }

    pub type ErasedListCursorInner = ExistsLt!(<'this, 'first> = ListCursorInner<'this, 'first>);
    pub struct ListCursorInner<'this, 'first> {
        /// Pointer to a node.
        ptr: Ptr<Own<'this, NodeStateCursor<'this>>, Node>,
        /// Pointer to the start of the list.
        first: Ptr<PointsTo<'first>, Node>,
    }

    impl<'this> ListCursorInner<'this, 'this> {
        pub fn new(ptr: Ptr<Own<'this, NodeStateFwd<'this, 'static>>, Node>) -> Self {
            let ptr = NodeStateFwd::unpack(ptr);
            ptr.unpack_target_lt(|ptr| {
                // TODO: avoid this write. needs VPtr<'static> -> VPtr<'static, Whatever> map.
                let (ptr, _) = ptr.write_field(FPrev, None);
                let ptr = pack_target_lt(ptr);
                let ptr = pack_target_lt(ptr);
                let ptr = NodeStateCursor::pack(ptr);
                let first = ptr.copy();
                ListCursorInner { ptr, first }
            })
        }
    }

    impl<'this, 'first> ListCursorInner<'this, 'first> {
        pub fn val(&self) -> &usize {
            &self.ptr.deref().val
        }
        pub fn val_mut(&mut self) -> &mut usize {
            &mut self.ptr.deref_mut().val
        }

        /// Helper.
        pub fn pack_lt(self) -> ErasedListCursorInner {
            ExistsLt::pack_lt(ExistsLt::pack_lt(self))
        }

        /// Helper: split off the forward list that includes the current node and the rest.
        fn split_after<R>(
            ptr: Ptr<Own<'this, NodeStateCursor<'this>>, Node>,
            f: impl for<'prev, 'next> FnOnce(
                Ptr<Own<'this>, Node<Own<'prev, NodeStateBwd<'prev, 'this>>, PointsTo<'next>>>,
                Option<NonEmptyList<'this>>,
            ) -> R,
        ) -> R {
            // ptr: Ptr<Own<'this, NodeStateCursor<'this>>, Node>
            // Expand the permissions to the fields of `Node`
            let ptr = NodeStateCursor::unpack(ptr);
            // Expand the lifetime
            ptr.unpack_target_lt(|ptr| {
                ptr.unpack_target_lt(|ptr| {
                    // ptr: Ptr<
                    //     Own<'this>,
                    //     Node<
                    //         Own<'prev, NodeStateBwd<'prev, 'this>>,
                    //         Own<'next, NodeStateFwd<'next, 'this>>,
                    //     >,
                    // >
                    // Extract the ownership in `next` (and get a copy of that pointer).
                    let (ptr, next) = ptr.read_field(FNext);
                    // let ptr = Node::pack_field_lt(ptr, FNext);
                    let next = next.map(|next| NonEmptyList::from_ptr(next));
                    f(ptr, next)
                })
            })
        }

        /// Helper: reverse `split_after`.
        fn unsplit_after<'prev, 'next>(
            ptr: Ptr<Own<'this>, Node<Own<'prev, NodeStateBwd<'prev, 'this>>, PointsTo<'next>>>,
            next: Option<NonEmptyList<'this>>,
        ) -> Ptr<Own<'this, NodeStateCursor<'this>>, Node> {
            let next = next.map(|next| next.into_ptr());
            ExistsLt::unpack_opt_lt(next, |next| {
                // Update `ptr.next`.
                let (ptr, _) = ptr.write_field(FNext, next);
                // Unexpand permissions
                let ptr = pack_target_lt(ptr);
                let ptr = pack_target_lt(ptr);
                NodeStateCursor::pack(ptr)
            })
        }

        /// Helper: split off the forward list that starts with the next node.
        fn split_before<R>(
            ptr: Ptr<Own<'this, NodeStateCursor<'this>>, Node>,
            f: impl for<'prev> FnOnce(
                Option<Ptr<Own<'prev, NodeStateBwd<'prev, 'this>>, Node>>,
                NonEmptyList<'prev>,
            ) -> R,
        ) -> R {
            let ptr = NodeStateCursor::unpack(ptr);
            ptr.unpack_target_lt(|ptr| {
                ptr.unpack_target_lt(|ptr| {
                    let (ptr, prev) = ptr.read_field(FPrev);
                    let ptr = pack_target_lt(ptr);
                    let ptr = NodeStateFwd::pack(ptr);
                    let list = NonEmptyList::from_ptr(ptr);
                    f(prev, list)
                })
            })
        }

        /// Helper: reverse `split_before`.
        fn unsplit_before<'prev>(
            prev: Option<Ptr<Own<'prev, NodeStateBwd<'prev, 'this>>, Node>>,
            list: NonEmptyList<'prev>,
        ) -> ExistsLt!(<'new> = Ptr<Own<'new, NodeStateCursor<'new>>, Node>) {
            list.into_ptr().unpack_lt(|ptr| {
                let ptr = NodeStateFwd::unpack(ptr);
                ptr.unpack_target_lt(|ptr| {
                    // Write to prev.next
                    let prev = prev.map(|prev| {
                        let prev = NodeStateBwd::unpack(prev);
                        prev.unpack_target_lt(|prev| {
                            let (prev, _) = prev.write_field(FNext, Some(ptr.weak_ref()));
                            let prev = pack_target_lt(prev);
                            NodeStateBwd::pack(prev)
                        })
                    });
                    let (ptr, _) = ptr.write_field(FPrev, prev);
                    let ptr = pack_target_lt(ptr);
                    let ptr = pack_target_lt(ptr);
                    let ptr = NodeStateCursor::pack(ptr);
                    ExistsLt::pack_lt(ptr)
                })
            })
        }

        pub fn insert_after(self, val: usize) -> Self {
            Self::split_after(self.ptr, |ptr, next| {
                let next = match next {
                    Some(next) => next.prepend_inner(val),
                    None => NonEmptyList::new(val, Some(ptr.weak_ref())),
                };
                let ptr = Self::unsplit_after(ptr, Some(next));
                // ptr: Ptr<ExistsLt!(Own<'_, NodeStateCursor<'_>>), Node>
                Self {
                    ptr,
                    first: self.first,
                }
            })
        }

        pub fn insert_before(self, val: usize) -> ErasedListCursorInner {
            Self::split_before(self.ptr, |prev, list| {
                let list = list.prepend_inner(val);
                Self::unsplit_before(prev, list).unpack_lt(|ptr| {
                    ListCursorInner {
                        ptr,
                        first: self.first,
                    }
                    .pack_lt()
                })
            })
        }

        pub fn remove_after(self) -> (Self, Option<usize>) {
            Self::split_after(self.ptr, |ptr, next| {
                let (next, val) = match next {
                    Some(next) => next.pop_front(),
                    None => (None, None),
                };
                let ptr = Self::unsplit_after(ptr, next);
                let this = Self {
                    ptr,
                    first: self.first,
                };
                (this, val)
            })
        }

        /// Advance the cursor. Returns `Err(self)` if the cursor could not be advanced.
        pub fn next(self) -> Result<ErasedListCursorInner, Self> {
            if self.ptr.deref().next.is_none() {
                return Err(self);
            };
            let ptr = self.ptr;
            // ptr: Ptr<Own<'this, NodeStateCursor<'this>>, Node>
            // Expand the permissions to the fields of `Node`
            let ptr = NodeStateCursor::unpack(ptr);
            // ptr: ExistsLt!(<'prev, 'next>, Ptr<
            //     Own<'this>,
            //     Node<
            //         Own<'prev, NodeStateBwd<'prev, 'this>>,
            //         Own<'next, NodeStateFwd<'next, 'this>>,
            //     >,
            // >)
            // Expand the lifetimes
            ptr.unpack_target_lt(|ptr| {
                ptr.unpack_target_lt(|ptr| {
                    // ptr: Ptr<
                    //     Own<'this>,
                    //     Node<
                    //         Own<'prev, NodeStateBwd<'prev, 'this>>,
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
                    //         Own<'prev, NodeStateBwd<'prev, 'this>>,
                    //         PointsTo<'next>,
                    //     >,
                    // >
                    // next: Ptr<Own<'next, NodeStateFwd<'next, 'this>>, Node>
                    // Unexpand the permissions
                    let ptr = pack_target_lt(ptr);
                    let ptr = NodeStateBwd::pack(ptr);
                    // ptr: Ptr<Own<'this, NodeStateBwd<'this, 'next>>, Node>
                    // Expand the permissions
                    let next = NodeStateFwd::unpack(next);
                    next.unpack_target_lt(|next| {
                        // next: Ptr<Own<'next>,
                        //    Node<
                        //      PointsTo<'this>,
                        //      Own<'nextnext, NodeStateFwd<'nextnext, 'next>>,
                        //    >,
                        // >
                        // Insert ownership
                        let next = next.write_field_permission(FPrev, ptr.into_virtual());
                        // next: Ptr<Own<'next>,
                        //    Node<
                        //      Own<'this, NodeStateBwd<'this, 'next>>,
                        //      Own<'nextnext, NodeStateFwd<'nextnext, 'next>>,
                        //    >>
                        // >
                        // Pack lifetimes
                        let next = pack_target_lt(next);
                        let next = pack_target_lt(next);
                        // TODO: here we lose info, on purpose, so that we could later change the list
                        // structure.
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
                        // Unexpand permissions
                        let next = NodeStateCursor::pack(next);
                        // next: Ptr<Own<'next, NodeStateCursor<'next>>, Node>
                        Ok((ListCursorInner {
                            ptr: next,
                            first: self.first,
                        })
                        .pack_lt())
                    })
                })
            })
        }
        /// Move the cursor backwards. Returns `Err(self)` if the cursor could not be moved.
        pub fn prev(self) -> Result<ErasedListCursorInner, Self> {
            if self.ptr.deref().prev.is_none() {
                return Err(self);
            };
            let ptr = self.ptr;
            // Expand the permissions to the fields of `Node`
            let ptr = NodeStateCursor::unpack(ptr);
            // Expand the lifetime
            ptr.unpack_target_lt(|ptr| {
                ptr.unpack_target_lt(|ptr| {
                    // Extract the ownership in `prev` (and get a copy of that pointer).
                    let (ptr, prev) = ptr.read_field(FPrev);
                    // `unwrap` is ok because we checked earlier.
                    let prev = prev.unwrap();
                    // Unexpand the permissions
                    let ptr = pack_target_lt(ptr);
                    let ptr = NodeStateFwd::pack(ptr);
                    // Expand the permissions
                    let prev = NodeStateBwd::unpack(prev);
                    prev.unpack_target_lt(|prev| {
                        // Insert ownership
                        let ptr = prev.write_field_permission(FNext, ptr.into_virtual());
                        // Pack lifetime
                        let ptr = pack_target_lt(ptr);
                        let ptr = pack_target_lt(ptr);
                        // Unexpand permissions
                        let ptr = NodeStateCursor::pack(ptr);
                        // Pack lifetime
                        Ok((ListCursorInner {
                            ptr,
                            first: self.first,
                        })
                        .pack_lt())
                    })
                })
            })
        }

        /// Converts the current pointer into a list. Assumes that this is pointing to the first
        /// element; any elements before will be lost.
        pub fn into_list(self) -> List {
            let ptr = NodeStateCursor::unpack(self.ptr);
            ptr.unpack_target_lt(|ptr| {
                ptr.unpack_target_lt(|ptr| {
                    let (ptr, _) = ptr.write_field(FPrev, None);
                    let ptr = pack_target_lt(ptr);
                    let ptr = NodeStateFwd::pack(ptr);
                    List(Some(NonEmptyList::from_ptr(ptr)))
                })
            })
        }
    }
}

// use cursor_via_backard_list::{ErasedListCursorInner, ListCursorInner};
use cursor_via_wand::{ErasedListCursorInner, ListCursorInner};
pub struct ListCursor<'a> {
    inner: Option<ErasedListCursorInner>,
    /// Borrow of the original list. While the cursor exists, the list thinks it's empty. Call
    /// `restore_list` to restore the list to the expected state.
    /// This is only `None` if we moved the value out, to prevent drop.
    list: Option<&'a mut List>,
}

impl ListCursor<'_> {
    pub fn val(&self) -> Option<&usize> {
        self.inner
            .as_ref()
            .map(|inner| inner.unpack_lt_ref(|inner| inner.unpack_lt_ref(|inner| inner.val())))
    }
    pub fn val_mut(&mut self) -> Option<&mut usize> {
        self.inner
            .as_mut()
            .map(|inner| inner.unpack_lt_mut(|inner| inner.unpack_lt_mut(|inner| inner.val_mut())))
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
            inner.unpack_lt(|inner| {
                *list = inner.into_list();
            })
        });
    }

    pub fn insert_after(mut self, val: usize) -> Self {
        if let Some(inner) = self.inner.take() {
            let inner =
                inner.unpack_lt(|inner| inner.unpack_lt(|inner| inner.insert_after(val).pack_lt()));
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

    // Panics if the list is empty, as there's nothing before which to insert.
    pub fn insert_before(mut self, val: usize) -> Self {
        let inner = self.inner.take().unwrap();
        inner.unpack_lt(|inner| {
            inner.unpack_lt(|inner| {
                let inner = inner.insert_before(val);
                Self {
                    inner: Some(inner),
                    list: self.list.take(),
                }
            })
        })
    }

    pub fn remove_after(mut self) -> (Self, Option<usize>) {
        if let Some(inner) = self.inner.take() {
            inner.unpack_lt(|inner| {
                inner.unpack_lt(|inner| {
                    let (inner, val) = inner.remove_after();
                    let this = Self {
                        inner: Some(inner.pack_lt()),
                        list: self.list.take(),
                    };
                    (this, val)
                })
            })
        } else {
            (self, None)
        }
    }

    /// Advance the cursor. Returns `Err(self)` if the cursor could not be advanced.
    pub fn next(mut self) -> Result<Self, Self> {
        if let Some(inner) = self.inner.take() {
            inner.unpack_lt(|inner| {
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
            })
        } else {
            Err(self)
        }
    }
    /// Move the cursor backwards. Returns `Err(self)` if the cursor could not be moved.
    pub fn prev(mut self) -> Result<Self, Self> {
        if let Some(inner) = self.inner.take() {
            inner.unpack_lt(|inner| {
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

#[allow(unused)]
mod cursor_via_wand {
    use super::*;
    // -> may not need the nodestates!!!!
    // -> paves the way to one-step rewinding???
    // the lifetime erasure will be a mess
    // -> hah, the output of the second wand must contain the first wand, because we need to
    // existentially erase the lifetimes together. so still need the nodestates, but with
    // side-wands instead now.
    //
    // With wands, can express cursor as:
    // ExistsLt!(<'prev> = (
    //     Ptr<Own<'this, NodeStateFwd<'this, 'prev>>, Node>,
    //     Wand<
    //         VPtr<Own<'this, NodeStateFwd<'this, 'prev>>, Node>,
    //         VPtr<Own<'prev, NodeStateCursor<'prev>>, Node>,
    //     >
    // ))
    //
    // Node<PointsTo<'prev>, Own<'next, NodeStateFwd<'next, 'this>>>
    // + Wand<Own<'this>, Own<'prev, NodeStateCursor>>
    // -> incorrect. if I modify this.prev and use the wand, the brands tell me
    // that this.prev.next.prev = this.prev which is no longer true.
    // hence the wand must enforce I don't change prev.
    // I can never change self.prev. I might be able to change it through `next.prev` tho.

    /// A cursor into a doubly-linked list. Owns the forward part of the list as normal, and uses
    /// wands to keep ownership of the previous nodes.
    // lmaooo this is an infinite backwards list x)))
    struct NodeStateWandCursor<'this>(InvariantLifetime<'this>);
    impl PointeePred for NodeStateWandCursor<'_> {}
    impl<'this> PackedPredicate<'this, Node> for NodeStateWandCursor<'this> {
        type Unpacked = ExistsLt!(<'prev> =
            Tagged<
                <NodeStateFwd<'this, 'prev> as PackedPredicate<'this, Node>>::Unpacked,
                Wand<
                    VPtr<Own<'this, NodeStateFwd<'this, 'prev>>, Node>,
                    VPtr<Own<'prev, NodeStateWandCursor<'prev>>, Node>,
                >,
            >
        );
    }

    pub type ErasedListCursorInner = ExistsLt!(<'this, 'first> = ListCursorInner<'this>);
    pub struct ListCursorInner<'this> {
        /// Pointer to a node.
        ptr: Ptr<Own<'this, NodeStateWandCursor<'this>>, Node>,
    }

    impl<'this> ListCursorInner<'this> {
        pub fn new(ptr: Ptr<Own<'this, NodeStateFwd<'this, 'static>>, Node>) -> Self {
            let ptr = NodeStateFwd::unpack(ptr);
            ptr.unpack_target_lt(|ptr| {
                let ptr = pack_target_lt(ptr);
                let wand = Wand::constant(VPtr::new_impossible());
                let ptr = ptr.tag_target(wand);
                let ptr = pack_target_lt(ptr);
                let ptr = NodeStateWandCursor::pack(ptr);
                ListCursorInner { ptr }
            })
        }
    }

    impl<'this> ListCursorInner<'this> {
        pub fn val(&self) -> &usize {
            &self.ptr.deref().val
        }
        pub fn val_mut(&mut self) -> &mut usize {
            &mut self.ptr.deref_mut().val
        }

        /// Helper.
        pub fn pack_lt(self) -> ErasedListCursorInner {
            ExistsLt::pack_lt(ExistsLt::pack_lt(self))
        }

        /// Advance the cursor, keeping the previous ownership in a wand.
        pub fn next(self) -> Result<ErasedListCursorInner, Self> {
            match Self::next_inner(self.ptr) {
                Ok(ptr) => Ok(ptr.unpack_lt(|ptr| ListCursorInner { ptr }.pack_lt())),
                Err(ptr) => Err(Self { ptr }),
            }
        }

        fn next_inner(
            ptr: Ptr<Own<'this, NodeStateWandCursor<'this>>, Node>,
        ) -> Result<
            ExistsLt!(<'next> = Ptr<Own<'next, NodeStateWandCursor<'next>>, Node>),
            Ptr<Own<'this, NodeStateWandCursor<'this>>, Node>,
        > {
            let this = ptr.copy();
            let ptr = NodeStateWandCursor::unpack(ptr);
            ptr.unpack_target_lt(|ptr| {
                let (ptr, old_wand) = ptr.untag_target();
                ptr.unpack_target_lt(|ptr| {
                    // ptr: Ptr<
                    //     Own<'this>,
                    //     Node<
                    //         PointsTo<'prev>,
                    //         Own<'next, NodeStateFwd<'next, 'this>>,
                    //     >,
                    // >
                    // Extract the ownership in `next` (and get a copy of that pointer).
                    ptr.get_field(FNext).unpack_lt(|(ptr_to_field, wand)| {
                        // ptr_to_field: Ptr<Own<'sub>, Option<Ptr<Own<'next, NodeStateFwd<'next, 'this>>, Node>>>,
                        // wand takes ptr_to_field and returns full ownership of 'this
                        let (ptr_to_field, next) = ptr_to_field.read_opt_ptr();
                        // ptr_to_field: Ptr<Own<'sub>, Option<Ptr<PointsTo<'next>, Node>>>,
                        // next: Option<Ptr<Own<'next, NodeStateFwd<'next, 'this>>, Node>>
                        match next {
                            Some(next) => {
                                let wand = ptr_to_field
                                    .into_virtual()
                                    .write_opt_ptr_perm_wand()
                                    .then(wand)
                                    .then(vpack_target_lt_wand())
                                    .then(VPtr::tag_target_wand(old_wand))
                                    // Forget that wand_output.next = this
                                    .then(vpack_target_lt_wand())
                                    .then(NodeStateWandCursor::pack_wand());
                                let next = NodeStateFwd::unpack(next);
                                let next = next.tag_target(wand);
                                let next = pack_target_lt(next);
                                let next = NodeStateWandCursor::pack(next);
                                Ok(ExistsLt::pack_lt(next))
                            }
                            None => {
                                let ptr_to_field = ptr_to_field.write(None);
                                let ptr = wand.apply(ptr_to_field.into_virtual());
                                let ptr = this.with_virtual(ptr);
                                let ptr = pack_target_lt(ptr);
                                let ptr = ptr.tag_target(old_wand);
                                let ptr = pack_target_lt(ptr);
                                let ptr = NodeStateWandCursor::pack(ptr);
                                Err(ptr)
                            }
                        }
                    })
                })
            })
        }

        /// Move the cursor backwards.
        pub fn prev(self) -> Result<ErasedListCursorInner, Self> {
            match Self::prev_inner(self.ptr) {
                Ok(ptr) => Ok(ptr.unpack_lt(|ptr| ListCursorInner { ptr }.pack_lt())),
                Err(ptr) => Err(Self { ptr }),
            }
        }

        fn prev_inner(
            ptr: Ptr<Own<'this, NodeStateWandCursor<'this>>, Node>,
        ) -> Result<
            ExistsLt!(<'prev> = Ptr<Own<'prev, NodeStateWandCursor<'prev>>, Node>),
            Ptr<Own<'this, NodeStateWandCursor<'this>>, Node>,
        > {
            let ptr = NodeStateWandCursor::unpack(ptr);
            ptr.unpack_target_lt(|ptr| {
                let (ptr, wand) = ptr.untag_target();
                ptr.unpack_target_lt(|ptr| {
                    let (ptr, prev) = ptr.read_field(FPrev);
                    match prev {
                        Some(prev) => {
                            let ptr = pack_target_lt(ptr);
                            let ptr = NodeStateFwd::pack(ptr);
                            let vprev = wand.apply(ptr.into_virtual());
                            let prev = prev.with_virtual(vprev);
                            Ok(ExistsLt::pack_lt(prev))
                        }
                        None => {
                            let ptr = pack_target_lt(ptr);
                            let ptr = ptr.tag_target(wand);
                            let ptr = pack_target_lt(ptr);
                            let ptr = NodeStateWandCursor::pack(ptr);
                            Err(ptr)
                        }
                    }
                })
            })
        }

        pub fn with_next_as_list(
            self,
            f: impl FnOnce(
                Option<NonEmptyList<'this>>,
                Ptr<PointsTo<'this>, Node>,
            ) -> Option<NonEmptyList<'this>>,
        ) -> Self {
            let ptr = NodeStateWandCursor::unpack(self.ptr);
            ptr.unpack_target_lt(|ptr| {
                let (ptr, wand) = ptr.untag_target();
                ptr.unpack_target_lt(|ptr| {
                    let (ptr, next) = ptr.read_field(FNext);
                    let next = next.map(|next| NonEmptyList::from_ptr(next));
                    let next = f(next, ptr.weak_ref());
                    let next = next.map(|next| next.into_ptr());
                    ExistsLt::unpack_opt_lt(next, |next| {
                        let (ptr, _) = ptr.write_field(FNext, next);
                        let ptr = pack_target_lt(ptr);
                        let ptr = ptr.tag_target(wand);
                        let ptr = pack_target_lt(ptr);
                        let ptr = NodeStateWandCursor::pack(ptr);
                        ListCursorInner { ptr }
                    })
                })
            })
        }

        pub fn insert_after(self, val: usize) -> Self {
            self.with_next_as_list(|next, ptr| {
                Some(match next {
                    Some(next) => next.prepend_inner(val),
                    None => NonEmptyList::new(val, Some(ptr)),
                })
            })
        }

        pub fn insert_before(self, val: usize) -> ErasedListCursorInner {
            match self.prev() {
                Ok(this) => this.unpack_lt(|this| {
                    this.unpack_lt(|this| {
                        let this = this.insert_after(val);
                        this.next().unwrap_or_else(|_| unreachable!())
                    })
                }),
                Err(this) => {
                    let mut list = this.into_list();
                    list.prepend(val);
                    list.0
                        .take()
                        .unwrap()
                        .into_ptr()
                        .unpack_lt(|ptr| ListCursorInner::new(ptr).pack_lt())
                }
            }
        }

        pub fn remove_after(self) -> (Self, Option<usize>) {
            let mut val = None;
            let this = self.with_next_as_list(|next, ptr| match next {
                Some(next) => {
                    let (next, got_val) = next.pop_front();
                    val = got_val;
                    next
                }
                None => None,
            });
            (this, val)
        }

        /// Converts the current pointer into a list. Assumes that this is pointing to the first
        /// element; any elements before will be lost.
        pub fn into_list(self) -> List {
            let ptr = NodeStateWandCursor::unpack(self.ptr);
            ptr.unpack_target_lt(|ptr| {
                let (ptr, _) = ptr.untag_target();
                ptr.unpack_target_lt(|ptr| {
                    let (ptr, _) = ptr.write_field(FPrev, None);
                    let ptr = pack_target_lt(ptr);
                    let ptr = NodeStateFwd::pack(ptr);
                    List(Some(NonEmptyList::from_ptr(ptr)))
                })
            })
        }
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
    let cursor = cursor.insert_before(43);
    let cursor = cursor.prev().unwrap();
    assert_eq!(cursor.val().unwrap(), &1);
    let cursor = cursor.prev().unwrap();
    assert_eq!(cursor.val().unwrap(), &0);
    let cursor = cursor.next().unwrap();
    drop(cursor);

    assert_eq!(list.iter().copied().collect::<Vec<_>>(), vec![0, 1, 43, 2]);
    for x in list.iter_mut() {
        *x += 1;
    }
    assert_eq!(list.iter().copied().collect::<Vec<_>>(), vec![1, 2, 44, 3]);
}
