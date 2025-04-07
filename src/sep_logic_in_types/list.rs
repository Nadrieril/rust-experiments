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
struct NodeStateFwd<'this, 'prev>(#[allow(unused)] NodeStateFwdUnpacked<'this, 'prev>);
type NodeStateFwdUnpacked<'this, 'prev> = ExistsLt!(<'next> =
    Node<PointsTo<'prev>, Own<'next, NodeStateFwd<'next, 'this>>>
);

impl PointeePred for NodeStateFwd<'_, '_> {}
impl<'this, 'prev> PackedPredicate<'this, Node> for NodeStateFwd<'this, 'prev> {
    type Unpacked = NodeStateFwdUnpacked<'this, 'prev>;
}

/// A cursor into a doubly-linked list. Owns the forward part of the list as normal, and uses
/// wands to keep ownership of the previous nodes.
struct NodeStateWandCursor<'this, 'first>(
    #[allow(unused)] NodeStateWandCursorUnpacked<'this, 'first>,
);
type NodeStateWandCursorUnpacked<'this, 'first> = ExistsLt!(<'prev> =
    Tagged<
        NodeStateFwdUnpacked<'this, 'prev>,
        Wand<
            VPtr<Own<'this, NodeStateFwd<'this, 'prev>>, Node>,
            Choice<
                VPtr<Own<'prev, NodeStateWandCursor<'prev, 'first>>, Node>,
                VPtr<Own<'first, NodeStateFwd<'first, 'static>>, Node>,
            >,
        >,
    >
);
impl PointeePred for NodeStateWandCursor<'_, '_> {}
impl<'this, 'first> PackedPredicate<'this, Node> for NodeStateWandCursor<'this, 'first> {
    type Unpacked = NodeStateWandCursorUnpacked<'this, 'first>;
}

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

mod cursor_via_wand {
    use super::*;

    pub type ErasedListCursorInner = ExistsLt!(<'this, 'first> = ListCursorInner<'this, 'first>);
    pub struct ListCursorInner<'this, 'first> {
        /// Pointer to a node.
        ptr: Ptr<Own<'this, NodeStateWandCursor<'this, 'first>>, Node>,
        /// Pointer to the start of the list.
        first: Ptr<PointsTo<'first>, Node>,
    }

    impl<'this> ListCursorInner<'this, 'this> {
        pub fn new(ptr: Ptr<Own<'this, NodeStateFwd<'this, 'static>>, Node>) -> Self {
            let ptr = NodeStateFwd::unpack(ptr);
            ptr.unpack_target_lt(|ptr| {
                let ptr = pack_target_lt(ptr);
                let wand = Choice::merge(Wand::constant(VPtr::new_impossible()), Wand::id());
                let ptr = ptr.tag_target(wand);
                let ptr = pack_target_lt(ptr);
                let ptr = NodeStateWandCursor::pack(ptr);
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

        /// Advance the cursor, keeping the previous ownership in a wand.
        pub fn next(self) -> Result<ErasedListCursorInner, Self> {
            match Self::next_inner(self.ptr) {
                Ok(ptr) => Ok(ptr.unpack_lt(|ptr| {
                    ListCursorInner {
                        ptr,
                        first: self.first,
                    }
                    .pack_lt()
                })),
                Err(ptr) => Err(Self {
                    ptr,
                    first: self.first,
                }),
            }
        }

        fn next_inner(
            ptr: Ptr<Own<'this, NodeStateWandCursor<'this, 'first>>, Node>,
        ) -> Result<
            ExistsLt!(<'next> = Ptr<Own<'next, NodeStateWandCursor<'next, 'first>>, Node>),
            Ptr<Own<'this, NodeStateWandCursor<'this, 'first>>, Node>,
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
                                    .then(vpack_target_lt_wand());
                                // old_wand takes 'this and returns Choice<'prev, 'first>
                                // wand takes 'next and returns Own<'this, NodeStateFwd::Unpacked>
                                // from there we want to either apply old_wand or tag with old_wand
                                let wand = wand.times_constant(old_wand).then(Choice::merge(
                                    // Tag the 'this with the old wand.
                                    VPtr::tag_target_wand()
                                        // Forget that wand_output.next = this
                                        .then(vpack_target_lt_wand())
                                        .then(NodeStateWandCursor::pack_wand()),
                                    // Pack the `'this` ptr.
                                    NodeStateFwd::pack_wand()
                                        .tensor_left()
                                        .then(Wand::swap_tuple())
                                        // Apply `old_wand` to get `Choice<'prev, 'first>`
                                        .then(Wand::apply_wand())
                                        .then(Choice::choose_right()),
                                ));
                                // Now `wand` takes 'next and returns Choice<'this, 'first>
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
                Ok(ptr) => Ok(ptr.unpack_lt(|ptr| {
                    ListCursorInner {
                        ptr,
                        first: self.first,
                    }
                    .pack_lt()
                })),
                Err(ptr) => Err(Self {
                    ptr,
                    first: self.first,
                }),
            }
        }

        fn prev_inner(
            ptr: Ptr<Own<'this, NodeStateWandCursor<'this, 'first>>, Node>,
        ) -> Result<
            ExistsLt!(<'prev> = Ptr<Own<'prev, NodeStateWandCursor<'prev, 'first>>, Node>),
            Ptr<Own<'this, NodeStateWandCursor<'this, 'first>>, Node>,
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
                            let choice = wand.apply(ptr.into_virtual());
                            let vprev = Choice::choose_left().apply(choice);
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
                        ListCursorInner {
                            ptr,
                            first: self.first,
                        }
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
            let this = self.with_next_as_list(|next, _ptr| match next {
                Some(next) => {
                    let (next, got_val) = next.pop_front();
                    val = got_val;
                    next
                }
                None => None,
            });
            (this, val)
        }

        fn rewind(self) -> Ptr<Own<'first, NodeStateFwd<'first, 'static>>, Node> {
            let ptr = NodeStateWandCursor::unpack(self.ptr);
            ptr.unpack_target_lt(|ptr| {
                let (ptr, wand) = ptr.untag_target();
                let ptr = NodeStateFwd::pack(ptr);
                let vfirst = wand.then(Choice::choose_right()).apply(ptr.into_virtual());
                self.first.with_virtual(vfirst)
            })
        }
        /// Recover the original list.
        pub fn into_list(self) -> List {
            let first = self.rewind();
            List(Some(NonEmptyList::from_ptr(first)))
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
