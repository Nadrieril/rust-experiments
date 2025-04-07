use std::ptr::NonNull;

use super::*;
use crate::ExistsLt;

type ErasedNode = ExistsLt!(Node<'_>);
type Child<'this> = ExistsLt!(<'child> = Ptr<Own<'child>, Node<'child, PointsTo<'this>>>);

/// The node of a binary search tree.
struct Node<'this, Parent = NoPerm> {
    val: usize,
    left: Option<Child<'this>>,
    right: Option<Child<'this>>,
    parent: Option<Ptr<Parent, ErasedNode>>,
}

unsafe impl<'this, Parent> ErasePerms for Node<'this, Parent> {
    type Erased = ErasedNode;
}

/// Type-level tokens that represent each field of `Node`.
#[derive(Clone, Copy)]
struct FParent;
#[derive(Clone, Copy)]
struct FLeft;
#[derive(Clone, Copy)]
struct FRight;
#[derive(Clone, Copy)]
struct FVal;

unsafe impl<'this, Parent: PtrPerm> HasField<FParent> for Node<'this, Parent> {
    type FieldTy = Option<Ptr<Parent, ErasedNode>>;
    unsafe fn field_raw(
        ptr: NonNull<Self>,
        _tok: FParent,
    ) -> NonNull<Option<Ptr<Parent, ErasedNode>>> {
        unsafe { NonNull::new_unchecked(&raw mut (*ptr.as_ptr()).parent) }
    }
}
unsafe impl<'this, Parent: PtrPerm> HasGenericPermField<FParent, Parent> for Node<'this, Parent> {
    type GenericFieldTy<FieldPerm: PtrPerm> = Option<Ptr<FieldPerm, ErasedNode>>;
    type ChangePerm<NewParent: PtrPerm> = Node<'this, NewParent>;
}
unsafe impl<'this, Parent: PtrPerm> HasOptPtrField<FParent, Parent> for Node<'this, Parent> {
    type PointeeTy = ErasedNode;
}
unsafe impl<'this, Parent: PtrPerm> HasField<FVal> for Node<'this, Parent> {
    type FieldTy = usize;
    unsafe fn field_raw(ptr: NonNull<Self>, _tok: FVal) -> NonNull<Self::FieldTy> {
        unsafe { NonNull::new_unchecked(&raw mut (*ptr.as_ptr()).val) }
    }
}
unsafe impl<'this, Parent: PtrPerm> HasField<FLeft> for Node<'this, Parent> {
    type FieldTy = Option<Child<'this>>;
    unsafe fn field_raw(ptr: NonNull<Self>, _tok: FLeft) -> NonNull<Self::FieldTy> {
        unsafe { NonNull::new_unchecked(&raw mut (*ptr.as_ptr()).left) }
    }
}
unsafe impl<'this, Parent: PtrPerm> HasField<FRight> for Node<'this, Parent> {
    type FieldTy = Option<Child<'this>>;
    unsafe fn field_raw(ptr: NonNull<Self>, _tok: FRight) -> NonNull<Self::FieldTy> {
        unsafe { NonNull::new_unchecked(&raw mut (*ptr.as_ptr()).right) }
    }
}

type NormalNode<'this, 'parent> = Node<'this, PointsTo<'parent>>;

mod non_empty_tree {
    use super::*;

    pub struct NonEmptyTree<'parent>(
        ExistsLt!(<'this> = Ptr<Own<'this>, NormalNode<'this, 'parent>>),
    );

    // impl<'parent> NonEmptyTree<'parent> {
    //     pub fn insert(val: usize) -> Self {
    //         type ToAlloc<'parent> = PackLt!(Node<'_, PointsTo<'parent>>);
    //         Ptr::new_uninit::<ToAlloc<'parent>>().unpack_lt(|new| {
    //             let new = new.write(Node {
    //                 val,
    //                 children: vec![],
    //                 parent: None,
    //                 parent_id: 0,
    //             });
    //             NonEmptyTree(ExistsLt::pack_lt(new))
    //         })
    //     }
    // }
}

mod cursor_via_wand {
    use super::*;

    /// A cursor into a tree. Owns the current subtree normally and uses wands to keep ownership of
    /// the rest.
    #[repr(transparent)]
    struct CursorNode<'this, 'root>(#[allow(unused)] CursorNodeUnpacked<'this, 'root>);
    type CursorNodeUnpacked<'this, 'root> = ExistsLt!(<'parent> =
        Tagged<
            // Owned pointed-to subtree.
            NormalNode<'this, 'parent>,
            // The wand contains ownership of the previous nodes. It can be used to rewind one node or
            // rewind back to the root node.
            Wand<
                VPtr<Own<'this>, NormalNode<'this, 'parent>>,
                Choice<
                    VPtr<Own<'parent>, CursorNode<'parent, 'root>>,
                    VPtr<Own<'root>, NormalNode<'root, 'static>>,
                >,
            >,
        >
    );

    // This could be derived.
    unsafe impl<'this, 'root> TransparentWrapper for CursorNode<'this, 'root> {
        type Unwrapped = CursorNodeUnpacked<'this, 'root>;
    }
    unsafe impl<'this, 'root> ErasePerms for CursorNode<'this, 'root> {
        type Erased = <CursorNodeUnpacked<'this, 'root> as ErasePerms>::Erased;
    }

    pub type ErasedCursorInner = ExistsLt!(<'this, 'root> = CursorInner<'this, 'root>);
    pub struct CursorInner<'this, 'root> {
        /// Pointer to a subtree.
        ptr: Ptr<Own<'this>, CursorNode<'this, 'root>>,
        /// Pointer to the root of the tree.
        root: Ptr<PointsTo<'root>, ErasedNode>,
    }

    impl<'this, 'root> CursorInner<'this, 'root> {
        fn left_inner(
            ptr: Ptr<Own<'this>, CursorNode<'this, 'root>>,
        ) -> Result<
            ExistsLt!(<'next> = Ptr<Own<'next>, CursorNode<'next, 'root>>),
            Ptr<Own<'this>, CursorNode<'this, 'root>>,
        > {
            let this = ptr.copy();
            let ptr = CursorNode::unwrap(ptr);
            ptr.unpack_target_lt(|ptr| {
                let (ptr, rewind_wand) = ptr.untag_target();
                // ptr: Ptr<Own<'this>, NormalNode<'this, 'parent>>
                // rewind_wand: Wand<
                //     VPtr<Own<'this>, NormalNode<'this, 'parent>>,
                //     Choice<
                //         VPtr<Own<'parent>, CursorNode<'parent, 'root>>,
                //         VPtr<Own<'root>, NormalNode<'root, 'static>>,
                //     >,
                // >
                ptr.get_field(FLeft)
                    .unpack_lt(|(ptr_to_field, field_wand)| {
                        // ptr_to_field: Ptr<Own<'sub>, Option<Child<'this>>>,
                        // field_wand: Wand<
                        //     VPtr<Own<'sub>, Option<Child<'this>>>,
                        //     VPtr<Own<'this>, NormalNode<'this, 'parent>>
                        // >,
                        match ptr_to_field.read_opt() {
                            Ok(x) => {
                                x.unpack_lt(|(ptr_to_field, opt_wand)| {
                                    // ptr_to_field: Ptr<Own<'subsub>, Child<'this>>,
                                    // opt_wand: Wand<
                                    //     VPtr<Own<'subsub>, Child<'this>>,
                                    //     VPtr<Own<'this>, Option<Child<'this>>>
                                    // >,
                                    todo!()
                                    // let (ptr_to_field, next) = ptr_to_field.read_opt_ptr();
                                    // // ptr_to_field: Ptr<Own<'sub>, Option<Ptr<PointsTo<'next>, Node>>>,
                                    // // next: Option<Ptr<Own<'next, FwdNode<'next, 'this>>, Node>>
                                    // let wand = VPtr::pack_ty_wand()
                                    //     .then(ptr_to_field.into_virtual().write_opt_ptr_perm_wand())
                                    //     .then(wand)
                                    //     .then(vpack_target_lt_wand());
                                    // // old_wand takes 'this and returns Choice<'prev, 'first>
                                    // // wand takes 'next and returns Own<'this, FwdNode::Unpacked>
                                    // // from there we want to either apply old_wand or tag with old_wand
                                    // let wand = wand.times_constant(old_wand).then(Choice::merge(
                                    //     FwdNode::wrap_wand()
                                    //         .tensor_left()
                                    //         // Tag the 'this with the old wand.
                                    //         .then(VPtr::tag_target_wand())
                                    //         // Forget that wand_output.next = this
                                    //         .then(vpack_target_lt_wand())
                                    //         .then(CursorNode::wrap_wand()),
                                    //     // Pack the `'this` ptr.
                                    //     FwdNode::wrap_wand()
                                    //         .tensor_left()
                                    //         .then(Wand::swap_tuple())
                                    //         // Apply `old_wand` to get `Choice<'prev, 'first>`
                                    //         .then(Wand::apply_wand())
                                    //         .then(Choice::choose_right()),
                                    // ));
                                    // // Now `wand` takes 'next and returns Choice<'this, 'first>
                                    // let next = next.unpack_ty();
                                    // let next = next.tag_target(wand);
                                    // let next = pack_target_lt(next);
                                    // let next = CursorNode::wrap(next);
                                    // Ok(ExistsLt::pack_lt(next))
                                })
                            }
                            Err(ptr_to_field) => {
                                let vptr = field_wand.apply(ptr_to_field.into_virtual());
                                let ptr = this.with_virtual(vptr);
                                let ptr = ptr.tag_target(rewind_wand);
                                let ptr = pack_target_lt(ptr);
                                let ptr = CursorNode::wrap(ptr);
                                Err(ptr)
                            }
                        }
                    })
            })
        }
    }
}
