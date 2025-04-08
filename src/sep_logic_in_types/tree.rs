use std::ptr::NonNull;

use super::*;
use crate::ExistsLt;

type ErasedNode = ExistsLt!(Node<'_>);
type NormalNode<'this, 'parent> = Node<'this, PointsTo<'parent>>;
type Child<'this> = ExistsLt!(<'child> = Ptr<Own<'child>, NormalNode<'child, 'this>>);

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
// TODO: can I be generic in just a brand instead?
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

impl<'this, Parent: PtrPerm> Node<'this, Parent> {
    fn read_child<Perm, FieldTok>(
        self: Ptr<Perm, Self>,
        tok: FieldTok,
    ) -> Result<
        ExistsLt!(<'child> = (
           Ptr<AccessThroughType<'child, Perm, Own<'child>>, NormalNode<'child, 'this>>,
           Wand<
               VPtr<AccessThroughType<'child, Perm, Own<'child>>, NormalNode<'child, 'this>>,
               VPtr<Perm, Self>
           >
        )),
        Ptr<Perm, Self>,
    >
    where
        Perm: HasRead<'this>,
        FieldTok: Copy,
        Self: HasField<FieldTok, FieldTy = Option<Child<'this>>>,
        for<'child> <Own<'child> as HasAccess>::Access: AccessThrough<Perm::Access>,
    {
        // self: Ptr<Perm, Node<'this, Parent>>
        let this = self.copy();
        self.get_field(tok).unpack_lt(|(ptr_to_field, field_wand)| {
            // ptr_to_field: Ptr<PointsTo<'sub, Access>, Option<Child<'this>>>,
            // field_wand: Wand<
            //     VPtr<PointsTo<'sub, Access>, Option<Child<'this>>>,
            //     VPtr<Perm, Node<'this, Parent>>
            // >,
            match ptr_to_field.read_opt() {
                Ok(x) => {
                    x.unpack_lt(|(ptr_to_field, opt_wand)| {
                        // ptr_to_field: Ptr<PointsTo<'subsub, Access>, Child<'this>>,
                        // opt_wand: Wand<
                        //     VPtr<PointsTo<'subsub, Access>, Child<'this>>,
                        //     VPtr<PointsTo<'sub, Access>, Option<Child<'this>>>
                        // >,
                        ptr_to_field.unpack_target_lt(|ptr_to_field| {
                            // ptr_to_field: Ptr<PointsTo<'subsub, Access>, Ptr<Own<'child>, NormalNode<'child, 'this>>>,
                            let (ptr_to_field, child) = ptr_to_field.read_nested_ptr();
                            // ptr_to_field: Ptr<PointsTo<'subsub, Access>, Ptr<PointsTo<'child>, NormalNode<'child, 'this>>>,
                            // child: Ptr<AccessThroughType<'child, Perm, Own<'child>>, NormalNode<'child, 'this>>
                            let wand = ptr_to_field
                                .into_virtual()
                                .write_nested_ptr_wand()
                                .then(vpack_target_lt_wand())
                                .then(opt_wand)
                                .then(field_wand);
                            Ok(ExistsLt::pack_lt((child, wand)))
                        })
                    })
                }
                Err(ptr_to_field) => {
                    let vptr = field_wand.apply(ptr_to_field.into_virtual());
                    let ptr = this.with_virtual(vptr);
                    Err(ptr)
                }
            }
        })
    }
}

pub use tree::Tree;
mod tree {
    use crate::sep_logic_in_types::tree::cursor_via_wand::Cursor;

    use super::{cursor_via_wand::ErasedCursor, *};

    struct NonEmptyTree<'parent>(pub Child<'parent>);

    pub fn alloc_node<'parent>(
        parent: Option<Ptr<PointsTo<'parent>, ErasedNode>>,
        val: usize,
    ) -> Child<'parent> {
        type ToAlloc<'this> = PackLt!(<'new> = NormalNode<'new, 'this>);
        Ptr::new_uninit::<ToAlloc<'_>>().unpack_lt(|new| {
            ExistsLt::pack_lt(new.write(Node {
                val,
                left: None,
                right: None,
                parent,
            }))
        })
    }
    impl NonEmptyTree<'static> {
        fn new(val: usize) -> Self {
            Self(alloc_node(None, val))
        }
        fn cursor(self) -> ErasedCursor {
            self.0.unpack_lt(|ptr| Cursor::new(ptr).pack_lt())
        }
        fn insert(self, val: usize) -> Self {
            self.cursor().unpack_lt(|cursor| {
                cursor.unpack_lt(|cursor| {
                    cursor
                        .insert(val)
                        .unpack_lt(|cursor| cursor.unpack_lt(|cursor| Self(cursor.rewind())))
                })
            })
        }
        /// Traverse in-order. The closure gets each element and the current depth.
        fn traverse<'a>(&'a self, f: impl FnMut(&'a usize, usize)) {
            self.0.unpack_lt_ref(|ptr| {
                iter::TreeRef::from_ptr(ptr.copy_read()).traverse(f);
            })
        }
    }

    pub struct Tree {
        tree: Option<NonEmptyTree<'static>>,
    }

    impl Tree {
        pub fn new() -> Self {
            Tree { tree: None }
        }
        pub fn insert(&mut self, val: usize) {
            self.tree = Some(match self.tree.take() {
                Some(tree) => tree.insert(val),
                None => NonEmptyTree::new(val),
            })
        }
        /// Traverse in-order. The closure gets each element and the current depth.
        pub fn traverse<'a>(&'a self, f: impl FnMut(&'a usize, usize)) {
            if let Some(t) = &self.tree {
                t.traverse(f);
            }
        }
    }
}

mod cursor_via_wand {
    use crate::sep_logic_in_types::tree::tree::alloc_node;

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

    pub type ErasedCursor = ExistsLt!(<'this, 'root> = Cursor<'this, 'root>);
    pub struct Cursor<'this, 'root> {
        /// Pointer to a subtree.
        ptr: Ptr<Own<'this>, CursorNode<'this, 'root>>,
        /// Pointer to the root of the tree.
        root: Ptr<PointsTo<'root>, ErasedNode>,
    }

    impl<'this, 'root> Cursor<'this, 'root> {
        pub fn val(&self) -> &usize {
            let ptr = self.ptr.copy_read();
            let ptr = CursorNode::unwrap(ptr);
            ptr.unpack_target_lt(|ptr| {
                ptr.ignore_tag()
                    .get_field(FVal)
                    .unpack_lt(|(ptr_to_field, _)| ptr_to_field.deref_exact())
            })
        }
        #[expect(unused)]
        pub fn val_mut(&mut self) -> &mut usize {
            let ptr = self.ptr.copy_mut();
            let ptr = CursorNode::unwrap(ptr);
            ptr.unpack_target_lt(|ptr| {
                ptr.ignore_tag()
                    .get_field(FVal)
                    .unpack_lt(|(ptr_to_field, _)| ptr_to_field.into_deref_mut())
            })
        }

        /// Insert this value into the current (sorted) subtree. The returned cursor points to the
        /// parent of the newly-added node.
        pub fn insert(self, val: usize) -> ErasedCursor {
            let go_right = val >= *self.val();
            let moved = if go_right {
                self.go_right()
            } else {
                self.go_left()
            };
            // Try to move in the direction the value should go. If we can, recurse, otherwise
            // create a new node.
            match moved {
                Ok(child) => child.unpack_lt(|child| child.unpack_lt(|child| child.insert(val))),
                Err(this) => this
                    .map_subtree(|ptr| {
                        let child = alloc_node(Some(ptr.weak_ref()), val);
                        if go_right {
                            ptr.map_field(FRight, |field| field.write(Some(child)))
                        } else {
                            ptr.map_field(FLeft, |field| field.write(Some(child)))
                        }
                    })
                    .pack_lt(),
            }
        }

        /// Helper.
        fn map_subtree(
            self,
            f: impl for<'parent> FnOnce(
                Ptr<Own<'this>, NormalNode<'this, 'parent>>,
            ) -> Ptr<Own<'this>, NormalNode<'this, 'parent>>,
        ) -> Self {
            let ptr = CursorNode::unwrap(self.ptr);
            ptr.unpack_target_lt(|ptr| {
                let (ptr, wand) = ptr.untag_target();
                let ptr = f(ptr);
                let ptr = ptr.tag_target(wand);
                let ptr = pack_target_lt(ptr);
                let ptr = CursorNode::wrap(ptr);
                Cursor {
                    ptr,
                    root: self.root,
                }
            })
        }
    }

    impl<'this> Cursor<'this, 'this> {
        pub fn new(ptr: Ptr<Own<'this>, NormalNode<'this, 'static>>) -> Self {
            let root = ptr.weak_ref();
            let wand = Choice::merge(Wand::constant(VPtr::new_impossible()), Wand::id());
            let ptr = ptr.tag_target(wand);
            let ptr = pack_target_lt(ptr);
            let ptr = CursorNode::wrap(ptr);
            Cursor { ptr, root }
        }
    }

    impl<'this, 'root> Cursor<'this, 'root> {
        /// Helper.
        pub fn pack_lt(self) -> ErasedCursor {
            ExistsLt::pack_lt(ExistsLt::pack_lt(self))
        }

        pub fn go_left(self) -> Result<ErasedCursor, Self> {
            self.go_child(FLeft)
        }
        pub fn go_right(self) -> Result<ErasedCursor, Self> {
            self.go_child(FRight)
        }
        /// Move the cursor to the given child.
        fn go_child<FieldTok>(self, tok: FieldTok) -> Result<ErasedCursor, Self>
        where
            FieldTok: Copy,
            for<'parent> NormalNode<'this, 'parent>:
                HasField<FieldTok, FieldTy = Option<Child<'this>>>,
        {
            let ptr = CursorNode::unwrap(self.ptr);
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
                match ptr.read_child(tok) {
                    Ok(x) => {
                        x.unpack_lt(|(child, child_wand)| {
                            // child: Ptr<Own<'child>, NormalNode<'child, 'this>>,
                            // child_wand: Wand<
                            //     VPtr<Own<'child>, NormalNode<'child, 'this>>,
                            //     VPtr<Own<'this>, Self>
                            // >
                            // Wand input: VPtr<Own<'child>, NormalNode<'child, 'this>>
                            let wand = child_wand
                                // VPtr<Own<'this>, NormalNode<'this, 'parent>>
                                .times_constant(rewind_wand)
                                // (VPtr<...>, Wand<...>)
                                .then(Choice::merge(
                                    // Pack the wand to get a `CursorNode` back.
                                    VPtr::tag_target_wand()
                                        .then(vpack_target_lt_wand())
                                        .then(CursorNode::wrap_wand()),
                                    // Apply `rewind_wand` to get `Choice<'prev, 'first>`
                                    Wand::swap_tuple()
                                        .then(Wand::apply_wand())
                                        .then(Choice::choose_right()),
                                ));
                            // wand: Wand<
                            //     VPtr<Own<'child>, NormalNode<'child, 'this>>,
                            //     Choice<
                            //         VPtr<Own<'this>, CursorNode<'this, 'root>>,
                            //         VPtr<Own<'root>, NormalNode<'root, 'static>>,
                            //     >,
                            // >
                            let child = child.tag_target(wand);
                            let child = pack_target_lt(child);
                            let child = CursorNode::wrap(child);
                            Ok(Cursor {
                                ptr: child,
                                root: self.root,
                            }
                            .pack_lt())
                        })
                    }
                    Err(ptr) => {
                        // No child, repack the pointer into a cursor node pointer.
                        let ptr = ptr.tag_target(rewind_wand);
                        let ptr = pack_target_lt(ptr);
                        let ptr = CursorNode::wrap(ptr);
                        return Err(Cursor {
                            ptr,
                            root: self.root,
                        });
                    }
                }
            })
        }

        /// Move the cursor to the parent node.
        #[expect(unused)]
        pub fn parent(self) -> Result<ErasedCursor, Self> {
            let ptr = CursorNode::unwrap(self.ptr);
            ptr.unpack_target_lt(|ptr| {
                let (ptr, rewind_wand) = ptr.untag_target();
                let (ptr, parent) = ptr.read_field(FParent);
                match parent {
                    Some(parent) => {
                        let choice = rewind_wand.apply(ptr.into_virtual());
                        let vparent = Choice::choose_left().apply(choice);
                        let parent = parent.with_virtual(vparent);
                        Ok(Cursor {
                            ptr: parent,
                            root: self.root,
                        }
                        .pack_lt())
                    }
                    None => {
                        let ptr = ptr.tag_target(rewind_wand);
                        let ptr = pack_target_lt(ptr);
                        let ptr = CursorNode::wrap(ptr);
                        Err(Cursor {
                            ptr,
                            root: self.root,
                        })
                    }
                }
            })
        }

        /// Recover ownership of the tree root.
        pub fn rewind(self) -> Child<'static> {
            let ptr = CursorNode::unwrap(self.ptr);
            ptr.unpack_target_lt(|ptr| {
                let (ptr, wand) = ptr.untag_target();
                let vroot = wand.then(Choice::choose_right()).apply(ptr.into_virtual());
                let root = self.root.with_virtual(vroot);
                ExistsLt::pack_lt(root)
            })
        }
    }
}

mod iter {
    use super::*;

    // In-order traversal
    pub struct TreeRef<'a>(
        ExistsLt!(<'this, 'parent> = Ptr<Read<'this, 'a>, NormalNode<'this, 'parent>>),
    );

    impl<'a> TreeRef<'a> {
        pub fn from_ptr<'this, 'parent>(
            ptr: Ptr<Read<'this, 'a>, NormalNode<'this, 'parent>>,
        ) -> Self {
            Self(ExistsLt::pack_lt(ExistsLt::pack_lt(ptr)))
        }

        /// Traverse in-order. The closure gets each element and the current depth.
        pub fn traverse(self, mut f: impl FnMut(&'a usize, usize)) {
            self.traverse_inner(&mut f, 0);
        }
        fn traverse_inner(self, f: &mut impl FnMut(&'a usize, usize), depth: usize) {
            self.0.unpack_lt(|ptr| {
                ptr.unpack_lt(|ptr| {
                    if let Ok(x) = ptr.copy_read_same_lifetime().read_child(FLeft) {
                        x.unpack_lt(|(child, _)| {
                            // child: Ptr<Read<'child, 'a>, NormalNode<'child, 'this>>,
                            TreeRef::from_ptr(child).traverse_inner(f, depth + 1);
                        })
                    }
                    ptr.copy_read_same_lifetime()
                        .get_field(FVal)
                        .unpack_lt(|(val_ptr, _)| {
                            let val = val_ptr.deref_exact();
                            f(val, depth);
                        });
                    if let Ok(x) = ptr.copy_read_same_lifetime().read_child(FRight) {
                        x.unpack_lt(|(child, _)| {
                            // child: Ptr<Read<'child, 'a>, NormalNode<'child, 'this>>,
                            TreeRef::from_ptr(child).traverse_inner(f, depth + 1);
                        })
                    }
                })
            })
        }
    }
}

#[test]
fn test_tree() {
    fn assert_tree(t: &Tree, shape: &[&str]) {
        let mut iter = shape.iter();
        t.traverse(|val, depth| {
            let expected = iter.next().unwrap();
            let actual = format!("{}{val}", " ".repeat(depth));
            assert_eq!(expected, &actual)
        });
    }
    let mut tree = Tree::new();
    tree.insert(5);
    tree.insert(3);
    tree.insert(7);
    tree.insert(1);
    tree.insert(4);
    tree.insert(6);
    tree.insert(9);
    tree.insert(2);
    tree.insert(8);
    assert_tree(
        &tree,
        &["  1", "   2", " 3", "  4", "5", "  6", " 7", "   8", "  9"],
    );
}
