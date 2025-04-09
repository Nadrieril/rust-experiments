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

/// Which branch of a node.
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Branch {
    Left,
    Right,
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
    use super::{
        external_wand_cursor::{Cursor, CursorInner},
        iter::Iter,
        *,
    };

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
        fn cursor(self) -> Cursor {
            self.0.unpack_lt(|ptr| CursorInner::new(ptr).pack_lt())
        }
        fn insert(self, val: usize) -> Self {
            self.cursor().unpack_lt(|cursor| {
                cursor.insert(val).unpack_lt(|cursor| {
                    let root = cursor.rewind();
                    Self(ExistsLt::pack_lt(root))
                })
            })
        }
        fn iter<'a>(&'a self) -> Iter<'a> {
            let cursor = self
                .0
                .unpack_lt_ref(|ptr| CursorInner::new(ptr.copy_read()).pack_lt());
            Iter::new(cursor)
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
        pub fn iter<'a>(&'a self) -> Iter<'a> {
            match &self.tree {
                Some(tree) => tree.iter(),
                None => Iter::new_empty(),
            }
        }
    }
}

mod external_wand_cursor {
    use super::{tree::alloc_node, *};

    /// Recursive wand to walk up the tree.
    #[repr(transparent)]
    struct Rewind<'this, 'parent, 'root, Access: PtrAccess>(
        RewindUnwrapped<'this, 'parent, 'root, Access>,
    );
    type RewindUnwrapped<'this, 'parent, 'root, Access> = Wand<
        VPtr<PointsTo<'this, Access>, NormalNode<'this, 'parent>>,
        Choice<
            IfReal<
                'parent,
                ExistsLt!(<'parent_parent> = (
                    VPtr<PointsTo<'parent, Access>, NormalNode<'parent, 'parent_parent>>,
                    Rewind<'parent, 'parent_parent, 'root, Access>,
                )),
            >,
            VPtr<PointsTo<'root, Access>, NormalNode<'root, 'static>>,
        >,
    >;

    // This could be derived.
    unsafe impl<'this, 'parent, 'root, Access: PtrAccess> TransparentWrapper
        for Rewind<'this, 'parent, 'root, Access>
    {
        type Unwrapped = RewindUnwrapped<'this, 'parent, 'root, Access>;
    }
    unsafe impl<Access: PtrAccess> Phantom for Rewind<'_, '_, '_, Access> {}

    pub struct CursorInner<'this, 'parent, 'root, Access: PtrAccess> {
        /// Pointer to the subtree.
        pub ptr: Ptr<PointsTo<'this, Access>, NormalNode<'this, 'parent>>,
        /// Recursive wand to walk up the tree.
        rewind: Rewind<'this, 'parent, 'root, Access>,
        /// Pointer to the root of the tree.
        root: Ptr<PointsTo<'root>, ErasedNode>,
    }

    impl<'this, Access: PtrAccess> CursorInner<'this, 'static, 'this, Access> {
        pub fn new(ptr: Ptr<PointsTo<'this, Access>, NormalNode<'this, 'static>>) -> Self {
            let root = ptr.weak_ref();
            let wand = Choice::merge(Wand::constant(IfReal::not_real()), Wand::id());
            let rewind = Rewind(wand);
            CursorInner { ptr, rewind, root }
        }
    }

    impl<'this, 'parent, 'root, Access: AtLeastRead> CursorInner<'this, 'parent, 'root, Access>
    where
        // This should always be true but we can't prove it
        POwn: AccessThrough<Access, AccessThrough = Access>,
    {
        pub fn copy_ptr(&self) -> Ptr<PointsTo<'this>, NormalNode<'this, 'parent>> {
            self.ptr.copy()
        }
        pub fn node(&self) -> &NormalNode<'this, 'parent> {
            self.ptr.deref()
        }
        pub fn node_mut(&mut self) -> &mut NormalNode<'this, 'parent>
        where
            Access: AtLeastMut,
        {
            self.ptr.deref_mut()
        }
        pub fn val(&self) -> &usize {
            &self.node().val
        }
        #[expect(unused)]
        pub fn val_mut(&mut self) -> &mut usize
        where
            Access: AtLeastMut,
        {
            &mut self.node_mut().val
        }

        /// Insert this value into the current (sorted) subtree. The returned cursor points to the
        /// parent of the newly-added node.
        pub fn insert(self, val: usize) -> Cursor<Access>
        where
            Access: AtLeastOwn,
        {
            let direction = if val >= *self.val() {
                Branch::Right
            } else {
                Branch::Left
            };
            // Try to move in the direction the value should go. If we can, recurse, otherwise
            // create a new node.
            match self.descend(direction) {
                Ok(child) => child.unpack_lt(|child| child.insert(val)),
                Err(mut this) => {
                    let child = alloc_node(Some(this.ptr.weak_ref()), val);
                    if direction == Branch::Right {
                        *this.ptr.deref_mut().field_mut(FRight) = Some(child);
                    } else {
                        *this.ptr.deref_mut().field_mut(FLeft) = Some(child);
                    }
                    this.pack_lt()
                }
            }
        }
    }

    impl<'this, 'parent, 'root, Access: AtLeastRead> CursorInner<'this, 'parent, 'root, Access>
    where
        // This should always be true but we can't prove it
        POwn: AccessThrough<Access, AccessThrough = Access>,
    {
        pub fn pack_lt(self) -> Cursor<Access> {
            Cursor(ExistsLt::pack_lt(ExistsLt::pack_lt(ExistsLt::pack_lt(
                self,
            ))))
        }

        /// Move the cursor to the given child.
        pub fn descend(self, branch: Branch) -> Result<Cursor<Access>, Self> {
            let Self { rewind, ptr, root } = self;
            let read_child = match branch {
                Branch::Left => ptr.read_child(FLeft),
                Branch::Right => ptr.read_child(FRight),
            };
            match read_child {
                Ok(x) => {
                    x.unpack_lt(|(child, child_wand)| {
                        // child: Ptr<PointsTo<'child, Access>, NormalNode<'child, 'this>>,
                        // child_wand: Wand<
                        //     VPtr<PointsTo<'child, Access>, NormalNode<'child, 'this>>,
                        //     VPtr<PointsTo<'this, Access>, NormalNode<'this, 'parent>>
                        // >
                        // Wand input: VPtr<PointsTo<'child, Access>, NormalNode<'child, 'this>>
                        let wand = child_wand
                            // VPtr<PointsTo<'this, Access>, NormalNode<'this, 'parent>>
                            .times_constant(rewind)
                            // (VPtr<...>, Rewind<...>)
                            .then(Choice::merge(
                                ExistsLt::pack_lt_wand().then(IfReal::lock_wand()),
                                Wand::swap_tuple()
                                    .then(Wand::tensor_left(Rewind::unwrap_wand()))
                                    // Apply the wand to get `Choice<'parent, 'root>`
                                    .then(Wand::apply_wand())
                                    // Choose the root
                                    .then(Choice::choose_right()),
                            ));
                        let cursor = CursorInner {
                            rewind: Rewind(wand),
                            ptr: child,
                            root,
                        };
                        Ok(cursor.pack_lt())
                    })
                }
                Err(ptr) => Err(Self { rewind, ptr, root }),
            }
        }

        /// Move the cursor to the parent node.
        pub fn ascend(self) -> Result<Cursor<Access>, Self>
        where
            POwn: AccessThrough<Access>,
        {
            match *self.ptr.deref().field_ref(FParent) {
                None => Err(self),
                Some(parent) => {
                    let Self { rewind, ptr, root } = self;
                    let Rewind(wand) = rewind;
                    wand.then(Choice::choose_left())
                        .apply(ptr.into_virtual())
                        .unlock(parent.weak_ref())
                        .unpack_lt(|(vparent, rewind)| {
                            let cursor = CursorInner {
                                rewind,
                                ptr: parent.with_virtual(vparent),
                                root,
                            };
                            Ok(cursor.pack_lt())
                        })
                }
            }
        }

        /// Recover ownership of the tree root.
        pub fn rewind(self) -> Ptr<PointsTo<'root, Access>, NormalNode<'root, 'static>> {
            let vroot = self
                .rewind
                .0
                .then(Choice::choose_right())
                .apply(self.ptr.into_virtual());
            self.root.with_virtual(vroot)
        }
    }

    pub struct Cursor<Access: PtrAccess = POwn>(
        ExistsLt!(<'this, 'parent, 'root> = CursorInner<'this, 'parent, 'root, Access>),
    );
    impl<Access: PtrAccess> Cursor<Access> {
        pub fn unpack_lt<R>(
            self,
            f: impl for<'this, 'parent, 'root> FnOnce(CursorInner<'this, 'parent, 'root, Access>) -> R,
        ) -> R {
            self.0
                .unpack_lt(|cursor| cursor.unpack_lt(|cursor| cursor.unpack_lt(f)))
        }
        pub fn unpack_lt_ref<'a, R>(
            &'a self,
            f: impl for<'this, 'parent, 'root> FnOnce(
                &'a CursorInner<'this, 'parent, 'root, Access>,
            ) -> R,
        ) -> R {
            self.0
                .unpack_lt_ref(|cursor| cursor.unpack_lt_ref(|cursor| cursor.unpack_lt_ref(f)))
        }
    }
    impl<Access: AtLeastRead> Cursor<Access>
    where
        // This should always be true but we can't prove it
        POwn: AccessThrough<Access, AccessThrough = Access>,
    {
        pub fn descend(self, branch: Branch) -> Result<Self, Self> {
            self.unpack_lt(|cursor| cursor.descend(branch).map_err(CursorInner::pack_lt))
        }
        pub fn ascend(self) -> Result<Self, Self>
        where
            POwn: AccessThrough<Access>,
        {
            self.unpack_lt(|cursor| cursor.ascend().map_err(CursorInner::pack_lt))
        }
        pub fn rewind(
            self,
        ) -> ExistsLt!(<'root> = Ptr<PointsTo<'root, Access>, NormalNode<'root, 'static>>) {
            self.unpack_lt(|cursor| ExistsLt::pack_lt(cursor.rewind()))
        }
    }
}

mod iter {
    use super::{external_wand_cursor::Cursor, *};

    /// Pointer to an edge within the tree.
    pub struct EdgeHandle<Access: PtrAccess> {
        /// Cursor into the tree.
        cursor: Cursor<Access>,
        /// Depth of the pointed-to node.
        depth: usize,
    }

    impl<Access: AtLeastRead> EdgeHandle<Access>
    where
        // This should always be true but we can't prove it
        POwn: AccessThrough<Access, AccessThrough = Access>,
    {
        /// Make a handle on the given subtree. The handle will start on the leftmost node of that
        /// subtree.
        pub fn new(mut cursor: Cursor<Access>, mut depth: usize) -> Self {
            // Start with the leftmost node.
            let cursor = loop {
                match cursor.descend(Branch::Left) {
                    Ok(c) => {
                        depth += 1;
                        cursor = c
                    }
                    Err(c) => break c,
                }
            };
            Self { cursor, depth }
        }

        pub fn next(
            self,
        ) -> Result<
            Self,
            ExistsLt!(<'root> = Ptr<PointsTo<'root, Access>, NormalNode<'root, 'static>>),
        > {
            let Self { cursor, mut depth } = self;
            // If we can move right, go to that subtree. If we can't, go parent until we're coming
            // from a left node.
            match cursor.descend(Branch::Right) {
                Ok(cursor) => Ok(Self::new(cursor, depth + 1)),
                Err(mut cursor) => {
                    loop {
                        let prev_node = cursor.unpack_lt_ref(|cursor| {
                            cursor.copy_ptr().erase_target_perms().noperm()
                        });
                        let parent = cursor.ascend().map_err(|root| root.rewind())?;
                        depth = depth - 1;
                        let coming_from_left =
                            parent.unpack_lt_ref(|parent| {
                                parent.node().left.as_ref().is_some_and(|ptr| {
                                    ptr.unpack_lt_ref(|ptr| ptr.addr_eq(&prev_node))
                                })
                            });
                        if coming_from_left {
                            // We're coming from the left, hence the new node comes
                            // after the nodes we've seen so far.
                            return Ok(Self {
                                cursor: parent,
                                depth,
                            });
                        } else {
                            // We're coming from the right, we must keep going up.
                            cursor = parent;
                        }
                    }
                }
            }
        }
    }

    // TODO: mutable/by-val iterator.
    // TODO: I must relinquish access to the already-visited nodes if I want to return mut refs.
    // Hence must be able to represent this. Could go with access generics, but that won't work for
    // btree. how tf do I represent a list of pointers, some of which have been invalidated??
    pub struct Iter<'a>(Option<EdgeHandle<PRead<'a>>>);

    impl<'a> Iter<'a> {
        pub(super) fn new_empty() -> Self {
            Iter(None)
        }
        pub(super) fn new(cursor: Cursor<PRead<'a>>) -> Self {
            Iter(Some(EdgeHandle::new(cursor, 0)))
        }
    }

    impl<'a> Iterator for Iter<'a> {
        type Item = (&'a usize, usize);
        fn next(&mut self) -> Option<Self::Item> {
            let handle = self.0.take()?;
            let depth = handle.depth;
            let val = handle.cursor.unpack_lt_ref(|cursor| {
                cursor
                    .ptr
                    .get_field(FVal)
                    .unpack_lt(|(ptr, _)| ptr.deref_exact())
            });
            self.0 = handle.next().ok();
            Some((val, depth))
        }
    }
}

#[test]
fn test_tree() {
    fn assert_tree(t: &Tree, expected: &[&str]) {
        t.iter()
            .map(|(val, depth)| format!("{}{val}", " ".repeat(depth)))
            .zip(expected)
            .for_each(|(actual, expected)| assert_eq!(expected, &actual));
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
