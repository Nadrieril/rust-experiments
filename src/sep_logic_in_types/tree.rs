use std::ptr::NonNull;

use super::*;
use crate::ExistsLt;

type ErasedNode = ExistsLt!(Node<'_>);
type Child<'this> = ExistsLt!(<'child> = Ptr<Own<'child>, Node<'child, PointsTo<'this>>>);
struct Node<'this, Parent = NoPerm> {
    val: usize,
    children: Vec<Child<'this>>,
    parent: Option<Ptr<Parent, ErasedNode>>,
    /// This node's index into the parent node's `children` array.
    parent_id: u16,
}

unsafe impl<'this, Parent> ErasePerms for Node<'this, Parent> {
    type Erased = ErasedNode;
}

/// Type-level tokens that represent each field of `Node`.
#[derive(Clone, Copy)]
struct FParent;
#[derive(Clone, Copy)]
struct FChildren;
#[derive(Clone, Copy)]
struct FVal;

unsafe impl<'this, Parent: PtrPerm> HasGenericPermField<FParent, Parent> for Node<'this, Parent> {
    type FieldTy<FieldPerm: PtrPerm> = Option<Ptr<FieldPerm, ErasedNode>>;
    type ChangePerm<NewParent: PtrPerm> = Node<'this, NewParent>;
    unsafe fn field_raw(
        ptr: NonNull<Self>,
        _tok: FParent,
    ) -> NonNull<Option<Ptr<Parent, ErasedNode>>> {
        unsafe { NonNull::new_unchecked(&raw mut (*ptr.as_ptr()).parent) }
    }
}
unsafe impl<'this, Parent: PtrPerm> HasOptPtrField<FParent, Parent> for Node<'this, Parent> {
    type PointeeTy = ErasedNode;
}
unsafe impl<'this, Parent: PtrPerm, UnusedPerm: PtrPerm> HasGenericPermField<FVal, UnusedPerm>
    for Node<'this, Parent>
{
    type FieldTy<Perm: PtrPerm> = usize;
    type ChangePerm<NewPerm: PtrPerm> = Self;
    unsafe fn field_raw(ptr: NonNull<Self>, _tok: FVal) -> NonNull<Self::FieldTy<UnusedPerm>> {
        unsafe { NonNull::new_unchecked(&raw mut (*ptr.as_ptr()).val) }
    }
}
unsafe impl<'this, Parent: PtrPerm, UnusedPerm: PtrPerm> HasGenericPermField<FChildren, UnusedPerm>
    for Node<'this, Parent>
{
    type FieldTy<Perm: PtrPerm> = Vec<Child<'this>>;
    type ChangePerm<NewPerm: PtrPerm> = Self;
    unsafe fn field_raw(ptr: NonNull<Self>, _tok: FChildren) -> NonNull<Self::FieldTy<UnusedPerm>> {
        unsafe { NonNull::new_unchecked(&raw mut (*ptr.as_ptr()).children) }
    }
}

pub struct NonEmptyTree<'parent>(
    ExistsLt!(<'this> = Ptr<Own<'this>, Node<'this, PointsTo<'parent>>>),
);
