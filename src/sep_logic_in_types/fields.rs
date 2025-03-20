use std::ptr::NonNull;

use super::*;
use crate::ExistsLt;
use higher_kinded_types::ForLt as PackLt;

/// Safety: `Self` and `Target` are the same modulo predicates in `Ptr`, and the predicates in
/// `Self` imply the corresponding predicates in `Target`.
pub unsafe trait EraseNestedPerms: Sized {
    type Erased;
    fn erase_nested_perms<Perm: PtrPerm>(ptr: VPtr<Perm, Self>) -> VPtr<Perm, Self::Erased> {
        // Safety: ok by the precondition.
        unsafe { ptr.cast_ty() }
    }
}

unsafe impl<T> EraseNestedPerms for ExistsLt<T>
where
    T: PackLt,
    for<'a> T::Of<'a>: EraseNestedPerms,
{
    type Erased = <T::Of<'static> as EraseNestedPerms>::Erased;
}

/// A type that has an `Option<Ptr<Perm, FieldTy>>` field where `Perm` is a generic argument.
/// This trait permits manipulating the value and permissions of this field.
/// The `F` is the index of the field, to support multiple fields per type.
pub unsafe trait HasPermField<FieldTok, FieldPerm>: EraseNestedPerms
where
    FieldTok: Copy,
    FieldPerm: PtrPerm,
{
    type FieldTy;
    type ChangePerm<NewPerm: PtrPerm>: HasPermField<FieldTok, NewPerm>
        + EraseNestedPerms<Erased = Self::Erased>;

    unsafe fn field_raw(
        ptr: NonNull<Self>,
        _tok: FieldTok,
    ) -> NonNull<Option<Ptr<FieldPerm, Self::FieldTy>>>;

    #[expect(unused)]
    fn field_ref(&self, tok: FieldTok) -> &Option<Ptr<FieldPerm, Self::FieldTy>> {
        unsafe { Self::field_raw(NonNull::from(self), tok).as_ref() }
    }
    #[expect(unused)]
    fn field_mut(&mut self, tok: FieldTok) -> &mut Option<Ptr<FieldPerm, Self::FieldTy>> {
        unsafe { Self::field_raw(NonNull::from(self), tok).as_mut() }
    }

    /// Given a pointer to `self`, get a pointer to the field, with the same permissions. While the
    /// new pointer is active, the permissions to `self` are inaccessible (because it was moved
    /// out). The original permissions can be recovered by relinquishing the subpointer using the
    /// returned wand.
    /// Note: this may look like it allows for type-changing modifications without full ownership,
    /// but actually type modifications on `self` are only possible if type modifications via `'sub`
    /// are possible, which ends up requiring `PtrPrem::Access: AtLeastOwn`.
    /// Implicit property: only the pointer with full ownership has the right type, others may be
    /// lying.
    /// Could make this stronger: erase type when building non-owning pointers.

    /// -> prevents map_perm
    /// Feels limiting: what if Ptr<Read, Ptr<Own>>: if I can accidentally
    /// get wrong brand for the inner pointer, extremely bad shit is doomed.
    /// -> while there's a read live, can't type-change anyway
    /// only non-access ptrs can be wrong about the type
    ///
    /// Ptr<'this, Own, Node<A>>
    /// ->
    /// Ptr<'this, Own, Node<A>>
    /// * Ptr<'this, Node<A>>
    /// ->
    /// Ptr<'this, Own, Node<B>>
    /// * Ptr<'this, Node<A>>
    /// ->
    /// Ptr<'this, Node<B>>
    /// * Own<'this>
    /// * Ptr<'this, Node<A>>
    /// ->
    /// Ptr<'this, Node<B>>
    /// * Ptr<'this, Own, Node<A>>
    /// FUCK
    /// -> an Own token outside of a Ptr MUST know what it owns.
    ///
    /// separate predicate isn't better:
    ///
    /// Ptr<'this, Own, Node<'prev, 'next>>
    /// * Own<'prev>
    /// * Own<'next>
    /// * PredicateOn<'prev, NodeStateBwd<'prev, 'this>>
    /// * PredicateOn<'next, NodeStateFwd<'next, 'this>>
    /// -> pack
    /// Ptr<'this, Own, Node<'prev, 'next>>
    /// * PredicateOn<'this, NodeStateCursor<'this>>
    /// -> write
    /// Ptr<'this, Own, Node<'newprev, 'next>>
    /// * PredicateOn<'this, NodeStateCursor<'this>>
    /// -> unpack gives wrong type
    /// obviously, a predicate on the pointee is invalidated if we do a write duh
    /// predicate needs to be quantified together with knowledge about the pointee's contained
    /// brands.
    /// I was a fucking genious with the original design wtf
    /// brands that are existentially quantified independent of predicates on them are just useless,
    /// I should never work around this on pain of unsoundness.
    ///
    /// maybe it's more of a `Ptr<'this, Access, Exists!(Tagged<Pred<..>, Node<..>>)>`?
    /// but then I need an operation for:
    /// Ptr<'this, Node>
    /// * PointedToTypeIs<'this, Tagged<...>>
    /// ->
    /// Ptr<'this, Tagged<..>>
    /// feels entirely wrong: this predicate needs to be invalidated by writes.
    ///
    /// implicit premise: I need type-changing operations. if not for that things would be good. but
    /// "brands track pointer address" + need to modify addresses => need for type-changing ops.
    ///
    /// fundamentally: a pointee predicate should be invalidated by writes.
    /// ergo freestanding predicates can't work
    /// a VPtr does make sense however. the owning one is the one with the real type
    /// but I really want separate predicates to make the core model simpler!
    /// -> `PredicateOn<'this, pred, Node>`?
    /// Ptr<'this, T> * PredicateOn<'this, PackedPred, T>
    /// <->
    /// Ptr<'this, T> * <PackedPred as PackedPredicate<'this, T>>::Unpacked
    ///
    /// but then it's an annoying game of match-up. much less nice than current setup.
    ///
    /// TODO:
    /// - fix soundness by replacing freestanding permissions with VPtr
    /// - figure out how much we can improve ergonomics with vptr
    /// - think real hard about what I want to do with this
    ///
    ///
    /// maybe never need to track things in the Ptr, maybe all in Own nodes is ok
    /// or rather, maybe moving a permission to a pointer erases the target knowledge
    /// ugh, what's the mental model???
    /// permissions in pointers are good mental model.
    /// predicates ouside pointers are nice, but require synthesizing ownership predicates
    /// outside a pointer. hence must make sense of it.
    /// essentially I want to do everything in pointers plus I want virtual pointers with no runtime
    /// value attached.
    /// -> can do type-changing operations on the virtual pointer?? weird shit
    /// I don't _like_ virtual pointers. they lack the shutzpah of ownership predicates.
    /// but! they're only needed in combination with `PredicateOn` which is kinda nice?
    ///
    /// ok, goals:
    /// - for soundness, I musn't use permissions on their own
    /// - I want to play with `PredicateOn` style predicates
    /// steps:
    /// - define `VPtr`, use it instead of freestanding predicates.
    /// - migrate to externalized predicates
    /// - remove predicates from `PointsTo` (keep only Access)
    /// - migrate to using only `Node` and `Node<'prev, 'next>`
    /// - use `ErasedNode = ExistsLt!(Node<'_, '_>)` instead of `Node`
    /// - redefine `[V]Ptr` as `[V]Ptr<'this, Access, T>`.
    fn get_field<'this, 'field, PtrPerm, NewFieldPerm: self::PtrPerm>(
        self: Ptr<PtrPerm, Self>,
        tok: FieldTok,
    ) -> ExistsLt!(<'sub> = (
            Ptr<PointsTo<'sub, PtrPerm::Access>, Option<Ptr<FieldPerm, Self::FieldTy>>>,
            Wand<
                Ptr<PointsTo<'sub, PtrPerm::Access>, Option<Ptr<NewFieldPerm, Self::FieldTy>>>,
                Ptr<PtrPerm, Self::ChangePerm<NewFieldPerm>>
            >,
       ))
    where
        PtrPerm: HasRead<'this>,
    {
        let sub_ptr = unsafe { Self::field_raw(self.as_non_null(), tok) };
        let wand = unsafe { Wand::new(self.cast_ty()).map() };
        let ptr = unsafe { Ptr::new_with_perm(sub_ptr, PointsTo::new()) };
        ExistsLt::pack_lt((ptr, wand))
    }

    /// Read the contents of the field, taking the permissions with it as much as possible.
    fn read_field<'this, 'field, PtrPerm>(
        self: Ptr<PtrPerm, Self>,
        tok: FieldTok,
    ) -> (
        Ptr<PtrPerm, Self::ChangePerm<PointsTo<'field>>>,
        Option<Ptr<AccessThroughType<'this, 'field, PtrPerm, FieldPerm>, Self::FieldTy>>,
    )
    where
        PtrPerm: HasRead<'this>,
        FieldPerm: IsPointsTo<'field>,
        FieldPerm::Access: AccessThrough<PtrPerm::Access>,
    {
        self.get_field(tok).unpack_lt(|(ptr_to_field, wand)| {
            // ptr_to_field: Ptr<PointsTo<'sub, PtrPerm::Access>, Option<Ptr<FieldPerm, Self::FieldTy>>>,
            let (ptr_to_field, inner) = ptr_to_field.read_nested_ptr();
            // ptr_to_field: Ptr<PointsTo<'sub, PtrPerm::Access>, Option<Ptr<PointsTo<'inner>, Self::FieldTy>>>,
            // inner: Option<Ptr<FieldPerm::AccessThrough, Self::FieldTy>>,
            let ptr = wand.apply(ptr_to_field);
            // ptr: Ptr<PtrPerm, Self::ChangePerm<PointsTo<'field>>>,
            (ptr, inner)
        })
    }
    /// Writes the given pointer into the field.
    fn write_field<'this, 'field, PtrPerm, NewPerm>(
        self: Ptr<PtrPerm, Self>,
        tok: FieldTok,
        new: Option<Ptr<NewPerm, Self::FieldTy>>,
    ) -> (
        Ptr<PtrPerm, Self::ChangePerm<NewPerm>>,
        Option<Ptr<FieldPerm, Self::FieldTy>>,
    )
    where
        PtrPerm: HasOwn<'this>,
        FieldPerm: IsPointsTo<'field>,
        NewPerm: self::PtrPerm,
    {
        self.get_field(tok).unpack_lt(|(ptr_to_field, wand)| {
            // ptr_to_field: Ptr<PointsTo<'sub, PtrPerm::Access>, Option<Ptr<FieldPerm, Self::FieldTy>>>,
            let (ptr_to_field, inner) = ptr_to_field.read_nested_ptr();
            // ptr_to_field: Ptr<PointsTo<'sub, PtrPerm::Access>, Option<Ptr<PointsTo<'inner>, Self::FieldTy>>>,
            // inner: Option<Ptr<PointsTo<'_, FieldPerm::Access, FieldPerm::Pred>, Self::FieldTy>>
            let inner = inner.map(Ptr::pack_perm);
            // inner: Option<Ptr<FieldPerm, Self::FieldTy>>,
            let ptr_to_field = ptr_to_field.write_nested_ptr(new);
            // ptr_to_field: Ptr<PointsTo<'sub, PtrPerm::Access>, Option<Ptr<NewPerm, Self::FieldTy>>>,
            let ptr = wand.apply(ptr_to_field);
            // ptr: Ptr<PtrPerm, Self::ChangePerm<NewPerm>>,
            (ptr, inner)
        })
    }
    /// Like `write_field` but only moves permissions around. Does not write to memory.
    fn write_field_permission<'this, 'field, PtrPerm, NewPerm>(
        self: Ptr<PtrPerm, Self>,
        tok: FieldTok,
        new: Ptr<NewPerm, Self::FieldTy>,
    ) -> Ptr<PtrPerm, Self::ChangePerm<NewPerm>>
    where
        PtrPerm: HasOwn<'this>,
        FieldPerm: IsPointsTo<'field>,
        NewPerm: IsPointsTo<'field>,
    {
        self.get_field(tok).unpack_lt(|(ptr_to_field, wand)| {
            // ptr_to_field: Ptr<PointsTo<'sub, PtrPerm::Access>, Option<Ptr<FieldPerm, Self::FieldTy>>>,
            let ptr_to_field = ptr_to_field.write_nested_ptr_perm(new.into_virtual());
            let ptr = wand.apply(ptr_to_field);
            // ptr: Ptr<PtrPerm, Self::ChangePerm<NewPerm>>,
            ptr
        })
    }
}

/// A predicate on a pointed-to value. It is defined by the fact that `Ptr<PointsTo<'this, Access,
/// Self>, Ty>` and `Ptr<PointsTo<'this, Access>, Self::Unpacked>` are interchangeable. This makes
/// it possible to represent inductive predicates, that are rolled/unrolled using the
/// `pack`/`unpack` methods.
pub trait PackedPredicate<'this, Ty>: PointeePred + Sized {
    type Unpacked: EraseNestedPerms<Erased = Ty>;
    /// Given a pointer with `Self` permission, turn it into a pointer to the type with permissions
    /// applied.
    fn unpack<A: PtrAccess>(
        ptr: Ptr<PointsTo<'this, A, Self>, Ty>,
    ) -> Ptr<PointsTo<'this, A>, Self::Unpacked> {
        // Safety: by the `EraseNestedPerms` precondition this only changes predicates (i.e. ghost
        // types) so the two types are layout-compatible. Since the definition of `Self` as a
        // predicate is the effect of this function, this is definitionally a correct cast wrt
        // permissions.
        unsafe { ptr.cast_pred().cast_ty() }
    }
    /// Reverse of `unpack`.
    fn pack<A: PtrAccess>(
        ptr: Ptr<PointsTo<'this, A>, Self::Unpacked>,
    ) -> Ptr<PointsTo<'this, A, Self>, Ty> {
        // Safety: by the `EraseNestedPerms` precondition this only changes predicates (i.e. ghost
        // types) so the two types are layout-compatible. Since the definition of `Self` as a
        // predicate is the effect of this function, this is definitionally a correct cast wrt
        // permissions.
        unsafe { ptr.cast_pred().cast_ty() }
    }
}
