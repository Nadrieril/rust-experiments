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

/// A struct-like type with a field whose type is generic in a pointer permission. This trait
/// permits manipulating the value and permissions of this field.
/// The `FieldTok` is a token identifying the field, which allows for types with several fields.
/// Safety: TODO, definitely something about transmutability.
pub unsafe trait HasGenericPermField<FieldTok, FieldPerm>: EraseNestedPerms
where
    FieldTok: Copy,
    FieldPerm: PtrPerm,
{
    type FieldTy<Perm: PtrPerm>;
    type ChangePerm<NewPerm: PtrPerm>: HasGenericPermField<FieldTok, NewPerm>
        + EraseNestedPerms<Erased = Self::Erased>;

    unsafe fn field_raw(ptr: NonNull<Self>, _tok: FieldTok) -> NonNull<Self::FieldTy<FieldPerm>>;

    /// Given a pointer to `self`, get a pointer to the field, with the same permissions. While the
    /// new pointer is active, the permissions to `self` are inaccessible (because it was moved
    /// out). The original permissions can be recovered by relinquishing the subpointer using the
    /// returned wand.
    // TODO: could (should?) require empty pointee pred
    fn get_field_virt<'this, 'field, PtrPerm, NewFieldPerm: self::PtrPerm>(
        self: VPtr<PtrPerm, Self>,
        _tok: FieldTok,
    ) -> ExistsLt!(<'sub> = (
            VPtr<PointsTo<'sub, PtrPerm::Access>, Self::FieldTy<FieldPerm>>,
            Wand<
                VPtr<PointsTo<'sub, PtrPerm::Access>, Self::FieldTy<NewFieldPerm>>,
                VPtr<PtrPerm, Self::ChangePerm<NewFieldPerm>>
            >,
       ))
    where
        PtrPerm: HasRead<'this>, // TODO: can we relax this?
    {
        let wand = unsafe { Wand::new(self.cast_ty()).map() };
        let ptr = unsafe { VPtr::new(PointsTo::new()) };
        ExistsLt::pack_lt((ptr, wand))
    }

    /// Given a pointer to `self`, get a pointer to the field, with the same permissions. While the
    /// new pointer is active, the permissions to `self` are inaccessible (because it was moved
    /// out). The original permissions can be recovered by relinquishing the subpointer using the
    /// returned wand.
    // TODO: could (should?) require empty pointee pred
    fn get_field<'this, 'field, PtrPerm, NewFieldPerm: self::PtrPerm>(
        self: Ptr<PtrPerm, Self>,
        tok: FieldTok,
    ) -> ExistsLt!(<'sub> = (
            Ptr<PointsTo<'sub, PtrPerm::Access>, Self::FieldTy<FieldPerm>>,
            Wand<
                VPtr<PointsTo<'sub, PtrPerm::Access>, Self::FieldTy<NewFieldPerm>>,
                VPtr<PtrPerm, Self::ChangePerm<NewFieldPerm>>
            >,
       ))
    where
        PtrPerm: HasRead<'this>,
    {
        let this = self.copy();
        self.into_virtual()
            .get_field_virt::<PtrPerm, NewFieldPerm>(tok)
            .unpack_lt(|(field_vptr, wand)| {
                let field_ptr = unsafe { Self::field_raw(this.as_non_null(), tok) };
                let field_ptr = unsafe { Ptr::new_with_vptr(field_ptr, field_vptr) };
                ExistsLt::pack_lt((field_ptr, wand))
            })
    }

    #[expect(unused)]
    fn field_ref(&self, tok: FieldTok) -> &Self::FieldTy<FieldPerm> {
        Ptr::from_ref(self)
            .get_field::<_, NoPerm>(tok)
            .unpack_lt(|(ptr_to_field, _)| ptr_to_field.deref_exact())
    }
    #[expect(unused)]
    fn field_mut(&mut self, tok: FieldTok) -> &mut Self::FieldTy<FieldPerm> {
        Ptr::from_mut(self)
            .get_field::<_, NoPerm>(tok)
            .unpack_lt(|(ptr_to_field, _)| ptr_to_field.into_deref_mut())
    }
}

/// A type that has an `Option<Ptr<Perm, FieldTy>>` field where `Perm` is a generic argument.
pub unsafe trait HasOptPtrField<FieldTok, FieldPerm>: EraseNestedPerms
where
    FieldTok: Copy,
    FieldPerm: PtrPerm,
{
    type FieldTy;
    type ChangePerm<NewPerm: PtrPerm>: HasOptPtrField<FieldTok, NewPerm>
        + EraseNestedPerms<Erased = Self::Erased>;

    unsafe fn field_raw(
        ptr: NonNull<Self>,
        _tok: FieldTok,
    ) -> NonNull<Option<Ptr<FieldPerm, Self::FieldTy>>>;

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
        let this = self.copy();
        self.get_field(tok).unpack_lt(|(ptr_to_field, wand)| {
            // ptr_to_field: Ptr<PointsTo<'sub, PtrPerm::Access>, Option<Ptr<FieldPerm, Self::FieldTy>>>,
            let (ptr_to_field, inner) = ptr_to_field.read_nested_ptr();
            // ptr_to_field: Ptr<PointsTo<'sub, PtrPerm::Access>, Option<Ptr<PointsTo<'inner>, Self::FieldTy>>>,
            // inner: Option<Ptr<FieldPerm::AccessThrough, Self::FieldTy>>,
            let ptr = this.with_virtual(wand.apply(ptr_to_field.into_virtual()));
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
        let this = self.copy();
        self.get_field(tok).unpack_lt(|(ptr_to_field, wand)| {
            // ptr_to_field: Ptr<PointsTo<'sub, PtrPerm::Access>, Option<Ptr<FieldPerm, Self::FieldTy>>>,
            let (ptr_to_field, inner) = ptr_to_field.read_nested_ptr();
            // ptr_to_field: Ptr<PointsTo<'sub, PtrPerm::Access>, Option<Ptr<PointsTo<'inner>, Self::FieldTy>>>,
            // inner: Option<Ptr<PointsTo<'_, FieldPerm::Access, FieldPerm::Pred>, Self::FieldTy>>
            let inner = inner.map(Ptr::pack_perm);
            // inner: Option<Ptr<FieldPerm, Self::FieldTy>>,
            let ptr_to_field = ptr_to_field.write_nested_ptr(new);
            // ptr_to_field: Ptr<PointsTo<'sub, PtrPerm::Access>, Option<Ptr<NewPerm, Self::FieldTy>>>,
            let ptr = this.with_virtual(wand.apply(ptr_to_field.into_virtual()));
            // ptr: Ptr<PtrPerm, Self::ChangePerm<NewPerm>>,
            (ptr, inner)
        })
    }
    /// Like `write_field` but only moves permissions around. Does not write to memory.
    fn write_field_permission<'this, 'field, PtrPerm, NewPerm>(
        self: Ptr<PtrPerm, Self>,
        tok: FieldTok,
        new: VPtr<NewPerm, Self::FieldTy>,
    ) -> Ptr<PtrPerm, Self::ChangePerm<NewPerm>>
    where
        PtrPerm: HasOwn<'this>,
        FieldPerm: IsPointsTo<'field>,
        NewPerm: IsPointsTo<'field>,
    {
        self.map_virtual(|v| v.write_field_permission_virt(tok, new))
    }
    fn write_field_permission_virt<'this, 'field, PtrPerm, NewPerm>(
        self: VPtr<PtrPerm, Self>,
        tok: FieldTok,
        new: VPtr<NewPerm, Self::FieldTy>,
    ) -> VPtr<PtrPerm, Self::ChangePerm<NewPerm>>
    where
        PtrPerm: HasOwn<'this>,
        FieldPerm: IsPointsTo<'field>,
        NewPerm: IsPointsTo<'field>,
    {
        self.get_field_virt(tok).unpack_lt(|(ptr_to_field, wand)| {
            // ptr_to_field: VPtr<PointsTo<'sub, PtrPerm::Access>, Option<Ptr<FieldPerm, Self::FieldTy>>>,
            let ptr_to_field = ptr_to_field.write_nested_ptr_perm(new);
            let ptr = wand.apply(ptr_to_field);
            // ptr: VPtr<PtrPerm, Self::ChangePerm<NewPerm>>,
            ptr
        })
    }
    #[expect(unused)]
    fn drop_field_permission<'this, 'field, PtrPerm>(
        self: VPtr<PtrPerm, Self>,
        tok: FieldTok,
    ) -> VPtr<PtrPerm, Self::ChangePerm<PointsTo<'field>>>
    where
        PtrPerm: HasOwn<'this>,
        FieldPerm: IsPointsTo<'field>,
    {
        self.write_field_permission_virt(tok, VPtr::permissionless())
    }
}
unsafe impl<FieldTok, FieldPerm, T> HasGenericPermField<FieldTok, FieldPerm> for T
where
    Self: HasOptPtrField<FieldTok, FieldPerm>,
    FieldTok: Copy,
    FieldPerm: PtrPerm,
{
    type FieldTy<Perm: PtrPerm> =
        Option<Ptr<Perm, <Self as HasOptPtrField<FieldTok, FieldPerm>>::FieldTy>>;
    type ChangePerm<NewPerm: PtrPerm> =
        <Self as HasOptPtrField<FieldTok, FieldPerm>>::ChangePerm<NewPerm>;
    unsafe fn field_raw(ptr: NonNull<Self>, tok: FieldTok) -> NonNull<Self::FieldTy<FieldPerm>> {
        unsafe { <Self as HasOptPtrField<FieldTok, FieldPerm>>::field_raw(ptr, tok) }
    }
}
