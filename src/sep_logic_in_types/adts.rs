use std::{mem::offset_of, ptr::NonNull};

use super::*;
use crate::ExistsLt;
use higher_kinded_types::ForLt as PackLt;

/// Safety: `Self` and `Erased` are the same modulo predicates in `Ptr`, and the predicates in
/// `Self` imply the corresponding predicates in `Erased`.
/// In particular, `Self` and `Erased` must be compatible for transmutability.
pub unsafe trait ErasePerms: Sized {
    type Erased;
}

unsafe impl<T> ErasePerms for ExistsLt<T>
where
    T: PackLt,
    for<'a> T::Of<'a>: ErasePerms,
{
    type Erased = <T::Of<'static> as ErasePerms>::Erased;
}

unsafe impl<Perm, T> ErasePerms for Ptr<Perm, T> {
    type Erased = Ptr<NoPerm, T>;
}

unsafe impl<T: ErasePerms> ErasePerms for Option<T> {
    type Erased = Option<T::Erased>;
}

impl<Perm, T> Ptr<Perm, Option<T>> {
    /// Gets a pointer to the inside of the pointed-to option.
    pub fn read_opt<'this, U>(
        self,
    ) -> Result<
        ExistsLt!(<'sub> = (
             Ptr<PointsTo<'sub, Perm::Access>, T>,
             Wand<
                 VPtr<PointsTo<'sub, Perm::Access>, U>,
                 VPtr<Perm, Option<U>>
             >,
        )),
        Ptr<Perm, Option<U>>,
    >
    where
        Perm: HasRead<'this>,
    {
        // Is there no better way to get a raw pointer to the inside of an option?
        if self.deref().is_some() {
            let ptr = unsafe {
                self.as_non_null()
                    .cast::<u8>()
                    .add(offset_of!(Option<T>, Some.0))
                    .cast::<T>()
            };
            let ptr = unsafe { Ptr::new_with_perm(ptr, PointsTo::new()) };
            let wand = unsafe { Wand::mimic_closure(|_| self.into_virtual().cast_ty()) };
            Ok(ExistsLt::pack_lt((ptr, wand)))
        } else {
            Err(unsafe { self.cast_ty() })
        }
    }
}

/// A struct-like type with a field whose type is generic in a pointer permission. This trait
/// permits manipulating the value and permissions of this field.
/// The `FieldTok` is a token identifying the field, which allows for types with several fields.
/// Safety: TODO, definitely something about transmutability.
pub unsafe trait HasGenericPermField<FieldTok, FieldPerm>: ErasePerms
where
    FieldTok: Copy,
    FieldPerm: PtrPerm,
{
    type FieldTy<Perm: PtrPerm>;
    type ChangePerm<NewPerm: PtrPerm>: HasGenericPermField<FieldTok, NewPerm>
        + ErasePerms<Erased = Self::Erased>;

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
            // What if there's a change I could do to an existential brand in FieldTy that invalidates
            // Self?
            VPtr<PointsTo<'sub, PtrPerm::Access>, Self::FieldTy<FieldPerm>>,
            Wand<
                VPtr<PointsTo<'sub, PtrPerm::Access>, Self::FieldTy<NewFieldPerm>>,
                VPtr<PtrPerm, Self::ChangePerm<NewFieldPerm>>
            >,
       ))
    where
        PtrPerm: HasRead<'this>, // TODO: can we relax this?
    {
        let wand = unsafe { Wand::mimic_closure(|_| self.cast_ty()) };
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

/// Extension trait for `HasGenericPermField` where the field of the type is `Option<Ptr<Perm,
/// PointeeTy>>`.
pub unsafe trait HasOptPtrField<FieldTok, FieldPerm>:
    HasGenericPermField<FieldTok, FieldPerm>
where
    FieldTok: Copy,
    FieldPerm: PtrPerm,
{
    type PointeeTy;

    /// Read the contents of the field, taking the permissions with it as much as possible.
    fn read_field<'this, 'field, PtrPerm>(
        self: Ptr<PtrPerm, Self>,
        tok: FieldTok,
    ) -> (
        Ptr<PtrPerm, Self::ChangePerm<PointsTo<'field>>>,
        Option<Ptr<AccessThroughType<'field, PtrPerm, FieldPerm>, Self::PointeeTy>>,
    )
    where
        PtrPerm: HasRead<'this>,
        FieldPerm: IsPointsTo<'field>,
        FieldPerm::Access: AccessThrough<PtrPerm::Access>,
        Self: HasGenericPermField<
            FieldTok,
            FieldPerm,
            FieldTy<FieldPerm> = Option<Ptr<FieldPerm, Self::PointeeTy>>,
        >,
        Self: HasGenericPermField<
            FieldTok,
            FieldPerm,
            FieldTy<PointsTo<'field>> = Option<Ptr<PointsTo<'field>, Self::PointeeTy>>,
        >,
    {
        let this = self.copy();
        self.get_field(tok).unpack_lt(|(ptr_to_field, wand)| {
            // ptr_to_field: Ptr<PointsTo<'sub, PtrPerm::Access>, Option<Ptr<FieldPerm, Self::FieldTy>>>,
            let (ptr_to_field, inner) = ptr_to_field.read_opt_ptr();
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
        new: Option<Ptr<NewPerm, Self::PointeeTy>>,
    ) -> (
        Ptr<PtrPerm, Self::ChangePerm<NewPerm>>,
        Option<Ptr<FieldPerm, Self::PointeeTy>>,
    )
    where
        PtrPerm: HasOwn<'this>,
        FieldPerm: IsPointsTo<'field>,
        NewPerm: self::PtrPerm,
        Self: HasGenericPermField<
            FieldTok,
            FieldPerm,
            FieldTy<FieldPerm> = Option<Ptr<FieldPerm, Self::PointeeTy>>,
        >,
        Self: HasGenericPermField<
            FieldTok,
            FieldPerm,
            FieldTy<NewPerm> = Option<Ptr<NewPerm, Self::PointeeTy>>,
        >,
    {
        let this = self.copy();
        self.get_field(tok).unpack_lt(|(ptr_to_field, wand)| {
            // ptr_to_field: Ptr<PointsTo<'sub, PtrPerm::Access>, Option<Ptr<FieldPerm, Self::FieldTy>>>,
            let (ptr_to_field, inner) = ptr_to_field.read_opt_ptr();
            // ptr_to_field: Ptr<PointsTo<'sub, PtrPerm::Access>, Option<Ptr<PointsTo<'inner>, Self::FieldTy>>>,
            // inner: Option<Ptr<PointsTo<'_, FieldPerm::Access, FieldPerm::Pred>, Self::FieldTy>>
            let inner = inner.map(Ptr::pack_perm);
            // inner: Option<Ptr<FieldPerm, Self::FieldTy>>,
            let ptr_to_field = ptr_to_field.write(new);
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
        new: VPtr<NewPerm, Self::PointeeTy>,
    ) -> Ptr<PtrPerm, Self::ChangePerm<NewPerm>>
    where
        PtrPerm: HasOwn<'this>,
        FieldPerm: IsPointsTo<'field>,
        NewPerm: IsPointsTo<'field>,
        Self: HasGenericPermField<
            FieldTok,
            FieldPerm,
            FieldTy<FieldPerm> = Option<Ptr<FieldPerm, Self::PointeeTy>>,
        >,
        Self: HasGenericPermField<
            FieldTok,
            FieldPerm,
            FieldTy<NewPerm> = Option<Ptr<NewPerm, Self::PointeeTy>>,
        >,
    {
        self.map_virtual(|v| v.write_field_permission_virt(tok, new))
    }
    fn write_field_permission_virt<'this, 'field, PtrPerm, NewPerm>(
        self: VPtr<PtrPerm, Self>,
        tok: FieldTok,
        new: VPtr<NewPerm, Self::PointeeTy>,
    ) -> VPtr<PtrPerm, Self::ChangePerm<NewPerm>>
    where
        PtrPerm: HasOwn<'this>,
        FieldPerm: IsPointsTo<'field>,
        NewPerm: IsPointsTo<'field>,
        Self: HasGenericPermField<
            FieldTok,
            FieldPerm,
            FieldTy<FieldPerm> = Option<Ptr<FieldPerm, Self::PointeeTy>>,
        >,
        Self: HasGenericPermField<
            FieldTok,
            FieldPerm,
            FieldTy<NewPerm> = Option<Ptr<NewPerm, Self::PointeeTy>>,
        >,
    {
        self.get_field_virt(tok).unpack_lt(|(ptr_to_field, wand)| {
            // ptr_to_field: VPtr<PointsTo<'sub, PtrPerm::Access>, Option<Ptr<FieldPerm, Self::FieldTy>>>,
            let ptr_to_field = ptr_to_field.write_opt_ptr_perm(new);
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
        Self: HasGenericPermField<
            FieldTok,
            FieldPerm,
            FieldTy<FieldPerm> = Option<Ptr<FieldPerm, Self::PointeeTy>>,
        >,
        Self: HasGenericPermField<
            FieldTok,
            FieldPerm,
            FieldTy<PointsTo<'field>> = Option<Ptr<PointsTo<'field>, Self::PointeeTy>>,
        >,
    {
        self.write_field_permission_virt(tok, VPtr::permissionless())
    }
}
