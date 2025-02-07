use super::*;
use higher_kinded_types::ForLt as PackLt;

/// Safety: `Self` and `Target` are the same modulo predicates in `Ptr`, and the predicates in
/// `Self` imply the corresponding predicates in `Target`.
pub unsafe trait EraseNestedPerms: Sized {
    type Erased;
    fn erase_nested_perms<Perm>(ptr: Ptr<Perm, Self>) -> Ptr<Perm, Self::Erased> {
        // Safety: ok by the precondition.
        unsafe { ptr.cast_ty() }
    }
}

/// A type that has an `Option<Ptr<Perm, FieldTy>>` field where `Perm` is a generic argument.
/// This trait permits manipulating the value and permissions of this field.
/// The `F` is the index of the field, to support multiple fields per type.
pub unsafe trait HasPermField<FieldTok, FieldPerm>: EraseNestedPerms
where
    FieldTok: Copy,
{
    type FieldTy;
    type ChangePerm<NewPerm>: HasPermField<FieldTok, NewPerm>
        + EraseNestedPerms<Erased = Self::Erased>;

    fn field_ref(&self, _tok: FieldTok) -> &Option<Ptr<FieldPerm, Self::FieldTy>>;
    fn field_mut(&mut self, _tok: FieldTok) -> &mut Option<Ptr<FieldPerm, Self::FieldTy>>;

    /// Read the cintents of the field, taking the permissions with it as much as possible.
    fn read_field<'this, 'field, 'a, PtrPerm>(
        self: Ptr<PtrPerm, Self>,
        tok: FieldTok,
    ) -> (
        Ptr<PtrPerm, Self::ChangePerm<Weak<'field>>>,
        Option<Ptr<FieldPerm::AccessThrough, Self::FieldTy>>,
    )
    where
        PtrPerm: HasRead<'this>,
        FieldPerm: HasWeak<'field>,
        FieldPerm: AccessThrough<PtrPerm>,
        FieldPerm::AccessThrough: HasWeak<'field>,
    {
        let ptr = self;
        // Safety: by the invariant of `AccessThrough`, it's ok to get that pointer out.
        let field = ptr
            .deref()
            .field_ref(tok)
            .as_ref()
            .map(|ptr| unsafe { ptr.unsafe_copy().cast_access() });
        // Safety: we're downgrading a `HasWeak<'a>` to a `Weak<'a>`, which is fine even without
        // any particular permissions on `ptr`.
        let ptr = unsafe { ptr.cast_ty() };
        (ptr, field)
    }
    /// Writes the given pointer into the field.
    fn write_field<'this, PtrPerm, NewPerm>(
        self: Ptr<PtrPerm, Self>,
        tok: FieldTok,
        new: Option<Ptr<NewPerm, Self::FieldTy>>,
    ) -> (
        Ptr<PtrPerm, Self::ChangePerm<NewPerm>>,
        Option<Ptr<FieldPerm, Self::FieldTy>>,
    )
    where
        PtrPerm: HasOwn<'this>,
    {
        let mut ptr = self;
        let old_field_val = ptr
            .deref()
            .field_ref(tok)
            .as_ref()
            .map(|new| unsafe { new.unsafe_copy() });
        *ptr.deref_mut().field_mut(tok) = new.map(|new| unsafe { new.cast_perm() });
        let new_ptr = unsafe { ptr.cast_ty() };
        (new_ptr, old_field_val)
    }
    /// Like `write_field` but only moves permissions around. Does not write to memory.
    fn write_field_permission<'this, 'field, PtrPerm, NewPerm>(
        self: Ptr<PtrPerm, Self>,
        tok: FieldTok,
        _new: Ptr<NewPerm, Self::FieldTy>,
    ) -> (
        Ptr<PtrPerm, Self::ChangePerm<NewPerm>>,
        Option<Ptr<FieldPerm, Self::FieldTy>>,
    )
    where
        PtrPerm: HasOwn<'this>,
        FieldPerm: HasWeak<'field>,
        NewPerm: HasWeak<'field>,
    {
        let ptr = self;
        let old_field_val = ptr
            .deref()
            .field_ref(tok)
            .as_ref()
            .map(|new| unsafe { new.unsafe_copy() });
        // Safety: this has the same operation as `write_field`, except we don't need to
        // actually write to memory because the `'field` brand ensures the pointer values are
        // already equal.
        let ptr = unsafe { ptr.cast_ty() };
        (ptr, old_field_val)
    }

    /// Give a name to the hidden lifetime in the permission of the field.
    fn unpack_field_lt<'this, PtrPerm, R>(
        self: Ptr<PtrPerm, Self>,
        _tok: FieldTok,
        f: impl for<'field> FnOnce(Ptr<PtrPerm, Self::ChangePerm<FieldPerm::Of<'field>>>) -> R,
    ) -> R
    where
        FieldPerm: PackLt,
    {
        // Safety: the higher-ranked type + invariant lifetimes hopefully ensures the identifier is
        // fresh and cannot be mixed with other similar identifiers. The behavior of associated
        // types in this context is not entirely clear to me though.
        f(unsafe { self.cast_ty() })
    }
    /// Hide the name of the lifetime in the permission of the field.
    fn pack_field_lt<'this, 'field, PtrPerm>(
        ptr: Ptr<PtrPerm, Self::ChangePerm<FieldPerm::Of<'field>>>,
        _tok: FieldTok,
    ) -> Ptr<PtrPerm, Self>
    where
        FieldPerm: PackLt,
    {
        unsafe { ptr.cast_ty() }
    }
}

/// A predicate on a pointed-to value. It is defined by the fact that `Ptr<PointsTo<'this, Access,
/// Self>, Ty>` and `Ptr<PointsTo<'this, Access>, Self::Unpacked>` are interchangeable. This makes
/// it possible to represent inductive predicates, that are rolled/unrolled using the
/// `pack`/`unpack` methods.
pub trait PackedPredicate<'this, Ty>: Sized {
    type Unpacked: EraseNestedPerms<Erased = Ty>;
    /// Given a pointer with `Self` permission, turn it into a pointer to the type with permissions
    /// applied.
    fn unpack<Perm>(
        ptr: Ptr<PointsTo<'this, Perm, Self>, Ty>,
    ) -> Ptr<PointsTo<'this, Perm>, Self::Unpacked> {
        // Safety: by the `EraseNestedPerms` precondition this only changes predicates (i.e. ghost
        // types) so the two types are layout-compatible. Since the definition of `Self` as a
        // predicate is the effect of this function, this is definitionally a correct cast wrt
        // permissions.
        unsafe { ptr.cast_pred().cast_ty() }
    }
    /// Reverse of `unpack`.
    fn pack<Perm>(
        ptr: Ptr<PointsTo<'this, Perm>, Self::Unpacked>,
    ) -> Ptr<PointsTo<'this, Perm, Self>, Ty> {
        // Safety: by the `EraseNestedPerms` precondition this only changes predicates (i.e. ghost
        // types) so the two types are layout-compatible. Since the definition of `Self` as a
        // predicate is the effect of this function, this is definitionally a correct cast wrt
        // permissions.
        unsafe { ptr.cast_pred().cast_ty() }
    }
}
