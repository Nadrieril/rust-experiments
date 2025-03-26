use std::marker::PhantomData;

use super::{ptr::PtrPerm, vptr::VPtr};

/// Represents a `FnOnce(I) -> O` between ZSTs and guaranteed to have no side-effects. This can be
/// used to represent complex permission operations that are unobservable at runtime.
pub struct Wand<I, O>(PhantomData<fn(I) -> O>);

impl<I, O> Wand<I, O> {
    /// The function isn't actually called, it's used to help inference.
    /// Safety: the constructed wand must be valid.
    pub unsafe fn from_fn(_: impl FnOnce(I) -> O) -> Self {
        Wand(PhantomData)
    }
}
impl<I, Perm: PtrPerm, T> Wand<I, VPtr<Perm, T>> {
    pub fn apply(self, _x: I) -> VPtr<Perm, T> {
        unsafe { VPtr::new(Perm::new()) }
    }
}
