use std::marker::PhantomData;

use super::brands::Phantom;

/// Represents a side-effect-free `FnOnce(I) -> O` between ZSTs. This can be used to represent
/// complex permission operations that are unobservable at runtime.
///
/// An important usecase is: a wand can represent a `O`-structure with an ownership hole of type
/// `I`. Filling the hole makes it possible to recover full ownership of `O`. For example, getting
/// access to a field of a struct leaves a wand that can be used to recover full ownership of the
/// struct.
pub struct Wand<I, O>(PhantomData<fn(I) -> O>);
unsafe impl<I, O> Phantom for Wand<I, O> {}

impl<I, O> Wand<I, O> {
    /// Safety: the constructed wand must be valid.
    pub unsafe fn from_thin_air() -> Self {
        Wand(PhantomData)
    }
    /// The function isn't actually called, it's used to help inference.
    /// Safety: the constructed wand must be valid.
    pub unsafe fn mimic_closure(_: impl FnOnce(I) -> O) -> Self {
        unsafe { Wand::from_thin_air() }
    }
    /// The function isn't actually called, it's used to help inference. Better than
    /// `mimic_closure` for inference.
    /// Safety: the constructed wand must be valid.
    pub unsafe fn mimic_fn(f: fn(I) -> O) -> Self {
        unsafe { Wand::mimic_closure(f) }
    }

    /// Compose two wands.
    pub fn then<U>(self, _other: Wand<O, U>) -> Wand<I, U> {
        unsafe { Wand::from_thin_air() }
    }
}

impl<I, O: Phantom> Wand<I, O> {
    pub fn apply(self, _x: I) -> O {
        unsafe { O::new() }
    }
}
