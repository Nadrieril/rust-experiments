use std::marker::PhantomData;

/// Represents a `FnOnce(I) -> O` guaranteed to have no side-effects, implemented by
/// just keeping the `O`. This can be used to represent complex permission operations
/// that are unobservable at runtime.
pub struct Wand<I, O>(O, PhantomData<fn(I) -> O>);

impl<O> Wand<O, O> {
    pub fn new(x: O) -> Self {
        Self(x, PhantomData)
    }
}
impl<I, O> Wand<I, O> {
    pub fn apply(self, _x: I) -> O {
        self.0
    }
    /// Safety: there must exist a reversible I -> J function with no side-effects.
    pub unsafe fn map<J>(self) -> Wand<J, O> {
        Wand(self.0, PhantomData)
    }
}
