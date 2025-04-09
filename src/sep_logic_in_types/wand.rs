use std::marker::PhantomData;

use crate::ExistsLt;

use super::{
    brands::{ExistsLt, Phantom},
    permissions::{PointsTo, PtrAccess},
    vptr::VPtr,
};

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

    /// Constant wand that returns the provided value.
    pub fn constant(x: O) -> Self
    where
        O: Phantom,
    {
        unsafe { Wand::mimic_closure(|_| x) }
    }
    pub fn times_constant<U>(self, x: U) -> Wand<I, (O, U)>
    where
        U: Phantom,
    {
        self.then(unsafe { Wand::mimic_closure(|o| (o, x)) })
    }
    pub fn swap_tuple() -> Wand<(I, O), (O, I)> {
        unsafe { Wand::from_thin_air() }
    }
    pub fn tensor_left<X>(self) -> Wand<(I, X), (O, X)> {
        unsafe { Wand::from_thin_air() }
    }

    /// Compose two wands.
    pub fn then<U>(self, _other: Wand<O, U>) -> Wand<I, U> {
        unsafe { Wand::from_thin_air() }
    }

    /// Apply the wand to the given value, returning the output.
    pub fn apply(self, _x: I) -> O
    where
        O: Phantom,
    {
        unsafe { O::new() }
    }
    pub fn apply_wand() -> Wand<(Self, I), O> {
        Wand::id().uncurry()
    }
}

impl<I> Wand<I, I> {
    pub fn id() -> Self {
        unsafe { Wand::mimic_fn(|x| x) }
    }
}

impl<I, J, O> Wand<I, Wand<J, O>> {
    pub fn uncurry(self) -> Wand<(I, J), O> {
        unsafe { Wand::from_thin_air() }
    }
}
impl<I, J, O> Wand<(I, J), O> {
    #[expect(unused)]
    pub fn curry(self) -> Wand<I, Wand<J, O>> {
        unsafe { Wand::from_thin_air() }
    }
}

impl Wand<(), ()> {
    /// By virtue of the unforgeability of brands, it's impossible to construct a permission with
    /// the `'impossible` brand. From impossibility one can deduce anything, which this wand
    /// represents.
    #[expect(unused)]
    pub fn ex_falso<Access: PtrAccess, T, X>(
    ) -> ExistsLt!(<'impossible> = Wand<VPtr<PointsTo<'impossible, Access>, T>, X>) {
        ExistsLt::pack_lt(unsafe { Wand::from_thin_air() })
    }
}

/// Additive disjunction: a special pair from which you can choose to extract an `A` or a `B`, but
/// not both. This is an idea from linear logic.
pub struct Choice<A, B>(PhantomData<(A, B)>);
unsafe impl<A: Phantom, B: Phantom> Phantom for Choice<A, B> {}

impl<A: Phantom, B: Phantom> Choice<A, B> {
    pub fn choose_left() -> Wand<Self, A> {
        unsafe { Wand::from_thin_air() }
    }
    pub fn choose_right() -> Wand<Self, B> {
        unsafe { Wand::from_thin_air() }
    }
    pub fn merge<X>(_left: Wand<X, A>, _right: Wand<X, B>) -> Wand<X, Self> {
        unsafe { Wand::from_thin_air() }
    }
    #[expect(unused)]
    pub fn swap() -> Wand<Self, Choice<B, A>> {
        Choice::merge(Self::choose_right(), Self::choose_left())
    }
}
