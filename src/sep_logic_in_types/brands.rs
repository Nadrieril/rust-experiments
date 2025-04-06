pub use higher_kinded_types::ForLt as PackLt;
use std::{marker::PhantomData, mem::MaybeUninit};

/// Types that are transmutable to/from `PhantomData`.
///
/// Safety: must be transmutable to/from `PhantomData` and have no `Drop` implementation.
pub unsafe trait Phantom: Sized {
    /// Create a value of that type.
    ///
    /// Safety: the safety invariant of the created value.
    unsafe fn new() -> Self {
        unsafe { MaybeUninit::zeroed().assume_init() }
    }
}
unsafe impl<T> Phantom for PhantomData<T> {}

// Copied from `ghost_cell`.
pub type InvariantLifetime<'brand> = PhantomData<fn(&'brand ()) -> &'brand ()>;

/// Represents `exists<'this> T::Of<'this>`.
#[repr(transparent)]
pub struct ExistsLt<T: PackLt> {
    /// The lifetime is a lie.
    inner: T::Of<'static>,
}

#[macro_export]
macro_rules! ExistsLt {
    (<$first_lt:lifetime, $($lts:lifetime)*> = $($tt:tt)*) => {
        ExistsLt!(<$first_lt> = ExistsLt!(<$($lts)*> = $($tt)*))
    };
    ($($tt:tt)*) => {
        ExistsLt<higher_kinded_types::ForLt!($($tt)*)>
    };
}

// TODO: implement generic pack/unpack with ForLt.
// oops: this isn't actually safe because it's not actually parametric because of associated types
// :'(
// I really want safe transmute
impl<T: PackLt> ExistsLt<T> {
    pub fn pack_lt(val: T::Of<'_>) -> Self {
        Self {
            inner: unsafe { std::mem::transmute(val) },
        }
    }
    #[expect(unused)]
    pub fn pack_lt_ref<'a>(val: &'a T::Of<'_>) -> &'a Self {
        unsafe { std::mem::transmute(val) }
    }
    #[expect(unused)]
    pub fn pack_lt_mut<'a>(val: &'a mut T::Of<'_>) -> &'a mut Self {
        unsafe { std::mem::transmute(val) }
    }

    pub fn unpack_lt<R>(self, f: impl for<'this> FnOnce(T::Of<'this>) -> R) -> R {
        f(unsafe { std::mem::transmute(self.inner) })
    }
    pub fn unpack_lt_ref<'a, R>(&'a self, f: impl for<'this> FnOnce(&'a T::Of<'this>) -> R) -> R {
        f(unsafe { std::mem::transmute(&self.inner) })
    }
    pub fn unpack_lt_mut<'a, R>(
        &'a mut self,
        f: impl for<'this> FnOnce(&'a mut T::Of<'this>) -> R,
    ) -> R {
        f(unsafe { std::mem::transmute(&mut self.inner) })
    }

    pub fn unpack_opt_lt<R>(
        opt_self: Option<Self>,
        f: impl for<'this> FnOnce(Option<T::Of<'this>>) -> R,
    ) -> R
    where
        T: PackLt,
    {
        match opt_self {
            None => f(None),
            Some(x) => x.unpack_lt(|x| f(Some(x))),
        }
    }
}

/// Witness that `'a` and `'b` are interchangeable, for an notion of "interchangeable" appropriate
/// to what the brands are used for.
#[derive(Debug, Clone, Copy)]
pub struct EqPredicate<'a, 'b>(InvariantLifetime<'a>, InvariantLifetime<'b>);

impl<'a> EqPredicate<'a, 'a> {
    #[expect(unused)]
    pub fn refl() -> Self {
        Self(PhantomData, PhantomData)
    }
}
impl<'a, 'b> EqPredicate<'a, 'b> {
    /// Safety: the brands must be the same, for an appropriate notion of "same".
    pub unsafe fn make() -> Self {
        Self(PhantomData, PhantomData)
    }
    #[expect(unused)]
    pub fn apply<T: PackLt>(self, x: T::Of<'a>) -> T::Of<'b> {
        // Safety: this can only be constructed when `'a == 'b`, and the lifetimes are invariant.
        // Hence the types are actually equal.
        unsafe { std::mem::transmute(x) }
    }
    #[expect(unused)]
    pub fn flip(self) -> EqPredicate<'b, 'a> {
        EqPredicate(PhantomData, PhantomData)
    }
}
