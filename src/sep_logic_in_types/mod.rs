mod fields;
pub mod list;
mod permissions;
mod ptr;
mod wand;
pub use higher_kinded_types::ForLt as PackLt;

use fields::*;
use permissions::*;
use ptr::*;
use std::marker::PhantomData;
use wand::*;

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
    pub fn pack_lt_ref<'a>(val: &'a T::Of<'_>) -> &'a Self {
        unsafe { std::mem::transmute(val) }
    }
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
    pub fn refl() -> Self {
        Self(PhantomData, PhantomData)
    }
}
impl<'a, 'b> EqPredicate<'a, 'b> {
    /// Safety: the brands must be the same, for an appropriate notion of "same".
    pub unsafe fn make() -> Self {
        Self(PhantomData, PhantomData)
    }
    pub fn apply<T: PackLt>(self, x: T::Of<'a>) -> T::Of<'b> {
        // Safety: this can only be constructed when `'a == 'b`, and the lifetimes are invariant.
        // Hence the types are actually equal.
        unsafe { std::mem::transmute(x) }
    }
    pub fn flip(self) -> EqPredicate<'b, 'a> {
        EqPredicate(PhantomData, PhantomData)
    }
}
