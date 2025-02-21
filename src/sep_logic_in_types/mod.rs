mod fields;
pub mod list;
mod permissions;
mod ptr;
pub use higher_kinded_types::ForLt as PackLt;

use fields::*;
use permissions::*;
use ptr::*;
use std::marker::PhantomData;

/// Represents `exists<'this> T::Of<'this>`.
#[repr(transparent)]
pub struct ExistsLt<T: PackLt> {
    /// The lifetime is a lie.
    inner: T::Of<'static>,
}

#[macro_export]
macro_rules! ExistsLt {
    ($($tt:tt)*) => { ExistsLt<higher_kinded_types::ForLt!($($tt)*)> }
}

impl<T: PackLt> ExistsLt<T> {
    pub fn pack_lt(val: T::Of<'_>) -> Self {
        Self {
            inner: unsafe { std::mem::transmute(val) },
        }
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
