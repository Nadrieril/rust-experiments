fn main() {}

trait Trait {
    type Assoc;
}
impl<T> Trait for T {
    type Assoc = T;
}
#[allow(unused)]
struct Inv<T: Trait>(T::Assoc);

macro_rules! assert_subtype {
    (for<$($lt:lifetime),*> $a:ty :< $b:ty) => {
        const _: () = {
            #[allow(unused)]
            fn fwd<$($lt),*>(x: $a) -> $b {
                x
            }
        };
    };
    (for<$($lt:lifetime),*> $a:ty :> $b:ty) => {
        const _: () = {
            #[allow(unused)]
            fn bwd<$($lt),*>(x: $b) -> $a {
                x
            }
        };
    };
    (for<$($lt:lifetime),*> $a:ty = $b:ty) => {
        assert_subtype!(for<$($lt),*> $a :> $b);
        assert_subtype!(for<$($lt),*> $a :< $b);
    };
    ($($x:tt)*) => {
        assert_subtype!(for<> $($x)*);
    }
}

assert_subtype!(
    fn(fn(&'static u32)) -> &'static u32
    = for<'a> fn(fn(&'a u32)) -> &'a u32
);

type ParamType1<'a> = for<'b> fn(&'b &'a (), &'a u32) -> &'b u32;
type ParamType2<'a> = for<'b> fn(&'static &'a (), &'a u32) -> &'static u32;

assert_subtype!(for<'a> ParamType1<'a> :< ParamType2<'a>);

type Type1 = for<'a, 'b> fn(&'b &'a (), &'a u32) -> &'b u32;
type Type2 = for<'a> fn(&'static &'a (), &'a u32) -> &'static u32;

// Unsound
assert_subtype!(Type1 :< Type2);
