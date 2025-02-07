//! Riffing on a recently-discovered unsoundness in rustc due to the type system not having a
//! termination checker: https://github.com/rust-lang/rust/issues/135011.
#![allow(unused)]

mod first_example {
    trait Impossible: Sized {}

    trait MetaImpossible {
        type Assoc: Impossible;
    }

    trait MetaMetaImpossible {
        type Assoc: MetaImpossible;
    }

    impl<T: MetaMetaImpossible> MetaImpossible for T {
        type Assoc = <T::Assoc as MetaImpossible>::Assoc;
    }

    impl MetaMetaImpossible for () {
        type Assoc = ();
    }
}

mod second_example {
    //! Based on https://github.com/rust-lang/rust/issues/135011#issuecomment-2577585549.
    //!
    //! The core of the issue is that the type system does not enforce termination of its terms. We
    //! can use a classic trick to construct a non-terminating associated type that works as a
    //! proof of a trait bound of our choice. We use this to prove any two types equal.

    /// Type-level equality. Using two separate traits for clarity.
    trait IdA {
        type This;
        fn get_this_a(self) -> Self::This;
    }
    impl<T> IdA for T {
        type This = T;
        fn get_this_a(self) -> Self::This {
            self
        }
    }
    trait IdB {
        type This;
        fn get_this_b(self) -> Self::This;
    }
    impl<T> IdB for T {
        type This = T;
        fn get_this_b(self) -> Self::This {
            self
        }
    }

    /// Type-level constant function.
    trait Constant<K> {
        type Val;
    }
    impl<T, K> Constant<K> for T {
        type Val = K;
    }

    /// A trait with non-positive recursion. We will exploit this to craft a proof that `A = B` for
    /// arbitrary `A` and `B`.
    trait NegRecursive<A, B> {
        type Diverge<Recur: NegRecursive<A, B>>: Constant<B, Val = A>;
    }
    /// The classic `omega` term. When applied to itself it gives the non-terminating assoc type
    /// `<() as NegRecursive<A, B>>::Diverge<()>` that implements the trait of our choice. The rest
    /// of the exploit consists in carefully applying this to itself without letting rustc
    /// normalize the type.
    impl<A, B> NegRecursive<A, B> for () {
        type Diverge<Recur: NegRecursive<A, B>> = Recur::Diverge<Recur>;
    }

    /// Trait we use to apply the evil impl to itself. We make it so its associated type can be
    /// normalized in two ways, and the evil type is such that these two normalizations differ.
    // The W,A,B generic params are just for the impl to be well-defined.
    trait Apply<W, A, B> {
        /// Given the `IdB` blanket impl, this should imply `Self::Assoc = Self`.
        type Assoc: IdB<This = Self>;

        /// Converts between `Self::Assoc` and `Self` since they're the same type.
        fn assoc_is_self<Assoc>(x: Assoc) -> Self
        where
            // Indirect through `IdA` to avoid evaluation of `Self::Assoc` when the function is
            // called.
            Assoc: IdA<This = Self::Assoc>;
    }
    impl<A, B1, B2, W: NegRecursive<A, B2>> Apply<W, A, B2> for B1 {
        /// This type can be normalized in two ways:
        /// 1. using the `Constant` blanket impl, `Assoc = B1`;
        /// 2. if `B1 == B2`, using the `NegRecursive` item bound, `Assoc = A`.
        ///
        /// A coherent type system would only allow `W: NegRecursive<A, B>` if `A == B`, which
        /// would make both choices consistent. This is not the case in rustc, which we exploit
        /// below.
        ///
        /// Within the impl we keep `B1` and `B2` separate so that this resolves to `B1`.
        type Assoc = <W::Diverge<W> as Constant<B1>>::Val;

        /// Converts between `Self::Assoc` and `Self` since they're the same type.
        fn assoc_is_self<Assoc>(x: Assoc) -> Self
        where
            // Indirect through `IdA` to avoid evaluation of `Self::Assoc` when the function is
            // called.
            Assoc: IdA<This = Self::Assoc>,
        {
            // <Assoc as IdA>::This: IdB<This = Self>
            // -------------------------------------- normalize
            // Self::Assoc: IdB<This = Self>
            // ----------------------------- prove via item-bound
            x.get_this_a().get_this_b()
        }
    }

    fn transmute<A, B>(x: A) -> B {
        // We prove the where-bounds of `Apply::transmute` in a generic context to avoid
        // normalizing `W::Diverge<W>`.
        fn inner<A, B, W: NegRecursive<A, B>>(x: A) -> B {
            // Need to prove A == B::Assoc (modulo indirection through `IdA`). Because we unify
            // `B1` and `B2`, this normalizes `B::Assoc` using the `NegRecursive` item bound.
            //
            // A: IdA<This = Self::Assoc>
            // -------------------------- normalize
            // A: IdA<This = <W::Diverge<W> as Constant<B>>::Val>
            // -------------------------------------------------- normalize using `NegRecursive` item bound
            // A: IdA<This = A>
            // ---------------- prove using blanket impl
            <B as Apply<W, A, B>>::assoc_is_self(x)
        }
        inner::<A, B, ()>(x)
    }

    #[test]
    fn test_transmute() {
        let x: &str = transmute(&[65u8, 66, 67][..]);
        assert_eq!(x, "ABC");
    }
}
