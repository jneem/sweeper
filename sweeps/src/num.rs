//! A thin abstraction over the different numerical types we support.

use std::hash::Hash;

use malachite::Rational;
use ordered_float::NotNan;

/// A trait for abstracting over the properties we need from numerical types.
///
/// This is implemented for `NotNan<f64>`, `NotNan<f32>`, and `malachite::Rational`.
pub trait Float:
    Sized
    + std::ops::Add<Self, Output = Self>
    + std::ops::Sub<Self, Output = Self>
    + std::ops::Mul<Self, Output = Self>
    + std::ops::Div<Self, Output = Self>
    + std::ops::Neg<Output = Self>
    + for<'a> std::ops::Add<&'a Self, Output = Self>
    + for<'a> std::ops::Sub<&'a Self, Output = Self>
    + for<'a> std::ops::Mul<&'a Self, Output = Self>
    + for<'a> std::ops::Div<&'a Self, Output = Self>
    + Clone
    + std::fmt::Debug
    + Ord
    + Eq
    + Hash
    + 'static
{
    fn from_f32(x: f32) -> Self;

    fn to_exact(&self) -> Rational;

    fn abs(self) -> Self;
}

impl Float for Rational {
    fn from_f32(x: f32) -> Self {
        Rational::try_from(x).unwrap()
    }

    fn to_exact(&self) -> Rational {
        self.clone()
    }

    fn abs(self) -> Self {
        <Rational as malachite::num::arithmetic::traits::Abs>::abs(self)
    }
}

impl Float for NotNan<f32> {
    fn from_f32(x: f32) -> Self {
        NotNan::try_from(x).unwrap()
    }

    fn to_exact(&self) -> Rational {
        self.into_inner().try_into().unwrap()
    }

    fn abs(self) -> Self {
        self.into_inner().abs().try_into().unwrap()
    }
}

impl Float for NotNan<f64> {
    fn from_f32(x: f32) -> Self {
        NotNan::try_from(f64::from(x)).unwrap()
    }

    fn to_exact(&self) -> Rational {
        self.into_inner().try_into().unwrap()
    }

    fn abs(self) -> Self {
        self.into_inner().abs().try_into().unwrap()
    }
}

#[cfg(test)]
pub(crate) mod tests {
    use super::*;
    use proptest::prelude::*;

    // Kind of like Arbitrary, but
    // - it's a local trait, so we can impl it for whatever we want, and
    // - it only returns "reasonable" values.
    pub trait Reasonable {
        type Strategy: Strategy<Value = Self>;
        fn reasonable() -> Self::Strategy;
    }

    impl<S: Reasonable, T: Reasonable> Reasonable for (S, T) {
        type Strategy = (S::Strategy, T::Strategy);

        fn reasonable() -> Self::Strategy {
            (S::reasonable(), T::reasonable())
        }
    }

    impl Reasonable for NotNan<f32> {
        type Strategy = BoxedStrategy<NotNan<f32>>;

        fn reasonable() -> Self::Strategy {
            (-1e6f32..1e6).prop_map(|x| NotNan::new(x).unwrap()).boxed()
        }
    }

    impl Reasonable for NotNan<f64> {
        type Strategy = BoxedStrategy<NotNan<f64>>;

        fn reasonable() -> Self::Strategy {
            (-1e6..1e6).prop_map(|x| NotNan::new(x).unwrap()).boxed()
        }
    }

    impl Reasonable for Rational {
        type Strategy = BoxedStrategy<Rational>;

        fn reasonable() -> Self::Strategy {
            (-1e6..1e6)
                .prop_map(|x| Rational::try_from(x).unwrap())
                .boxed()
        }
    }
}
