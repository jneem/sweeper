use std::hash::Hash;

use malachite::Rational;
use ordered_float::NotNan;

pub trait Float:
    Sized
    + std::ops::Add<Self, Output = Self>
    + std::ops::Sub<Self, Output = Self>
    + std::ops::Mul<Self, Output = Self>
    + std::ops::Div<Self, Output = Self>
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

    // These next two exist only to support `Bounds`, because this is easier
    // than adding `{add,sub,mul,div}_rounding_{up,down}`. Rational is allowed
    // to have the identity function for both of these.
    fn next_down(&self) -> Self;
    fn next_up(&self) -> Self;

    fn abs(self) -> Self;
}

impl Float for Rational {
    fn from_f32(x: f32) -> Self {
        Rational::try_from(x).unwrap()
    }

    fn to_exact(&self) -> Rational {
        self.clone()
    }

    fn next_down(&self) -> Self {
        self.clone()
    }

    fn next_up(&self) -> Self {
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

    fn next_down(&self) -> Self {
        self.into_inner().next_down().try_into().unwrap()
    }

    fn next_up(&self) -> Self {
        self.into_inner().next_up().try_into().unwrap()
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

    fn next_down(&self) -> Self {
        self.into_inner().next_down().try_into().unwrap()
    }

    fn next_up(&self) -> Self {
        self.into_inner().next_up().try_into().unwrap()
    }

    fn abs(self) -> Self {
        self.into_inner().abs().try_into().unwrap()
    }
}

/// Interval arithmetic, slightly sloppy but hopefully correct.
///
/// Rather than deal with rounding modes or higher-precision operations, we just
/// call `next_down` or `next_up` after every floating-point operation. This
/// should give correct (but not as tight as possible) upper and lower bounds.
#[derive(Copy, Clone, Debug)]
pub struct Bounds<F: Float> {
    pub lower: F,
    pub upper: F,
}

impl<F: Float> Bounds<F> {
    pub fn from_pair(a: F, b: F) -> Self {
        Self {
            lower: a.clone().min(b.clone()),
            upper: a.max(b),
        }
    }

    pub fn single(a: F) -> Self {
        Bounds {
            lower: a.clone(),
            upper: a,
        }
    }

    pub fn clamp(self, low: F, high: F) -> Self {
        assert!(low <= high);
        Self {
            lower: self.lower.max(low),
            upper: self.upper.min(high),
        }
    }

    pub fn max(self, low: F) -> Self {
        Self {
            lower: self.lower.max(low.clone()),
            upper: self.upper.max(low),
        }
    }

    pub fn ge(&self, other: &F) -> bool {
        self.lower >= *other
    }

    pub fn le(&self, other: &F) -> bool {
        self.upper <= *other
    }
}

impl<F: Float> std::ops::Add<Bounds<F>> for Bounds<F> {
    type Output = Bounds<F>;

    fn add(self, other: Bounds<F>) -> Self::Output {
        Bounds {
            lower: (self.lower + other.lower).next_down(),
            upper: (self.upper + other.upper).next_up(),
        }
    }
}

impl<F: Float> std::ops::Sub<Bounds<F>> for Bounds<F> {
    type Output = Bounds<F>;

    fn sub(self, other: Bounds<F>) -> Self::Output {
        Bounds {
            lower: (self.lower - other.upper).next_down(),
            upper: (self.upper - other.lower).next_up(),
        }
    }
}

impl<F: Float> std::ops::Div<Bounds<F>> for Bounds<F> {
    type Output = Bounds<F>;

    fn div(self, denom: Bounds<F>) -> Bounds<F> {
        let zero = F::from_f32(0.0);

        if denom.lower <= zero && denom.upper >= zero {
            // Technically, when working with floats we could return the "full"
            // bounds range from -infty to infty. But we can't do that with
            // Rational, and anyway division by a range containing zero probably
            // indicates a bug.
            panic!("division by zero");
        }

        if denom.upper < zero {
            Bounds {
                lower: self.lower / denom.lower,
                upper: self.upper / denom.upper,
            }
        } else {
            Bounds {
                lower: self.lower / denom.upper,
                upper: self.upper / denom.lower,
            }
        }
    }
}

/// A convex combination between `a` and `b`.
pub fn convex<F: Float>(a: &F, b: &F, t: &Bounds<F>) -> Bounds<F> {
    match a.cmp(b) {
        std::cmp::Ordering::Less => Bounds {
            lower: (a.clone() + (t.lower.clone() * (b.clone() - a).next_down()).next_down())
                .next_down(),
            upper: (a.clone() + (t.upper.clone() * (b.clone() - a).next_up()).next_up()).next_up(),
        },
        std::cmp::Ordering::Equal => Bounds::from_pair(a.clone(), b.clone()),
        std::cmp::Ordering::Greater => Bounds {
            lower: (a.clone() + (t.upper.clone() * (b.clone() - a).next_down()).next_down())
                .next_down(),
            upper: (a.clone() + (t.lower.clone() * (b.clone() - a).next_up()).next_up()).next_up(),
        },
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

    proptest! {
        #[test]
        fn bounds_add(x in NotNan::<f64>::reasonable(), y in NotNan::<f64>::reasonable()) {
            let b = Bounds::single(x) + Bounds::single(y);
            assert!(b.lower <= x + y);
            assert!(b.upper >= x + y);
        }

        #[test]
        fn bounds_sub(x in NotNan::<f64>::reasonable(), y in NotNan::<f64>::reasonable()) {
            let b = Bounds::single(x) - Bounds::single(y);
            assert!(b.lower <= x - y);
            assert!(b.upper >= x - y);
        }

        #[test]
        fn bounds_div(x in NotNan::<f64>::reasonable(), y in NotNan::<f64>::reasonable()) {
            if y.abs().into_inner() > 1e-3 {
                let b = Bounds::single(x) / Bounds::single(y);
                assert!(b.lower <= x / y);
                assert!(b.upper >= x / y);
            }
        }
    }
}
