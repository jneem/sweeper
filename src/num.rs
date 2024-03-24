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
{
    fn from(x: f32) -> Self;

    // These next two exist only to support `Bounds`, because this is easier
    // than adding `{add,sub,mul,div}_rounding_{up,down}`. Rational is allowed
    // to have the identity function for both of these.
    fn next_down(&self) -> Self;
    fn next_up(&self) -> Self;
}

impl Float for Rational {
    fn from(x: f32) -> Self {
        Rational::try_from(x).unwrap()
    }

    fn next_down(&self) -> Self {
        self.clone()
    }

    fn next_up(&self) -> Self {
        self.clone()
    }
}

impl Float for NotNan<f32> {
    fn from(x: f32) -> Self {
        NotNan::try_from(x).unwrap()
    }

    fn next_down(&self) -> Self {
        self.into_inner().next_down().try_into().unwrap()
    }

    fn next_up(&self) -> Self {
        self.into_inner().next_up().try_into().unwrap()
    }
}

impl Float for NotNan<f64> {
    fn from(x: f32) -> Self {
        NotNan::try_from(f64::from(x)).unwrap()
    }

    fn next_down(&self) -> Self {
        self.into_inner().next_down().try_into().unwrap()
    }

    fn next_up(&self) -> Self {
        self.into_inner().next_up().try_into().unwrap()
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

    pub fn ge(self, other: &F) -> bool {
        self.lower >= *other
    }

    pub fn le(self, other: &F) -> bool {
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
        let zero = F::from(0.0);

        if (denom.lower > zero) != (denom.upper > zero) || denom.lower == zero {
            panic!("dividing gives full bounds");
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
