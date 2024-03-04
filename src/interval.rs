//! Interval arithmetic, slightly sloppy but hopefully correct.
//!
//! Rather than deal with rounding modes or higher-precision operations, we just
//! call `next_down` or `next_up` after every floating-point operation. This
//! should give correct (but not as tight as possible) upper and lower bounds.

use crate::Float;

#[derive(Copy, Clone, Debug)]
pub struct Bounds {
    pub lower: Float,
    pub upper: Float,
}

impl Bounds {
    pub fn from_pair(a: Float, b: Float) -> Self {
        Self {
            lower: a.min(b),
            upper: a.max(b),
        }
    }

    pub fn full() -> Bounds {
        Bounds {
            lower: f64::NEG_INFINITY.try_into().unwrap(),
            upper: f64::INFINITY.try_into().unwrap(),
        }
    }

    pub fn clamp(self, low: Float, high: Float) -> Self {
        assert!(low <= high);
        Self {
            lower: self.lower.max(low),
            upper: self.upper.min(high),
        }
    }

    pub fn ge(self, other: f64) -> bool {
        self.lower.into_inner() >= other
    }

    pub fn le(self, other: f64) -> bool {
        self.upper.into_inner() <= other
    }
}

impl From<Float> for Bounds {
    fn from(x: Float) -> Self {
        Self { lower: x, upper: x }
    }
}

impl std::ops::Add<Bounds> for Bounds {
    type Output = Bounds;

    fn add(self, other: Bounds) -> Self::Output {
        Bounds {
            lower: (self.lower + other.lower).next_down().try_into().unwrap(),
            upper: (self.upper + other.upper).next_up().try_into().unwrap(),
        }
    }
}

impl std::ops::Sub<Bounds> for Bounds {
    type Output = Bounds;

    fn sub(self, other: Bounds) -> Self::Output {
        Bounds {
            lower: (self.lower - other.upper).next_down().try_into().unwrap(),
            upper: (self.upper - other.lower).next_up().try_into().unwrap(),
        }
    }
}

impl std::ops::Div<Bounds> for Bounds {
    type Output = Bounds;

    fn div(self, denom: Bounds) -> Bounds {
        dbg!(self, denom);

        if denom.lower.signum() != denom.upper.signum() || denom.lower == 0.0 {
            Bounds::full()
        } else if denom.upper.into_inner() < 0.0 {
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
pub fn convex(a: Float, b: Float, t: Bounds) -> Bounds {
    if a < b {
        Bounds {
            lower: (a + (t.lower * (b - a).next_down()).next_down())
                .next_down()
                .try_into()
                .unwrap(),
            upper: (a + (t.upper * (b - a).next_up()).next_up())
                .next_up()
                .try_into()
                .unwrap(),
        }
    } else if a > b {
        Bounds {
            lower: (a + (t.upper * (b - a).next_down()).next_down())
                .next_down()
                .try_into()
                .unwrap(),
            upper: (a + (t.lower * (b - a).next_up()).next_up())
                .next_up()
                .try_into()
                .unwrap(),
        }
    } else {
        Bounds::from_pair(a, b)
    }
}
