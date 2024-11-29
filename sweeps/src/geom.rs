use malachite::Rational;
use ordered_float::NotNan;

use crate::num::{Bounds, Float};

// Points are sorted by `y` and then by `x`
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Point<F: Float> {
    pub y: F,
    pub x: F,
}

impl<F: Float> std::fmt::Debug for Point<F> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "({:?}, {:?})", self.x, self.y)
    }
}

impl<F: Float> Point<F> {
    pub fn new(x: F, y: F) -> Self {
        Point { x, y }
    }

    pub fn to_exact(&self) -> Point<Rational> {
        Point {
            x: self.x.to_exact(),
            y: self.y.to_exact(),
        }
    }

    // Panics on nans. Should be fine as long as everything is finite.
    pub fn affine(&self, other: &Self, t: &F) -> Self {
        let one = F::from_f32(1.0);
        Point {
            x: (one.clone() - t) * &self.x + t.clone() * &other.x,
            y: (one - t) * &self.y + t.clone() * &other.y,
        }
    }
}

impl<F: Float> From<(F, F)> for Point<F> {
    fn from((x, y): (F, F)) -> Self {
        Self { x, y }
    }
}

impl From<(f64, f64)> for Point<NotNan<f64>> {
    fn from((x, y): (f64, f64)) -> Self {
        Self {
            x: x.try_into().unwrap(),
            y: y.try_into().unwrap(),
        }
    }
}

impl<F: Float> std::ops::Sub for Point<F> {
    type Output = Vector<F>;

    fn sub(self, rhs: Self) -> Self::Output {
        Vector {
            x: self.x - rhs.x,
            y: self.y - rhs.y,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Vector<F: Float> {
    pub x: F,
    pub y: F,
}

// The start point of a line is always strictly less than its end point.
// This is the right representation for most of the sweep-line operations,
// but it's a little clunky for other things because we need to keep track of
// the original orientation.
#[derive(Clone, PartialEq, Eq)]
pub struct Segment<F: Float> {
    pub start: Point<F>,
    pub end: Point<F>,
}

impl<F: Float> std::fmt::Debug for Segment<F> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?} -- {:?}", self.start, self.end)
    }
}

impl<F: Float> Segment<F> {
    /// Our `x` coordinate at the given `y` coordinate.
    ///
    /// Horizontal segments will return their largest `x` coordinate.
    ///
    /// Panics if `y` is outside the `y` range of this segment.
    pub fn at_y(&self, y: &F) -> F {
        assert!((&self.start.y..=&self.end.y).contains(&y));

        if self.start.y == self.end.y {
            self.end.x.clone()
        } else {
            // Even if the segment is *almost* horizontal, t is guaranteed
            // to be in [0.0, 1.0].
            let t = (y.clone() - &self.start.y) / (self.end.y.clone() - &self.start.y);
            self.start.x.clone() + t * (self.end.x.clone() - &self.start.x)
        }
    }

    pub fn at_y_bound(&self, y: &F) -> Bounds<F> {
        assert!((&self.start.y..=&self.end.y).contains(&y));

        let denom = Bounds::single(self.end.y.clone()) - Bounds::single(self.start.y.clone());
        let zero = F::from_f32(0.0);
        if denom.lower <= zero {
            Bounds::from_pair(self.start.x.clone(), self.end.x.clone())
        } else {
            let t = (Bounds::single(y.clone()) - Bounds::single(self.start.y.clone()))
                .max(zero.clone())
                / denom;
            let t = t.clamp(zero.clone(), F::from_f32(1.0));
            crate::num::convex(&self.start.x, &self.end.x, &t)
        }
    }

    /// Returns the x difference between segments at the last y position that they share.
    /// Returns a positive value if `other` is to the right.
    ///
    /// (Returns nonsense if they don't share a y position.)
    pub fn end_offset(&self, other: &Self) -> F {
        if self.end.y < other.end.y {
            other.at_y(&self.end.y) - &self.end.x
        } else {
            other.end.x.clone() - self.at_y(&other.end.y)
        }
    }

    /// Returns the x difference between segments at the first y position that they share.
    /// Returns a positive value if `other` is to the right.
    ///
    /// (Returns nonsense if they don't share a y position.)
    pub fn start_offset(&self, other: &Self) -> F {
        if self.start.y >= other.start.y {
            other.at_y(&self.start.y) - &self.start.x
        } else {
            other.start.x.clone() - self.at_y(&other.start.y)
        }
    }

    /// Returns the y-coordinate of the intersection between this segment and the other, if
    /// there is one and we can get an accurate estimate of it. Assumes that `self` starts
    /// off roughly to the left of `other`.
    ///
    /// We guarantee that if this returns a y value, the two line segments have approximately
    /// the same x-coordinate (within eps/2) at that y value.
    ///
    /// (Actually, we don't guarantee anything of the sort because I haven't done the analysis
    /// yet. But that's the guarantee we need. We're allowed to assume that the lines aren't
    /// close to horizontal.)
    ///
    /// This function is allowed to have false negatives (i.e. fail to find an intersection if
    /// there is one but just barely). In this case the intersection will be caught by comparing
    /// x coordinates along the sweep line.
    ///
    /// # Panics
    /// Panics if the lines don't have overlapping y ranges. (It would be easy enough to return
    /// `None` in this case, but in our application it would indicate a bug anyway.)
    pub fn approx_intersection_y(&self, other: &Self) -> Option<Bounds<F>> {
        let y0 = self.start.y.clone().max(other.start.y.clone());
        let y1 = self.end.y.clone().min(other.end.y.clone());

        assert!(y1 >= y0);

        let dx0 = other.at_y_bound(&y0) - self.at_y_bound(&y0);
        let dx1 = other.at_y_bound(&y1) - self.at_y_bound(&y1);
        let denom = dx0.clone() - dx1;
        if denom.lower <= F::from_f32(0.0) {
            return None;
        }

        let t = dx0 / denom;
        if t.ge(&F::from_f32(0.0)) && t.le(&F::from_f32(1.0)) {
            Some(crate::num::convex(&y0, &y1, &t))
        } else {
            None
        }
    }

    pub fn to_exact(&self) -> Segment<Rational> {
        Segment {
            start: self.start.to_exact(),
            end: self.end.to_exact(),
        }
    }

    pub fn is_horizontal(&self) -> bool {
        self.start.y == self.end.y
    }
}

impl Segment<Rational> {
    pub fn exact_intersection_y(&self, other: &Self) -> Option<Rational> {
        let y0 = self.start.y.clone().max(other.start.y.clone());
        let y1 = self.end.y.clone().min(other.end.y.clone());

        assert!(y1 >= y0);

        let dx0 = other.at_y(&y0) - self.at_y(&y0);
        let dx1 = other.at_y(&y1) - self.at_y(&y1);
        if dx0 == dx1 {
            // They're parallel.
            (dx0 == 0).then_some(y0)
        } else {
            let t = &dx0 / (&dx0 - dx1);
            (0..=1).contains(&t).then(|| &y0 + t * (y1 - &y0))
        }
    }
}

#[cfg(test)]
pub(crate) mod tests {
    use super::*;
    use crate::num::tests::Reasonable;
    use ordered_float::NotNan;
    use proptest::prelude::*;

    impl<F: Reasonable + Float> Reasonable for Point<F>
    where
        F::Strategy: 'static,
    {
        type Strategy = BoxedStrategy<Point<F>>;

        fn reasonable() -> Self::Strategy {
            (F::reasonable(), F::reasonable())
                .prop_map(|(x, y)| Point::new(x, y))
                .boxed()
        }
    }

    impl<F: Reasonable + Float> Reasonable for Segment<F>
    where
        F: 'static,
        F::Strategy: 'static,
    {
        type Strategy = BoxedStrategy<Segment<F>>;

        fn reasonable() -> Self::Strategy {
            (Point::reasonable(), Point::reasonable())
                .prop_map(|(start, end)| {
                    if start <= end {
                        Segment { start, end }
                    } else {
                        Segment {
                            start: end,
                            end: start,
                        }
                    }
                })
                .boxed()
        }
    }

    proptest! {
        #[test]
        fn approx_y(s0 in Segment::<NotNan<f32>>::reasonable(), s1 in Segment::<NotNan<f32>>::reasonable()) {
            if s0.start.y <= s1.end.y && s1.start.y <= s0.end.y {
                if let Some(approx_y) = s0.approx_intersection_y(&s1) {
                    let y = s0.to_exact().exact_intersection_y(&s1.to_exact()).unwrap();
                    assert!((approx_y.lower.to_exact()..=approx_y.upper.to_exact()).contains(&y));
                }
            }
        }
    }
}
