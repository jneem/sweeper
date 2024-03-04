use ordered_float::NotNan;
use std::cmp::Ordering;

use crate::interval::{self, Bounds};

type Float = NotNan<f64>;

#[derive(Debug)]
pub enum Crosses {
    Now,
    At { y: Float },
    Never,
}

#[derive(Debug)]
pub enum Interaction {
    Blocks,
    Ignores,
}

// Points are sorted by `y` and then by `x`
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Point {
    pub y: Float,
    pub x: Float,
}

impl Point {
    pub fn new(x: f64, y: f64) -> Point {
        Point {
            x: NotNan::new(x).unwrap(),
            y: NotNan::new(y).unwrap(),
        }
    }

    // Panics on nans. Should be fine as long as everything is finite.
    pub fn affine(self, other: Point, t: Float) -> Point {
        let one = NotNan::new(1.0).unwrap();
        Point {
            x: (one - t) * self.x + t * other.x,
            y: (one - t) * self.y + t * other.y,
        }
    }
}

impl std::ops::Sub for Point {
    type Output = Vector;

    fn sub(self, rhs: Self) -> Self::Output {
        Vector {
            x: self.x - rhs.x,
            y: self.y - rhs.y,
        }
    }
}

impl std::fmt::Debug for Point {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "({:?}, {:?})", self.x.into_inner(), self.y.into_inner())
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct Vector {
    pub x: Float,
    pub y: Float,
}

impl Vector {
    pub fn cross(&self, other: Vector) -> f64 {
        self.x.into_inner() * other.y.into_inner() - self.y.into_inner() * other.x.into_inner()
    }

    pub fn dot(&self, other: Vector) -> f64 {
        self.x.into_inner() * other.x.into_inner() + self.y.into_inner() * other.y.into_inner()
    }
}

// The start point of a line is always strictly less than its end point.
// This is the right representation for most of the sweep-line operations,
// but it's a little clunky for other things because we need to keep track of
// the original orientation.
#[derive(Copy, Clone, PartialEq, Eq)]
pub struct Segment {
    pub start: Point,
    pub end: Point,
}

impl Segment {
    /// The second return value is true if the original point order was preserved.
    ///
    /// Panics if the points are equal.
    pub fn from_unordered_points(p0: Point, p1: Point) -> (Segment, bool) {
        match p0.cmp(&p1) {
            Ordering::Less => (Segment { start: p0, end: p1 }, true),
            Ordering::Greater => (Segment { start: p1, end: p0 }, false),
            Ordering::Equal => panic!("empty segment"),
        }
    }
}

impl std::fmt::Debug for Segment {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?} -- {:?}", self.start, self.end)
    }
}

impl Segment {
    pub fn eval(&self, t: Float) -> Point {
        self.start.affine(self.end, t)
    }

    /// Our `x` coordinate at the given `y` coordinate.
    ///
    /// Horizontal segments will return their largest `x` coordinate.
    ///
    /// Panics if `y` is outside the `y` range of this segment.
    pub fn at_y(&self, y: Float) -> Float {
        assert!((self.start.y..=self.end.y).contains(&y));

        if self.start.y == self.end.y {
            self.end.x
        } else {
            // Even if the segment is *almost* horizontal, t is guaranteed
            // to be in [0.0, 1.0].
            let t = (y - self.start.y) / (self.end.y - self.start.y);
            self.eval(t).x
        }
    }

    pub fn at_y_bound(&self, y: Float) -> Bounds {
        assert!((self.start.y..=self.end.y).contains(&y));

        let denom = Bounds::from(self.end.y) - Bounds::from(self.start.y);
        if denom.lower == 0.0 {
            Bounds::from_pair(self.start.x, self.end.x)
        } else {
            let t = (Bounds::from(y) - Bounds::from(self.start.y))
                .clamp(0.0.try_into().unwrap(), f64::INFINITY.try_into().unwrap())
                / denom;
            let t = t.clamp(0.0.try_into().unwrap(), 1.0.try_into().unwrap());
            crate::interval::convex(self.start.x, self.end.x, t)
        }
    }

    /// Returns the x difference between segments at the last y position that they share.
    /// Returns a positive value if `other` is to the right.
    ///
    /// (Returns nonsense if they don't share a y position.)
    pub fn end_offset(&self, other: &Segment) -> Float {
        if self.end.y < other.end.y {
            other.at_y(self.end.y) - self.end.x
        } else {
            other.end.x - self.at_y(other.end.y)
        }
    }

    /// Returns the x difference between segments at the first y position that they share.
    /// Returns a positive value if `other` is to the right.
    ///
    /// (Returns nonsense if they don't share a y position.)
    pub fn start_offset(&self, other: &Segment) -> Float {
        if self.start.y >= other.start.y {
            other.at_y(self.start.y) - self.start.x
        } else {
            other.start.x - self.at_y(other.start.y)
        }
    }

    /// Returns the y-coordinate of the intersection between this segment and the other, if
    /// there is one and we can get an accurate estimate of it.
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
    // TODO: get rid of _eps and make it return Option<Bounds>
    pub fn approx_intersection_y(&self, other: &Segment, _eps: Float) -> Option<Float> {
        let y0 = self.start.y.max(other.start.y);
        let y1 = self.end.y.min(other.end.y);

        assert!(y1 >= y0);

        let dy0 = other.at_y_bound(y0) - self.at_y_bound(y0);
        let dy1 = other.at_y_bound(y1) - self.at_y_bound(y1);

        let t = dy0 / (dy0 - dy1);
        if t.ge(0.0) && t.le(1.0) {
            Some(interval::convex(y0, y1, t).lower)
        } else {
            None
        }
    }

    pub fn is_exactly_horizontal(&self) -> bool {
        self.start.y == self.end.y
    }

    // TODO: should this depend on epsilon? probably.
    pub fn is_almost_horizontal(&self) -> bool {
        (self.start.x - self.end.x).abs() >= 1e3 * (self.start.y - self.end.y).abs()
    }

    /// If the other segment starts to the left of us, what is the interaction like?
    pub fn compare_to_the_left(
        &self,
        other: &Segment,
        y: Float,
        eps: Float,
    ) -> (Crosses, Interaction) {
        let start_offset = other.at_y(y) - self.at_y(y);
        let end_offset = self.end_offset(other);

        // TODO: explain why we shift the other guy
        let y_int = self.approx_intersection_y(&other.shift_horizontal(eps / 2.0), eps);
        let y_int = y_int
            .filter(|z| z >= &y && !self.is_exactly_horizontal() && !other.is_exactly_horizontal());

        if let Some(y) = y_int {
            // Because of the shift, maybe there wasn't really an intersection. Or maybe
            // the intersection was in the wrong direction.
            if end_offset.into_inner() > 0.0 {
                (Crosses::At { y }, Interaction::Blocks)
            } else {
                (Crosses::Never, Interaction::Ignores)
            }
        } else {
            // No intersection, or there was an intersection but we're more-or-less parallel.
            let crosses = if end_offset >= eps {
                Crosses::Now
            } else {
                Crosses::Never
            };
            #[allow(clippy::if_same_then_else)]
            let interact = if end_offset < eps && end_offset >= start_offset + eps {
                // TODO: the condition above needs to be compatible with the bound in
                // approx_intersection_y. We need to ensure that if we failed to find
                // an intersection and the above condition holds, they really are
                // disjoint after y.
                Interaction::Blocks
            } else if end_offset < -eps {
                Interaction::Blocks
            } else {
                Interaction::Ignores
            };
            (crosses, interact)
        }
    }

    pub fn compare_to_the_right(
        &self,
        other: &Segment,
        y: Float,
        eps: Float,
    ) -> (Crosses, Interaction) {
        self.reflect().compare_to_the_left(&other.reflect(), y, eps)
    }

    /// Reflect this segment horizontally.
    pub fn reflect(&self) -> Segment {
        Segment {
            start: Point {
                x: -self.start.x,
                y: self.start.y,
            },
            end: Point {
                x: -self.end.x,
                y: self.end.y,
            },
        }
    }

    pub fn shift_horizontal(&self, delta: Float) -> Segment {
        Segment {
            start: Point {
                x: self.start.x + delta,
                y: self.start.y,
            },
            end: Point {
                x: self.end.x + delta,
                y: self.end.y,
            },
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn approx_intersection_y() {
        let a = Segment {
            start: Point::new(0.0, 0.0),
            end: Point::new(0.0, 10.0),
        };
        let b = Segment {
            start: Point::new(-5.0, 0.0),
            end: Point::new(5.0, 10.0),
        };
        let c = Segment {
            start: Point::new(-5.0, 2.0),
            end: Point::new(5.0, 8.0),
        };

        let eps = Float::try_from(0.1).unwrap();

        fn close_lower_bound(x: Float, y: f64) {
            assert!(x.into_inner() <= y && x.into_inner() >= y - 1e-8);
        }
        close_lower_bound(a.approx_intersection_y(&b, eps).unwrap(), 5.0);
        close_lower_bound(b.approx_intersection_y(&a, eps).unwrap(), 5.0);
        close_lower_bound(a.approx_intersection_y(&c, eps).unwrap(), 5.0);
        close_lower_bound(c.approx_intersection_y(&a, eps).unwrap(), 5.0);
        close_lower_bound(b.approx_intersection_y(&c, eps).unwrap(), 5.0);
        close_lower_bound(c.approx_intersection_y(&b, eps).unwrap(), 5.0);
    }
}
