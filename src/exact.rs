//! Exact geometric primitives, using rational arithmetic, for testing.

use malachite::Rational;

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Point {
    pub y: Rational,
    pub x: Rational,
}

impl Point {
    // TryInto so that we can use floats (panicking on infinities and nans).
    pub fn new(x: impl TryInto<Rational>, y: impl TryInto<Rational>) -> Point {
        Point {
            x: x.try_into().ok().unwrap(),
            y: y.try_into().ok().unwrap(),
        }
    }
}

impl From<crate::Point> for Point {
    fn from(p: crate::Point) -> Self {
        Self {
            // Rational::try_from(f64) fails on NaN (impossible because we use NotNan)
            // and infinity (possible, but a bug).
            x: p.x.into_inner().try_into().unwrap(),
            y: p.y.into_inner().try_into().unwrap(),
        }
    }
}

impl<'a> std::ops::Sub<&'a Point> for &'a Point {
    type Output = Vector;

    fn sub(self, rhs: &'a Point) -> Vector {
        Vector {
            x: &self.x - &rhs.x,
            y: &self.y - &rhs.y,
        }
    }
}

impl Point {
    pub fn affine(&self, other: &Point, t: &Rational) -> Point {
        let one = Rational::from(1);
        Point {
            x: (&one - t) * &self.x + t * &other.x,
            y: (&one - t) * &self.y + t * &other.y,
        }
    }
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Segment {
    pub start: Point,
    pub end: Point,
}

impl From<crate::Segment> for Segment {
    fn from(s: crate::Segment) -> Self {
        Self {
            start: s.start.into(),
            end: s.end.into(),
        }
    }
}

impl Segment {
    pub fn at_y(&self, y: &Rational) -> Rational {
        if self.start.y == self.end.y {
            self.end.x.clone()
        } else {
            let t = (y - &self.start.y) / (&self.end.y - &self.start.y);
            self.start.affine(&self.end, &t).x
        }
    }

    // (If there's an interval of intersection, returns the last intersecting y)
    pub fn intersection_y(&self, other: &Segment) -> Option<Rational> {
        let u = &self.end - &self.start;
        let v = &other.end - &other.start;
        let w = &other.start - &self.start;

        let det = u.cross(&v);
        if det == 0 {
            // They're parallel.
            if u.cross(&w) == 0 {
                // They're colinear, so need to check if they overlap.
                // (If they aren't vertical we only need to check x...)
                if (self.start.x <= other.end.x && other.start.x <= self.end.x)
                    && (self.start.y <= other.end.y && other.start.y <= self.end.y)
                {
                    Some((&self.end.y).min(&other.end.y).clone())
                } else {
                    None
                }
            } else {
                None
            }
        } else {
            let s = w.cross(&v) / &det;
            let t = w.cross(&u) / &det;
            if (0..=1).contains(&s) && (0..=1).contains(&t) {
                Some(&self.start.y + &s * &u.y)
            } else {
                None
            }
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Vector {
    pub x: Rational,
    pub y: Rational,
}

impl Vector {
    pub fn cross(&self, other: &Vector) -> Rational {
        &self.x * &other.y - &self.y * &other.x
    }

    pub fn dot(&self, other: Vector) -> Rational {
        &self.x * &other.x + &self.y * &other.y
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn exact_intersection() {
        let a = Segment {
            start: Point::new(0, 0),
            end: Point::new(0, 1),
        };

        let b = Segment {
            start: Point::new(0.0, 0.0),
            end: Point::new(0.0, 0.99),
        };

        let c = Segment {
            start: Point::new(-1.0, 1.0),
            end: Point::new(1.0, 1.0),
        };

        let d = Segment {
            start: Point::new(0.0, 1.0),
            end: Point::new(0.0, 2.0),
        };

        assert_eq!(a.intersection_y(&b).unwrap(), 0.99);
        assert_eq!(b.intersection_y(&a).unwrap(), 0.99);
        assert_eq!(a.intersection_y(&c).unwrap(), 1);
        assert_eq!(c.intersection_y(&a).unwrap(), 1);
        assert_eq!(b.intersection_y(&c), None);
        assert_eq!(c.intersection_y(&b), None);

        assert_eq!(a.intersection_y(&d).unwrap(), 1);
        assert_eq!(d.intersection_y(&a).unwrap(), 1);
        assert_eq!(b.intersection_y(&d), None);
        assert_eq!(d.intersection_y(&b), None);
        assert_eq!(c.intersection_y(&d).unwrap(), 1);
        assert_eq!(d.intersection_y(&c).unwrap(), 1);
    }
}
