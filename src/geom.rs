use crate::num::Float;

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
    pub fn new(x: f32, y: f32) -> Self {
        Point {
            x: F::from(x),
            y: F::from(y),
        }
    }

    // Panics on nans. Should be fine as long as everything is finite.
    pub fn affine(&self, other: &Self, t: &F) -> Self {
        let one = F::from(1.0);
        Point {
            x: (one.clone() - t) * &self.x + t.clone() * &other.x,
            y: (one - t) * &self.y + t.clone() * &other.y,
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
