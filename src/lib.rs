#![warn(missing_docs)]
#![doc = include_str!("../README.md")]

mod geom;
mod num;
mod segments;
pub mod sweep;
pub mod topology;

pub use geom::{Point, Segment};
pub use num::Float;
use ordered_float::NotNan;
pub use segments::{SegIdx, Segments};

#[cfg(test)]
pub mod perturbation;

/// A fill rule tells us how to decide whether a point is "inside" a polyline.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub enum FillRule {
    /// The point is "inside" if its winding number is odd.
    EvenOdd,
    /// The point is "inside" if its winding number is non-zero.
    NonZero,
}

/// Binary operations between sets.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub enum BinaryOp {
    /// A point is in the union of two sets if it is in either one.
    Union,
    /// A point is in the intersection of two sets if it is in both.
    Intersection,
    /// A point is in the difference of two sets if it is in the first but not the second.
    Difference,
    /// A point is in the exclusive-or of two sets if it is in one or the other, but not both.
    Xor,
}

pub enum Error {
    Infinity,
    NaN,
}

pub fn boolean_op(
    set_a: &[Vec<(f64, f64)>],
    set_b: &[Vec<(f64, f64)>],
) -> Result<topology::Contours<NotNan<f64>>, Error> {
    todo!()
}
