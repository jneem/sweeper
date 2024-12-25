#![feature(float_next_up_down, array_windows)]

mod geom;
mod num;
mod segments;
mod sweep;
mod topology;
mod weak_ordering;

pub use geom::{Point, Segment};
pub use num::Float;
pub use segments::{SegIdx, Segments};
pub use topology::Topology;
pub use weak_ordering::{sweep, Position, PositionKind};

#[cfg(test)]
pub mod perturbation;
