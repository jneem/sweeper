#![warn(missing_docs)]
#![doc = include_str!("../README.md")]

mod geom;
mod num;
mod segments;
pub mod sweep;
pub mod topology;

pub use geom::{Point, Segment};
pub use num::Float;
pub use segments::{SegIdx, Segments};

#[cfg(test)]
pub mod perturbation;
