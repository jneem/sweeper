#![warn(missing_docs)]
#![doc = include_str!("../../README.md")]

mod geom;
mod num;
mod segments;
mod sweep;
mod topology;
mod weak_ordering;

pub use geom::{Point, Segment};
pub use num::Float;
pub use segments::{SegIdx, Segments};
pub use topology::{
    Contour, ContourIdx, Contours, HalfOutputSegIdx, HalfSegmentWindingNumbers, OutputSegIdx,
    Topology, WindingNumber,
};
pub use weak_ordering::{
    sweep, OutputEvent, OutputEventBatcher, OutputEventKind, SweepLine, Sweeper,
};

#[cfg(test)]
pub mod perturbation;
