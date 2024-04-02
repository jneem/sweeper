//! The inefficient sweep-strip algorithm.

// The order of building here is that we have the old strip and we have
// the event queue. We remove any segments that exit at the height of the old
// strip, and then add any segments that enter at that height. Then we look
// for the event in the queue that has a strictly bigger y coordinate, and we
// try to construct the next strip.

use crate::{
    geom::Point,
    num::Float,
    sweep::{SegIdx, SweepEvent},
};

/// This is where we accumulate the intermediate points for all the segments.
pub struct OutSegments<F: Float> {
    points: Vec<Vec<Point<F>>>,
}

impl<F: Float> OutSegments<F> {
    pub fn append_point(&mut self, seg: SegIdx, p: Point<F>) {
        if seg.0 >= self.points.len() {
            self.points.resize(seg.0 + 1, Vec::new());
        }
        self.points[seg.0].push(p);
    }
}

pub struct StripSeg<F: Float> {
    idx: SegIdx,
    x0: F,
    x1: F,
}

pub struct PreStrip<F: Float> {
    /// Start height of this strip.
    y0: F,
    /// End height of this strip. Guaranteed to be strictly bigger than `y0`.
    y1: F,

    /// Segments in this strip, sorted by absolute value of slope (so that
    /// vertical segments come first and horizontal segments last).
    active: Vec<SegIdx>,
}

impl<F: Float> PreStrip<F> {
    /// Try to build the full strip, failing if we encounter an intersection.
    pub fn build(&self) -> Result<Strip<F>, SweepEvent<F>> {
        todo!()
    }
}

pub struct Strip<F: Float> {
    /// Start height of this strip.
    y0: F,
    /// End height of this strip. Guaranteed to be strictly bigger than `y0`.
    y1: F,

    segs: Vec<StripSeg<F>>,
}
