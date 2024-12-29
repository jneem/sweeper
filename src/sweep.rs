use crate::{
    num::Float,
    segments::{SegIdx, Segments},
};

/// A sweep line event.
///
/// These are placed in an `EventQueue` and sorted by height, so that the
/// sweep-line algorithm processes them in increasing order.
#[derive(Clone, Copy, PartialOrd, Ord, PartialEq, Eq)]
pub struct SweepEvent<F: Float> {
    /// The height at which this event takes place.
    pub y: F,
    /// The event's data.
    pub kind: SweepEventKind,
}

impl<F: Float> SweepEvent<F> {
    /// Create an intersection event.
    ///
    /// `left` should be (approximately) to the left of `right` before height `y`,
    /// and then after height `y` they should be swapped.
    pub fn intersection(left: SegIdx, right: SegIdx, y: F) -> Self {
        SweepEvent {
            y,
            kind: SweepEventKind::Intersection { left, right },
        }
    }

    /// Create an enter and an exit event for a line segment (which should be non-horizontal).
    pub fn from_segment(i: SegIdx, arena: &Segments<F>) -> (Self, Self) {
        let s = &arena[i];
        (
            SweepEvent {
                y: s.start.y.clone(),
                kind: SweepEventKind::Enter(i),
            },
            SweepEvent {
                y: s.end.y.clone(),
                kind: SweepEventKind::Exit(i),
            },
        )
    }
}

impl<F: Float> std::fmt::Debug for SweepEvent<F> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?} -> {:?}", self.y, self.kind)
    }
}

/// The different kinds of sweep line events.
///
/// These are sorted in the order that our sweep-line algorithm needs to process them.
#[derive(Clone, Copy, PartialOrd, Ord, PartialEq, Eq)]
pub enum SweepEventKind {
    /// A segment is entering the sweep line (i.e. the sweep line's `y` is the same as the segment's starting `y`).
    ///
    /// This event is only used for non-horizontal segments.
    Enter(SegIdx),
    /// A horizontal segment is entering the sweep line (i.e. both its starting and ending `y`s are on the sweep line).
    Horizontal(SegIdx),
    /// A segment is exiting the sweep line (i.e. the sweep line's `y` is the same as the segment's ending `y`).
    Exit(SegIdx),
    /// Two segments intersect at the sweep line.
    Intersection {
        /// This segment used to be to the left, and after the intersection it will be to the right.
        ///
        /// In our sweep line intersection, this segment might have already been moved to the right by
        /// some other constraints. That's ok.
        left: SegIdx,
        /// This segment used to be to the right, and after the intersection it will be to the left.
        right: SegIdx,
    },
}

impl std::fmt::Debug for SweepEventKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SweepEventKind::Intersection { left, right, .. } => {
                write!(f, "left({left:?}) x right({right:?})")
            }
            SweepEventKind::Enter(seg) => {
                write!(f, "enter({seg:?})")
            }
            SweepEventKind::Exit(seg) => {
                write!(f, "exit({seg:?})")
            }
            SweepEventKind::Horizontal(seg) => {
                write!(f, "horizontal({seg:?})")
            }
        }
    }
}
