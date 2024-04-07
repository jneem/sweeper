use std::collections::BinaryHeap;

use crate::{geom::Segment, num::Float};

/// Throughout this library, we assign identities to segments, so that we may
/// consider segments as different even if they have the same start- and end-points.
///
/// This index is used to identify a segment, whose data can be retrieved by looking
/// it up in [`Segments`]. (Of course, this index-as-identifier breaks down if there are
/// multiple `Segments` in flight. Maybe `SegRef<'a>(pub &'a SegData)` would be a better
/// representation. But it makes us carry lifetimes around...
#[derive(Clone, Copy, PartialOrd, Ord, PartialEq, Eq, Hash)]
pub struct SegIdx(pub usize);

impl std::fmt::Debug for SegIdx {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "s_{}", self.0)
    }
}

#[derive(Clone, Copy, PartialOrd, Ord, PartialEq, Eq)]
pub struct SweepEvent<F: Float> {
    pub y: F,
    pub kind: SweepEventKind,
}

#[derive(Debug)]
pub struct Intersection<F: Float> {
    pub y: F,
    pub i: SegIdx,
    pub j: SegIdx,
}

impl<F: Float> SweepEvent<F> {
    pub fn intersection(left: SegIdx, right: SegIdx, y: F) -> Self {
        SweepEvent {
            y,
            kind: SweepEventKind::Intersection { left, right },
        }
    }

    pub fn from_segment(i: SegIdx, arena: &Segments<F>) -> (Self, Self) {
        let s = arena.get(i);
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

pub struct Segments<F: Float> {
    // TODO: make fields private; provide accessors and constructors
    pub segs: Vec<Segment<F>>,
    // TODO: support open paths too. Maybe reserve SegIdx(0)? Or SegIdx(usize::MAX)?
    pub contour_prev: Vec<SegIdx>,
    pub contour_next: Vec<SegIdx>,
}

impl<F: Float> Segments<F> {
    pub fn get(&self, idx: SegIdx) -> &Segment<F> {
        &self.segs[idx.0]
    }
}

#[derive(Clone, Copy, PartialOrd, Ord, PartialEq, Eq)]
pub enum SweepEventKind {
    Enter(SegIdx),
    Intersection { left: SegIdx, right: SegIdx },
    Exit(SegIdx),
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
        }
    }
}
