use crate::{
    geom::{Point, Segment},
    num::Float,
};

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

#[derive(Debug, Default, Clone)]
pub struct Segments<F: Float> {
    // TODO: make fields private; provide accessors and constructors
    pub segs: Vec<Segment<F>>,
    // TODO: support open paths too. Maybe reserve SegIdx(0)? Or SegIdx(usize::MAX)?
    pub contour_prev: Vec<Option<SegIdx>>,
    pub contour_next: Vec<Option<SegIdx>>,
    pub orientation: Vec<bool>,
}

impl<F: Float> Segments<F> {
    pub fn get(&self, idx: SegIdx) -> &Segment<F> {
        &self.segs[idx.0]
    }

    pub fn indices(&self) -> impl Iterator<Item = SegIdx> {
        (0..self.segs.len()).map(SegIdx)
    }

    pub fn oriented_start(&self, idx: SegIdx) -> &Point<F> {
        if self.orientation[idx.0] {
            &self.get(idx).start
        } else {
            &self.get(idx).end
        }
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

/// An inefficient but flexible representation of a single sweep-line.
#[derive(Clone, Debug)]
pub struct SweepLine<F: Float> {
    /// The vertical coordinate of this sweep line.
    pub y: F,
    /// All segments present in the sweep line, sorted by their first horizontal position.
    ///
    /// Must be non-empty.
    pub segs: Vec<SweepLineEntry<F>>,
}

#[derive(Clone, Debug)]
pub struct SweepLineEntry<F: Float> {
    pub idx: SegIdx,
    pub x: SweepLineSeg<F>,
}

#[derive(Clone, Debug)]
pub enum SweepLineSeg<F: Float> {
    Single(F),
    EnterExit(F, F),
}

impl<F: Float> SweepLine<F> {
    pub fn check_invariants(&self) {
        assert!(is_sorted(self.segs.iter().map(|entry| match &entry.x {
            SweepLineSeg::Single(x) | SweepLineSeg::EnterExit(x, _) => x,
        })));
    }
}

impl<F: Float> SweepLineSeg<F> {
    /// I couldn't think of a good name for this, but if `b` is true it returns the entering
    /// `x` coordinate and otherwise returns the exiting `x` coordinate.
    ///
    /// If you take `b` to be whether the line segment is positively oriented, this method returns
    /// the horizontal position of the point that gets visited first when walking the contour.
    pub fn enter(&self, b: bool) -> &F {
        match self {
            SweepLineSeg::Single(x) => x,
            SweepLineSeg::EnterExit(x, y) => {
                if b {
                    x
                } else {
                    y
                }
            }
        }
    }
}

fn is_sorted<T: PartialOrd, I: Iterator<Item = T>>(mut it: I) -> bool {
    let Some(mut prev) = it.next() else {
        return true;
    };

    for cur in it {
        if prev > cur {
            return false;
        }
        prev = cur;
    }
    true
}

#[cfg(test)]
mod tests {
    #[test]
    fn is_sorted() {
        use super::is_sorted;

        assert!(is_sorted([0, 1, 1, 5].iter()));
        assert!(is_sorted([0].iter()));
        assert!(is_sorted(Vec::<u32>::new().iter()));

        assert!(!is_sorted([0, 1, 0, 5].iter()));
        assert!(!is_sorted([1, 0, 0, 5].iter()));
        assert!(!is_sorted([1, 1, 1, 0].iter()));
        assert!(!is_sorted([1, 0].iter()));
    }
}
