use crate::{
    geom::{Point, Segment},
    num::Float,
};

/// An index into our segment arena.
///
/// Throughout this library, we assign identities to segments, so that we may
/// consider segments as different even if they have the same start- and end-points.
///
/// This index is used to identify a segment, whose data can be retrieved by looking
/// it up in [`Segments`]. (Of course, this index-as-identifier breaks down if there are
/// multiple `Segments` in flight. Just be careful not to mix them up.)
#[derive(Clone, Copy, PartialOrd, Ord, PartialEq, Eq, Hash)]
pub struct SegIdx(pub usize);

impl std::fmt::Debug for SegIdx {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "s_{}", self.0)
    }
}
#[derive(Debug, Clone)]
pub struct Segments<F: Float> {
    // TODO: make fields private; provide accessors and constructors
    pub segs: Vec<Segment<F>>,
    pub contour_prev: Vec<Option<SegIdx>>,
    pub contour_next: Vec<Option<SegIdx>>,
    /// For each segment, stores true if the sweep-line order (small y to big y)
    /// is the same as the orientation in its original contour.
    pub orientation: Vec<bool>,
}

impl<F: Float> Default for Segments<F> {
    fn default() -> Self {
        Self {
            segs: Default::default(),
            contour_prev: Default::default(),
            contour_next: Default::default(),
            orientation: Default::default(),
        }
    }
}

fn cyclic_pairs<T>(xs: &[T]) -> impl Iterator<Item = (&T, &T)> {
    xs.windows(2)
        .map(|pair| (&pair[0], &pair[1]))
        .chain(xs.last().zip(xs.first()))
}

impl<F: Float> Segments<F> {
    pub fn get(&self, idx: SegIdx) -> &Segment<F> {
        &self.segs[idx.0]
    }

    pub fn indices(&self) -> impl Iterator<Item = SegIdx> {
        (0..self.segs.len()).map(SegIdx)
    }

    pub fn segments(&self) -> impl Iterator<Item = &Segment<F>> {
        self.segs.iter()
    }

    pub fn oriented_start(&self, idx: SegIdx) -> &Point<F> {
        if self.orientation[idx.0] {
            &self.get(idx).start
        } else {
            &self.get(idx).end
        }
    }

    pub fn oriented_end(&self, idx: SegIdx) -> &Point<F> {
        if self.orientation[idx.0] {
            &self.get(idx).end
        } else {
            &self.get(idx).start
        }
    }

    pub fn positively_oriented(&self, idx: SegIdx) -> bool {
        self.orientation[idx.0]
    }

    pub fn add_points<P: Into<Point<F>>>(&mut self, ps: impl IntoIterator<Item = P>, closed: bool) {
        let old_len = self.segs.len();

        let ps: Vec<_> = ps.into_iter().map(|p| p.into()).collect();
        if ps.len() <= 1 {
            return;
        }

        for (p, q) in cyclic_pairs(&ps) {
            let (a, b, orient) = if p < q { (p, q, true) } else { (q, p, false) };
            self.segs.push(Segment {
                start: a.clone(),
                end: b.clone(),
            });
            self.orientation.push(orient);
            self.contour_prev
                .push(Some(SegIdx(self.segs.len().saturating_sub(2))));
            self.contour_next.push(Some(SegIdx(self.segs.len())));
        }
        if closed {
            self.contour_prev[old_len] = Some(SegIdx(self.segs.len() - 1));
            *self.contour_next.last_mut().unwrap() = Some(SegIdx(old_len));
        } else {
            // Yuck
            self.segs.pop();
            self.orientation.pop();
            self.contour_prev.pop();
            self.contour_next.pop();
            self.contour_prev[old_len] = None;
            *self.contour_next.last_mut().unwrap() = None;
        }
    }

    pub fn from_closed_cycle<P: Into<Point<F>>>(ps: impl IntoIterator<Item = P>) -> Self {
        let mut ret = Self::default();
        ret.add_points(ps, true);
        ret
    }
}
