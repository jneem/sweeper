//! The inefficient sweep-strip algorithm.

// The order of building here is that we have the old strip and we have
// the event queue. We remove any segments that exit at the height of the old
// strip, and then add any segments that enter at that height. Then we look
// for the event in the queue that has a strictly bigger y coordinate, and we
// try to construct the next strip.

use std::collections::{BTreeSet, HashMap};

use crate::{
    geom::Point,
    num::Float,
    sweep::{SegIdx, Segments, SweepEvent},
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

/// Our queue of events. Classically, this should be a priority queue but this algorithm requires
/// a `BTreeMap` because we need to iterate over all events at the next (potential) sweep-line
/// without actually removing them from the queue.
#[derive(Debug)]
pub struct EventQueue<F: Float> {
    queue: BTreeSet<SweepEvent<F>>,
}

impl<F: Float> EventQueue<F> {
    /// Return an iterator over all sweep events at the next sweep line.
    pub fn peek(&self) -> Option<impl Iterator<Item = &SweepEvent<F>>> {
        self.queue
            .first()
            .map(|first| self.queue.iter().take_while(move |ev| ev.y == first.y))
    }

    pub fn advance(&mut self) {
        if let Some(first) = self.queue.pop_first() {
            while self.queue.first().map_or(false, |ev| ev.y == first.y) {
                self.queue.pop_first();
            }
        }
    }
}

#[derive(Clone, Hash, PartialEq, Eq)]
pub struct StripSeg<F: Float> {
    pub idx: SegIdx,
    pub x0: F,
    pub x1: F,
}

impl<F: Float> std::fmt::Debug for StripSeg<F> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}, {:.3?} -- {:.3?}", self.idx, self.x0, self.x1)
    }
}

#[derive(Debug, Clone)]
pub struct PreStrip<F: Float> {
    /// Start height of this strip.
    y0: F,
    /// End height of this strip. Guaranteed to be strictly bigger than `y0`.
    y1: F,

    /// Segments in this strip, sorted by absolute value of slope (so that
    /// vertical segments come first and horizontal segments last).
    active: Vec<StripSeg<F>>,
}

impl<F: Float> PreStrip<F> {
    pub fn from_prev_strip(
        prev: &Strip<F>,
        segments: &Segments<F>,
        queue: &mut EventQueue<F>,
    ) -> Option<Self> {
        let y0 = prev.y1.clone();
        let evs = queue
            .peek()
            .expect("the previous line's events should still be in the queue");

        // All segments at the start of this strip, along with their starting x coordinates.
        // Segments from the previous strip start at their previous x coordinate; segments that
        // newly entered determine their own x coordinate.
        let mut active: HashMap<_, _> = prev.segs.iter().map(|s| (s.idx, s.x1.clone())).collect();

        for ev in evs {
            match ev.kind {
                crate::sweep::SweepEventKind::Enter(idx) => {
                    if active.insert(idx, segments.get(idx).at_y(&y0)).is_some() {
                        panic!("tried to insert a segment twice");
                    }
                }
                crate::sweep::SweepEventKind::Exit(idx) => {
                    if active.remove(&idx).is_none() {
                        panic!("tried to remove a segment that wasn't there");
                    }
                }
                crate::sweep::SweepEventKind::Intersection { .. } => {}
            }
        }

        queue.advance();

        // If there's nothing left in the queue, we're done; return None.
        let y1 = queue.peek()?.next().expect("peek returned empty").y.clone();

        let mut active: Vec<_> = active
            .into_iter()
            .map(|(idx, x0)| StripSeg {
                idx,
                x0,
                x1: segments.get(idx).at_y(&y1),
            })
            .collect();
        active.sort_by_key(|seg| (seg.x1.clone() - &seg.x0).abs());
        Some(PreStrip { y0, y1, active })
    }

    pub fn truncate(&mut self, segments: &Segments<F>, y1: &F) {
        assert!(y1 > &self.y0);

        self.y1 = y1.clone();
        for s in &mut self.active {
            s.x1 = segments.get(s.idx).at_y(y1);
        }
        // Because of numerical errors, the sort order probably won't be completely correct anymore.
        // It's probably close enough not to matter, but we re-sort anyway.
        self.active
            .sort_by_key(|seg| (seg.x1.clone() - &seg.x0).abs());
    }

    /// Try to build the full strip, failing if we encounter an intersection.
    pub fn build(&self, eps: &F) -> Result<Strip<F>, SweepEvent<F>> {
        let mut strip = Strip {
            y0: self.y0.clone(),
            y1: self.y1.clone(),
            segs: Vec::new(),
        };

        for seg in &self.active {
            let idx = match strip
                .segs
                .binary_search_by(|s| (&s.x0, &s.x1).cmp(&(&seg.x0, &seg.x1)))
            {
                Ok(i) => i,
                Err(i) => i,
            };

            let (idx, seg) = match strip.check_new_seg(idx, seg, eps) {
                InsertionResult::Exact => (idx, seg.clone()),
                InsertionResult::Perturbed(new_idx, new_seg) => (new_idx, new_seg), // TODO: insert a new point into the output segment?
                InsertionResult::Intersected(y, other) => {
                    return Err(SweepEvent::intersection(seg.idx, other.idx, y))
                }
            };
            strip.segs.insert(idx, seg.clone());
        }
        Ok(strip)
    }
}

#[derive(Clone)]
pub struct Strip<F: Float> {
    /// Start height of this strip.
    pub y0: F,
    /// End height of this strip. Guaranteed to be strictly bigger than `y0`.
    pub y1: F,

    pub segs: Vec<StripSeg<F>>,
}

impl<F: Float> std::fmt::Debug for Strip<F> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "Strip {:?} -- {:?}", self.y0, self.y1)?;
        f.debug_list().entries(self.segs.iter()).finish()
    }
}

fn assert_sorted<'a, F: Float, I: Iterator<Item = &'a F>>(mut iter: I) {
    if let Some(mut prev) = iter.next() {
        for x in iter {
            assert!(prev <= x);
            prev = x;
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum InsertionResult<F: Float> {
    Exact,
    Perturbed(usize, StripSeg<F>),
    Intersected(F, StripSeg<F>),
}

impl<F: Float> Strip<F> {
    pub fn check_new_seg(&self, idx: usize, seg: &StripSeg<F>, eps: &F) -> InsertionResult<F> {
        // Precondition: the index is appropriate for the start-coordinate of `seg`.
        assert!(idx == 0 || self.segs[idx - 1].x0 <= seg.x0);
        assert!(idx == self.segs.len() || self.segs[idx].x0 >= seg.x0);

        let ok_left = idx == 0 || self.segs[idx - 1].x1 <= seg.x1;
        let ok_right = idx == self.segs.len() || seg.x1 <= self.segs[idx].x1;

        if ok_left && ok_right {
            InsertionResult::Exact
        } else {
            let dy = self.y1.clone() - &self.y0;
            let dx = (seg.x1.clone() - &seg.x0).abs();
            let threshold = dx.max(dy.clone()) * eps;

            // The first index whose x0 coordinate is such that we might consider moving before it.
            let i_start = self.segs[0..idx]
                .iter()
                .rposition(|s| (seg.x0.clone() - &s.x0) * &dy > threshold)
                .map_or(0, |j| j + 1);

            // Just after the last index whose x0 coordinate is such that we might consider moving after it.
            let i_stop = self.segs[idx..]
                .iter()
                .position(|s| (s.x0.clone() - &seg.x0) * &dy > threshold)
                .map_or(self.segs.len(), |j| j + idx);

            // Can we insert (with perturbation) at index j?
            let ok_at = |j: usize| -> bool {
                let ok_left = j == 0 || (self.segs[j - 1].x1.clone() - &seg.x1) * &dy <= threshold;
                let ok_right =
                    j == self.segs.len() || (seg.x1.clone() - &self.segs[j].x1) * &dy <= threshold;

                ok_left && ok_right
            };

            if let Some(j) = (i_start..=i_stop).position(ok_at) {
                let mut x0 = seg.x0.clone();
                let mut x1 = seg.x1.clone();

                if j > 0 {
                    x0 = x0.max(self.segs[j - 1].x0.clone());
                    x1 = x1.max(self.segs[j - 1].x1.clone());
                }
                if j < self.segs.len() {
                    x0 = x0.min(self.segs[j].x0.clone());
                    x1 = x1.min(self.segs[j].x1.clone());
                }

                let perturbed = StripSeg {
                    idx: seg.idx,
                    x0,
                    x1,
                };

                InsertionResult::Perturbed(j, perturbed)
            } else {
                // Index of a segment that definitely intersects us. We have tried to insert ourselves
                // between i_start and i_stop (inclusive), meaning that we have compared ourselves to
                // indices i_start-1 through i_stop. There must be a robust intersection somewhere in
                // that range.
                let j_start = i_start.saturating_sub(1);
                let j_stop = i_stop.min(self.segs.len() - 1);

                let j = (j_start..=j_stop)
                    .position(|j| {
                        // We start left and finish right of segs[j]
                        ((self.segs[j].x0.clone() - &seg.x0) * &dy >= threshold
                            && (seg.x1.clone() - &self.segs[j].x1) * &dy >= threshold)
                        ||
                        // We start right and finish left of segs[j]
                        ((seg.x0.clone() - &self.segs[j].x0) * &dy >= threshold
                         && (self.segs[j].x1.clone() - &seg.x1) * &dy >= threshold)
                    })
                    .unwrap()
                    + j_start;

                let other = &self.segs[j];
                assert!(
                    (seg.x0 > other.x0) == (seg.x1 < other.x1),
                    "non-crossing \"intersection\": {seg:?} and {other:?},\nsegs {:#?} at {idx} (searched {i_start}..{i_stop})", self.segs,
                );

                let d0 = seg.x0.clone() - &other.x0;
                let d1 = other.x1.clone() - &seg.x1;
                let t = d0.clone() / (d0 + d1);

                let y = self.y0.clone() + t * (self.y1.clone() - &self.y0);
                assert!(y > self.y0 && y < self.y1);
                InsertionResult::Intersected(y, self.segs[j].clone())
            }
        }
    }

    pub fn check_invariants(&self, segments: &Segments<F>) {
        for i in &self.segs {
            let seg = segments.get(i.idx);
            assert!(seg.start.y <= self.y0 && seg.end.y >= self.y1);
            // TODO: take a tolerance, and assert that the endpoints of the
            // strip segment are within that tolerance of the true line.
        }

        assert_sorted(self.segs.iter().map(|i| &i.x0));
        assert_sorted(self.segs.iter().map(|i| &i.x1));
    }
}

pub fn sweep<F: Float>(segments: &Segments<F>, eps: &F) -> Vec<Strip<F>> {
    let mut events = EventQueue {
        queue: segments
            .indices()
            .flat_map(|idx| {
                let (a, b) = SweepEvent::from_segment(idx, segments);
                [a, b]
            })
            .collect(),
    };

    let first_y = events.queue.first().expect("no segments!").y.clone();
    let mut strip = Strip {
        y0: first_y.clone(),
        y1: first_y,
        segs: Vec::new(),
    };

    let mut strips = Vec::new();
    while let Some(mut pre) = PreStrip::from_prev_strip(&strip, segments, &mut events) {
        let s = loop {
            match pre.build(eps) {
                Ok(s) => {
                    break s;
                }
                Err(intersection) => {
                    pre.truncate(segments, &intersection.y);
                    events.queue.insert(intersection);
                }
            }
        };
        strips.push(s.clone());
        strip = s;
    }

    strips
}

#[cfg(test)]
mod tests {
    use assert_matches::assert_matches;
    use ordered_float::NotNan;
    use proptest::prelude::*;

    use crate::{
        geom::Segment,
        perturbation::{f64_perturbation, perturbation, realize_perturbation},
    };

    use super::*;

    fn mk_strip(
        y0: f64,
        y1: f64,
        iter: impl IntoIterator<Item = (f64, f64)>,
    ) -> (Segments<NotNan<f64>>, Strip<NotNan<f64>>) {
        let y0: NotNan<f64> = y0.try_into().unwrap();
        let y1: NotNan<f64> = y1.try_into().unwrap();
        let segs: Vec<_> = iter
            .into_iter()
            .map(|(x0, x1)| Segment {
                start: Point::new(x0.try_into().unwrap(), y0),
                end: Point::new(x1.try_into().unwrap(), y1),
            })
            .collect();

        let segs = Segments {
            segs,
            contour_prev: vec![],
            contour_next: vec![],
        };

        let strip_segs: Vec<_> = segs
            .segs
            .iter()
            .enumerate()
            .map(|(idx, s)| StripSeg {
                idx: SegIdx(idx),
                x0: s.start.x,
                x1: s.end.x,
            })
            .collect();

        (
            segs,
            Strip {
                y0,
                y1,
                segs: strip_segs,
            },
        )
    }

    fn add_seg(
        segs: &mut Segments<NotNan<f64>>,
        (x0, y0): (f64, f64),
        (x1, y1): (f64, f64),
    ) -> StripSeg<NotNan<f64>> {
        segs.segs.push(Segment {
            start: Point::new(x0.try_into().unwrap(), y0.try_into().unwrap()),
            end: Point::new(x1.try_into().unwrap(), y1.try_into().unwrap()),
        });

        StripSeg {
            idx: SegIdx(segs.segs.len() - 1),
            x0: x0.try_into().unwrap(),
            x1: x1.try_into().unwrap(),
        }
    }

    #[test]
    fn test_check() {
        let eps = NotNan::new(0.1).unwrap();
        let (mut segs, strip) = mk_strip(0.0, 1.0, [(0.0, 0.0), (1.0, 1.0)]);

        let s = add_seg(&mut segs, (0.5, 0.0), (0.5, 1.0));
        assert_matches!(strip.check_new_seg(1, &s, &eps), InsertionResult::Exact);

        let s = add_seg(&mut segs, (0.0, 0.0), (0.0, 1.0));
        assert_matches!(strip.check_new_seg(0, &s, &eps), InsertionResult::Exact);
        assert_matches!(strip.check_new_seg(1, &s, &eps), InsertionResult::Exact);

        let s = add_seg(&mut segs, (1.0, 0.0), (1.0, 1.0));
        assert_matches!(strip.check_new_seg(1, &s, &eps), InsertionResult::Exact);
        assert_matches!(strip.check_new_seg(2, &s, &eps), InsertionResult::Exact);

        let s = add_seg(&mut segs, (-0.05, 0.0), (0.05, 1.0));
        assert_matches!(
            strip.check_new_seg(0, &s, &eps),
            InsertionResult::Perturbed(_, _)
        );

        let s = add_seg(&mut segs, (0.05, 0.0), (-0.05, 1.0));
        assert_matches!(
            strip.check_new_seg(1, &s, &eps),
            InsertionResult::Perturbed(_, _)
        );

        let s = add_seg(&mut segs, (1.05, 0.0), (0.95, 1.0));
        assert_matches!(
            strip.check_new_seg(2, &s, &eps),
            InsertionResult::Perturbed(_, _)
        );

        let s = add_seg(&mut segs, (-0.2, 0.0), (0.2, 1.0));
        assert_matches!(
            strip.check_new_seg(0, &s, &eps),
            InsertionResult::Intersected(_, _)
        );

        let s = add_seg(&mut segs, (0.2, 0.0), (-0.2, 1.0));
        assert_matches!(
            strip.check_new_seg(1, &s, &eps),
            InsertionResult::Intersected(_, _)
        );

        // Thin strips. When the strip is this thin, perturbations are basically always allowed.
        let y1 = 0.0f64.next_up();
        let (mut segs, strip) = mk_strip(0.0, y1, [(0.0, 0.0), (1.0, 1.0)]);

        let s = add_seg(&mut segs, (0.2, 0.0), (0.2, y1));
        assert_matches!(strip.check_new_seg(1, &s, &eps), InsertionResult::Exact);

        let s = add_seg(&mut segs, (0.2, 0.0), (-0.2, y1));
        assert_matches!(
            strip.check_new_seg(1, &s, &eps),
            InsertionResult::Perturbed(_, _)
        );

        // TODO: check some known-difficult cases (thin strips, coincident points, etc)
        // TODO: involve proptest
    }

    #[test]
    fn test_sweep() {
        let eps = NotNan::new(0.1).unwrap();
        let (segs, _strip) = mk_strip(0.0, 1.0, [(0.0, 0.0), (1.0, 1.0), (-2.0, 2.0)]);
        let strips = sweep(&segs, &eps);
        assert_eq!(3, strips.len());
    }

    fn p(x: f64, y: f64) -> Point<NotNan<f64>> {
        Point::new(x.try_into().unwrap(), y.try_into().unwrap())
    }

    fn cyclic_pairs<T>(xs: &[T]) -> impl Iterator<Item = (&T, &T)> {
        xs.windows(2)
            .map(|pair| (&pair[0], &pair[1]))
            .chain(xs.last().zip(xs.first()))
    }

    proptest! {
    #[test]
    fn perturbation_test(perturbations in prop::collection::vec(perturbation(f64_perturbation(0.1)), 1..5)) {
        let base = vec![vec![
            p(0.0, 0.0),
            p(1.0, 1.0),
            p(1.0, -1.0),
            p(2.0, 0.0),
            p(1.0, 1.0),
            p(1.0, -1.0),
        ]];

        let perturbed_polylines = perturbations
            .iter()
            .map(|p| realize_perturbation(&base, p))
            .collect::<Vec<_>>();
        let segs = Segments {
            segs: perturbed_polylines
                .iter()
                .flat_map(|poly| {
                    cyclic_pairs(poly).map(|(p0, p1)| Segment {
                        start: p0.min(p1).clone(),
                        end: p0.max(p1).clone(),
                    })
                })
                .collect(),
            contour_prev: vec![],
            contour_next: vec![],
        };

        let eps = NotNan::new(0.1).unwrap();
        let strips = sweep(&segs, &eps);
        for strip in &strips {
            strip.check_invariants(&segs);
        }
    }
    }
}
