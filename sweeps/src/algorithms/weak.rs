//! A sweep-line implementation using weak orderings.
//!
//! This algorithm is documented in `docs/sweep.typ`.
//!
//! TODO: I think in this algorithm it makes sense to put Exit events first.

// TODO:
// - better heuristic for horizontal positions, that avoids small horizontal lines at simple intersections
// - investigate better insertion heuristics: if there are a bunch of insertions at the same point, we
//   currently put them in some arbitrary order and then later have to process a bunch of intersections

use std::collections::BTreeSet;
use std::ops::Range;
use std::{
    cmp::Reverse,
    collections::{HashMap, HashSet},
};

use crate::{
    geom::Segment,
    num::{Bounds, Float},
    sweep::{
        SegIdx, Segments, SweepEvent, SweepEventKind, SweepLine, SweepLineEntry, SweepLineSeg,
    },
};

#[derive(Clone, Debug)]
pub struct WeakSweepLine<F: Float> {
    pub y: F,
    pub segs: Vec<SegIdx>,
    // For the sparse realization, this is the collection of segments that
    // we know need to be given explicit positions in the current sweep line.
    //
    // These include:
    // - any segments that changed order with any other segments
    // - any segments that entered or exited
    // - any segments that are between the endpoints of contour-adjacent segments.
    pub segs_needing_positions: HashSet<SegIdx>,
    // The horizontal segments present at the current sweep line. These aren't
    // included with the usual `segs` because it's easier (and probably faster)
    // to give them special treatment.
    pub horizontals: Vec<SegIdx>,
    pub exits: HashSet<SegIdx>,
    pub entrances: HashSet<SegIdx>,
}

impl<F: Float> WeakSweepLine<F> {
    pub fn new(y: F) -> Self {
        Self::new_with_segs(y, Vec::new())
    }

    pub fn new_with_segs(y: F, segs: Vec<SegIdx>) -> Self {
        Self {
            y,
            segs,
            segs_needing_positions: HashSet::new(),
            horizontals: Vec::new(),
            exits: HashSet::new(),
            entrances: HashSet::new(),
        }
    }
}

#[derive(Clone, Debug)]
pub struct EventQueue<F: Float> {
    inner: std::collections::BinaryHeap<std::cmp::Reverse<SweepEvent<F>>>,
}

impl<F: Float> EventQueue<F> {
    pub fn push(&mut self, ev: SweepEvent<F>) {
        self.inner.push(std::cmp::Reverse(ev));
    }

    pub fn pop(&mut self) -> Option<SweepEvent<F>> {
        self.inner.pop().map(|x| x.0)
    }

    pub fn next_y(&self) -> Option<&F> {
        self.inner.peek().map(|Reverse(ev)| &ev.y)
    }

    fn next_kind(&self) -> Option<&SweepEventKind> {
        self.inner.peek().map(|Reverse(ev)| &ev.kind)
    }

    pub fn next_is_stage_1(&self, y: &F) -> bool {
        self.next_y() == Some(y)
            && self.next_kind().map_or(false, |kind| match kind {
                SweepEventKind::Enter(_) | SweepEventKind::Horizontal(_) => true,
                SweepEventKind::Intersection { .. } | SweepEventKind::Exit(_) => false,
            })
    }

    pub fn next_is_stage_2(&self, y: &F) -> bool {
        self.next_y() == Some(y)
            && self.next_kind().map_or(false, |kind| match kind {
                SweepEventKind::Enter(_)
                | SweepEventKind::Horizontal(_)
                | SweepEventKind::Exit(_) => false,
                SweepEventKind::Intersection { .. } => true,
            })
    }

    pub fn next_is_at(&self, y: &F) -> bool {
        self.next_y() == Some(y)
    }
}

#[derive(Clone, Debug)]
pub struct State<F: Float> {
    pub eps: F,
    pub line: WeakSweepLine<F>,
    pub events: EventQueue<F>,
    pub segments: Segments<F>,
}

impl<F: Float> State<F> {
    fn process_exits(&mut self) {
        for seg_idx in std::mem::take(&mut self.line.exits) {
            let pos = self
                .line
                .position(seg_idx)
                .expect("exit for a segment we don't have");
            self.remove(pos);
            self.line.segs_needing_positions.insert(seg_idx);
            self.line
                .mark_contour_neighbor(seg_idx, false, &self.segments);
        }
    }

    pub fn advance(&mut self, y: F) {
        self.process_exits();
        self.line.y = y;
        self.line.segs_needing_positions.clear();
        self.line.horizontals.clear();
        self.line.entrances.clear();
    }

    pub fn intersection_scan_right(&mut self, start_idx: usize) {
        let seg = self.segments.get(self.line.segs[start_idx]);
        let y = &self.line.y;

        // We're allowed to take a potentially-smaller height bound by taking
        // into account the current queue. A larger height bound is still ok,
        // just a little slower.
        let mut height_bound = seg.end.y.clone();

        for j in (start_idx + 1)..self.line.segs.len() {
            let other = self.segments.get(self.line.segs[j]);
            height_bound = height_bound.min(other.end.y.clone());
            // In the write-up, we check whether `seg` crosses the upper bound
            // of `other`, and we aren't allowed to have false negatives.
            let crosses = other.end_offset(seg) >= self.eps.clone() / F::from_f32(2.0);
            let crosses =
                crosses || seg.at_y(y) >= other.at_y(y) + self.eps.clone() / F::from_f32(2.0);

            if crosses {
                let int_y = seg
                    .approx_intersection_y(other)
                    .map(|bounds| bounds.mid())
                    .unwrap_or_else(|| y.clone());
                // TODO: justify the second condition
                if int_y <= height_bound
                    && seg.end_offset(other) * F::from_f32(-2.0) >= self.eps.clone()
                {
                    self.events.push(SweepEvent::intersection(
                        self.line.segs[start_idx],
                        self.line.segs[j],
                        int_y.clone(),
                    ));
                    height_bound = int_y;
                }
            }

            // For the early stopping, we need to check whether `seg` is less than `other`'s lower
            // bound on the whole interesting `y` interval. Since they're lines, it's enough to check
            // at the two interval endpoints.
            let y1 = &height_bound;
            if seg.at_y_bound(y).upper <= other.lower_bound(y, &self.eps).lower
                && seg.at_y_bound(y1).upper <= other.lower_bound(y1, &self.eps).lower
            {
                break;
            }
        }
    }

    pub fn intersection_scan_left(&mut self, start_idx: usize) {
        let seg = self.segments.get(self.line.segs[start_idx]);
        let y = &self.line.y;

        let mut height_bound = seg.end.y.clone();

        for j in (0..start_idx).rev() {
            let other = self.segments.get(self.line.segs[j]);
            height_bound = height_bound.min(other.end.y.clone());
            let crosses = seg.end_offset(other) >= self.eps.clone() / F::from_f32(2.0);
            let crosses =
                crosses || seg.at_y(y) <= other.at_y(y) - self.eps.clone() / F::from_f32(2.0);

            if crosses {
                let int_y = other
                    .approx_intersection_y(seg)
                    .map(|bounds| bounds.mid())
                    .unwrap_or_else(|| y.clone());

                if int_y <= height_bound
                    && seg.end_offset(other) * F::from_f32(2.0) >= self.eps.clone()
                {
                    self.events.push(SweepEvent::intersection(
                        self.line.segs[j],
                        self.line.segs[start_idx],
                        int_y.clone(),
                    ));
                    height_bound = int_y;
                }
            }

            // For the early stopping, we need to check whether `seg` is greater than `other`'s upper
            // bound on the whole interesting `y` interval. Since they're lines, it's enough to check
            // at the two interval endpoints.
            let y1 = &height_bound;
            if seg.at_y_bound(y).lower >= other.upper_bound(y, &self.eps).upper
                && seg.at_y_bound(y1).lower >= other.upper_bound(y1, &self.eps).upper
            {
                break;
            }
        }
    }

    fn remove(&mut self, pos: usize) {
        self.line.segs.remove(pos);
        if pos > 0 {
            self.intersection_scan_right(pos - 1);
            self.intersection_scan_left(pos - 1);
        }
    }

    fn insert(&mut self, pos: usize, seg: SegIdx) {
        self.line.segs.insert(pos, seg);
        self.intersection_scan_right(pos);
        self.intersection_scan_left(pos);
    }

    pub fn step(&mut self) {
        let Some(ev) = self.events.pop() else {
            return;
        };

        assert!(self.line.y == ev.y);
        match ev.kind {
            SweepEventKind::Enter(seg_idx) => {
                let new_seg = self.segments.get(seg_idx);
                let pos = self.line.insertion_idx(&self.segments, new_seg, &self.eps);
                self.insert(pos, seg_idx);
                self.line.segs_needing_positions.insert(seg_idx);
                self.line
                    .mark_contour_neighbor(seg_idx, true, &self.segments);
                self.line.entrances.insert(seg_idx);
            }
            SweepEventKind::Exit(seg_idx) => {
                self.line.exits.insert(seg_idx);
            }
            SweepEventKind::Intersection { left, right } => {
                let left_idx = self.line.segs.iter().position(|&x| x == left).unwrap();
                let right_idx = self.line.segs.iter().position(|&x| x == right).unwrap();
                if left_idx < right_idx {
                    self.line
                        .segs_needing_positions
                        .extend(&self.line.segs[left_idx..=right_idx]);
                    let left_seg = self.segments.get(left);
                    let eps = &self.eps;
                    let y = &self.line.y;

                    // We're going to put `left_seg` after `right_seg` in the
                    // sweep line, and while doing so we need to "push" along
                    // all segments that are strictly bigger than `left_seg`
                    // (slight false positives are allowed).
                    let mut to_move = vec![(left_idx, self.line.segs[left_idx])];
                    for j in (left_idx + 1)..right_idx {
                        let seg = self.segments.get(self.line.segs[j]);
                        if left_seg.upper_bound(y, eps).lower < seg.lower_bound(y, eps).upper {
                            to_move.push((j, self.line.segs[j]));
                        }
                    }

                    // Remove them in reverse to make indexing easier.
                    for &(j, _) in to_move.iter().rev() {
                        self.remove(j);
                    }

                    // We want to insert them at what was previously `right_idx + 1`, but the
                    // index changed because of the removal.
                    let insertion_pos = right_idx + 1 - to_move.len();

                    for &(_, seg) in to_move.iter().rev() {
                        self.insert(insertion_pos, seg);
                    }
                }
            }
            SweepEventKind::Horizontal(seg_idx) => {
                self.line.horizontals.push(seg_idx);
            }
        }
    }

    pub fn finished(&self) -> bool {
        self.events.inner.is_empty()
    }

    pub fn check_invariants(&self) {
        assert!(self
            .line
            .find_invalid_order(&self.segments, &self.eps)
            .is_none());

        for i in 0..self.line.segs.len() {
            for j in (i + 1)..self.line.segs.len() {
                let segi = self.segments.get(self.line.segs[i]).to_exact();
                let segj = self.segments.get(self.line.segs[j]).to_exact();

                if let Some(y_int) = segi.exact_intersection_y(&segj) {
                    if y_int >= self.line.y.to_exact() {
                        // Find an event between i and j.
                        let is_between = |idx: SegIdx| -> bool {
                            self.line
                                .position(idx)
                                .map_or(false, |pos| i <= pos && pos <= j)
                        };
                        let has_witness = self.events.inner.iter().any(|ev| match &ev.0.kind {
                            SweepEventKind::Enter(_) | SweepEventKind::Horizontal(_) => false,
                            SweepEventKind::Intersection { left, right } => {
                                is_between(*left) && is_between(*right)
                            }
                            SweepEventKind::Exit(seg_idx) => is_between(*seg_idx),
                        });
                        assert!(has_witness);
                    }
                }
            }
        }
    }
}

impl<F: Float> Segment<F> {
    // Scale eps based on the slope of this line.
    //
    // The write-up used 1/(cos theta) for scaling. Here we use
    // the smaller (and therefore stricter) max(1, 1/|slope|) scaling,
    // because it's possible to compute exactly when doing rational
    // arithmetic.
    fn scaled_eps(&self, eps: &F) -> F {
        assert!(self.start.y < self.end.y);
        let dx = (self.end.x.clone() - &self.start.x).abs();
        let dy = self.end.y.clone() - &self.start.y;

        if dx <= dy {
            eps.clone()
        } else {
            (dx * eps) / dy
        }
    }

    // TODO: for a more efficient algorithm we can probably avoid tracking
    // intervals: we just need some analysis to bound our numerical error,
    // and then do some comparisons with epsilons.
    fn scaled_eps_bound(&self, eps: &F) -> Bounds<F> {
        if self.is_horizontal() {
            // This isn't really "correct"; the answer should be infinity. But in
            // the usages of this method it doesn't really matter. `lower_bound` and
            // `upper_bound` use `at_y_bound`, which gives the right endpoint on
            // horizontal segments.
            //
            // If we end up dropping the generic float, maybe it would make sense
            // to use infinity here instead.
            return Bounds::single(eps.clone());
        }

        let max_x = self.end.x.clone().max(self.start.x.clone());
        let min_x = self.end.x.clone().min(self.start.x.clone());
        let dx = Bounds::single(max_x) - Bounds::single(min_x);
        let dy = Bounds::single(self.end.y.clone()) - Bounds::single(self.start.y.clone());

        if dx.upper <= dy.lower {
            Bounds::single(eps.clone())
        } else {
            (dx * Bounds::single(eps.clone())) / dy
        }
    }

    /// The lower envelope of this segment at the given height.
    ///
    /// In the write-up this was called `alpha^-_(y,epsilon)`.
    fn lower(&self, y: &F, eps: &F) -> F {
        let min_x = self.end.x.clone().min(self.start.x.clone());

        (self.at_y(y) - self.scaled_eps(eps)).max(min_x - eps)
    }

    /// Like [`lower`], but returns an interval.
    fn lower_bound(&self, y: &F, eps: &F) -> Bounds<F> {
        let min_x = self.end.x.clone().min(self.start.x.clone());
        let scaled_eps = self.scaled_eps_bound(eps);

        (self.at_y_bound(y) - scaled_eps).max((min_x - eps).next_down())
    }

    fn upper(&self, y: &F, eps: &F) -> F {
        let max_x = self.end.x.clone().max(self.start.x.clone());

        (self.at_y(y) + self.scaled_eps(eps)).min(max_x + eps)
    }

    fn upper_bound(&self, y: &F, eps: &F) -> Bounds<F> {
        let max_x = self.end.x.clone().max(self.start.x.clone());
        let scaled_eps = self.scaled_eps_bound(eps);

        (self.at_y_bound(y) + scaled_eps).min((max_x + eps).next_up())
    }
}

impl<F: Float> WeakSweepLine<F> {
    /// If the ordering invariants fail, returns a pair of indices witnessing that failure.
    pub fn find_invalid_order(&self, segments: &Segments<F>, eps: &F) -> Option<(SegIdx, SegIdx)> {
        let eps = eps.to_exact();
        let y = self.y.to_exact();
        for i in 0..self.segs.len() {
            for j in (i + 1)..self.segs.len() {
                let segi = segments.get(self.segs[i]).to_exact();
                let segj = segments.get(self.segs[j]).to_exact();

                if segi.lower(&y, &eps) > segj.upper(&y, &eps) {
                    return Some((self.segs[i], self.segs[j]));
                }
            }
        }

        None
    }

    // Finds an index into this sweep line where it's ok to insert this new segment.
    fn insertion_idx(&self, segments: &Segments<F>, seg: &Segment<F>, eps: &F) -> usize {
        // Checks if `other` is smaller than `seg` with no false negatives: if `other` is actually smaller than `seg`
        // it will definitely return true.
        let maybe_strictly_smaller = |other: &SegIdx| -> bool {
            let other = segments.get(*other);
            other.upper_bound(&self.y, eps).lower < seg.lower_bound(&self.y, eps).upper
        };

        // The rust stdlib docs say that we're not allowed to do this, because our array isn't sorted
        // with respect to `maybe_strictly_smaller`. But for now at least, their implementation does a
        // normal binary search and so it's guaranteed to return an index where `maybe_strictly_smaller`
        // fails but the index before it succeeds.
        let search_start = self.segs.partition_point(maybe_strictly_smaller);
        let mut idx = search_start;
        for i in search_start..self.segs.len() {
            if maybe_strictly_smaller(&self.segs[i]) {
                idx = i + 1;
            }

            // Once we've found a segment whose lower bound is definitely bigger than seg's, there's no need
            // to look further.
            let other = segments.get(self.segs[i]);
            if other.lower_bound(&self.y, eps).lower >= seg.lower_bound(&self.y, eps).upper {
                break;
            }
        }
        idx
    }

    /// Marks as re-ordered all segments in the weakly-ordered sweep line that
    /// might intersect any horizontal segment.
    fn add_horizontal_reorders(&mut self, segments: &Segments<F>, eps: &F) {
        for &h_idx in &self.horizontals {
            let h_seg = segments.get(h_idx);

            // If there's a segment whose upper bound is less than seg.start.x, we
            // can ignore all it and everything to its left (even if those things to
            // its left have a bigger upper bound).
            //
            // Like in `WeakSweepLine::insertion_idx`, we're abusing the guarantees of
            // the stdlib binary search: the segments aren't guaranteed to be ordered,
            // but this should still find some index that evaluated to false, but whose
            // predecessor evaluated to true.
            let start_idx = self.segs.partition_point(|idx| {
                segments.get(*idx).upper_bound(&self.y, eps).upper < h_seg.start.x
            });

            for idx in &self.segs[start_idx..] {
                // We can stop once we've found a segment whose lower bound is definitely
                // past the horizontal segment.
                if segments.get(*idx).lower_bound(&self.y, eps).lower > h_seg.end.y {
                    break;
                }
                self.segs_needing_positions.insert(*idx);
            }
        }
    }

    // Find the position of the given segment in our array.
    //
    // TODO: if we're large, we could use a binary search.
    fn position(&self, seg: SegIdx) -> Option<usize> {
        self.segs.iter().position(|&x| x == seg)
    }

    // If this segment is in our line, find the subrange of our line that could possibly
    // influence `seg`'s position.
    fn influence_range(
        &self,
        seg: SegIdx,
        segments: &Segments<F>,
        eps: &F,
    ) -> Option<Range<usize>> {
        let idx = self.position(seg)?;
        let mut start_idx = idx;
        let mut seg_min = segments.get(seg).lower_bound(&self.y, eps).lower;

        for i in (0..idx).rev() {
            let prev_seg = segments.get(self.segs[i]);
            if prev_seg.upper_bound(&self.y, eps).upper < seg_min {
                break;
            } else {
                seg_min = prev_seg.lower_bound(&self.y, eps).lower;
                start_idx = i;
            }
        }

        let mut end_idx = idx + 1;
        let mut seg_max = segments.get(seg).upper_bound(&self.y, eps).upper;
        for i in (idx + 1)..self.segs.len() {
            let next_seg = segments.get(self.segs[i]);
            if next_seg.lower_bound(&self.y, eps).lower > seg_max {
                break;
            } else {
                seg_max = next_seg.upper_bound(&self.y, eps).upper;
                end_idx = i + 1;
            }
        }
        Some(start_idx..end_idx)
    }

    fn mark_contour_neighbor(&mut self, idx: SegIdx, enter: bool, segments: &Segments<F>) {
        let nbr = if segments.positively_oriented(idx) == enter {
            segments.contour_prev[idx.0]
        } else {
            segments.contour_next[idx.0]
        };
        let Some(nbr) = nbr else {
            return;
        };

        let seg_pos = self.position(idx);
        let nbr_pos = self.position(nbr);
        let Some((seg_pos, nbr_pos)) = seg_pos.zip(nbr_pos) else {
            return;
        };

        self.segs_needing_positions.extend(
            self.segs[seg_pos.min(nbr_pos)..=seg_pos.max(nbr_pos)]
                .iter()
                .copied(),
        );
    }

    /// Return all the segments in this sweep-line, along with a valid x position.
    ///
    /// TODO: this returns the smallest possible valid x position, which is correct but leads
    /// to weird output, with unnecessary horizontal segments. We can probably find a heuristic
    /// to improve this. (Like maybe also calculating the largest possible valid x position,
    /// and then choosing something in between.)
    fn ordered_xs<'a>(
        &'a self,
        segments: &'a Segments<F>,
        eps: &'a F,
    ) -> impl Iterator<Item = (SegIdx, F)> + 'a {
        let mut max_so_far = self
            .segs
            .first()
            .map(|seg| segments.get(*seg).lower(&self.y, eps))
            // If `self.segs` is empty our y doesn't matter; we're going to return
            // an empty iterator.
            .unwrap_or(F::from_f32(0.0));

        self.segs.iter().map(move |seg_idx| {
            let x = segments.get(*seg_idx).lower(&self.y, eps);
            max_so_far = max_so_far.clone().max(x);
            (*seg_idx, max_so_far.clone())
        })
    }

    /// Return a slice of segments in this sweep-line, along with a valid x position.
    ///
    /// TODO: this returns the smallest possible valid x position, which is correct but leads
    /// to weird output, with unnecessary horizontal segments. We can probably find a heuristic
    /// to improve this. (Like maybe also calculating the largest possible valid x position,
    /// and then choosing something in between.)
    fn ordered_partial_xs<'a>(
        &'a self,
        range: Range<usize>,
        segments: &'a Segments<F>,
        eps: &'a F,
    ) -> impl Iterator<Item = (SegIdx, F)> + 'a {
        let segs = &self.segs[range];
        let mut max_so_far = segs
            .first()
            .map(|seg| segments.get(*seg).lower(&self.y, eps))
            // If `self.segs` is empty our y doesn't matter; we're going to return
            // an empty iterator.
            .unwrap_or(F::from_f32(0.0));

        segs.iter().map(move |seg_idx| {
            let x = segments.get(*seg_idx).lower(&self.y, eps);
            max_so_far = max_so_far.clone().max(x);
            (*seg_idx, max_so_far.clone())
        })
    }
}

/// Runs a sweep over all the segments, returning a sweep line at every `y` where
/// there was an event.
pub fn sweep<F: Float>(
    segments: &Segments<F>,
    eps: &F,
) -> Vec<(WeakSweepLine<F>, WeakSweepLine<F>)> {
    let events = EventQueue {
        inner: segments
            .indices()
            .flat_map(|idx| {
                if segments.get(idx).is_horizontal() {
                    vec![SweepEvent {
                        y: segments.get(idx).start.y.clone(),
                        kind: SweepEventKind::Horizontal(idx),
                    }]
                } else {
                    let (a, b) = SweepEvent::from_segment(idx, segments);
                    vec![a, b]
                }
            })
            .map(std::cmp::Reverse)
            .collect(),
    };

    let line = WeakSweepLine::new(events.next_y().unwrap().clone());

    let mut state = State {
        eps: eps.clone(),
        line,
        events,
        segments: segments.clone(),
    };
    state.check_invariants();

    let mut ret = Vec::new();

    while let Some(y) = state.events.next_y().cloned() {
        state.advance(y.clone());
        state.check_invariants();
        // Process all the enter events at this y.
        while state.events.next_is_stage_1(&y) {
            state.step();
            state.check_invariants();
        }
        let old_line = state.line.clone();

        // Process all the reorderings
        while state.events.next_is_stage_2(&y) {
            state.step();
            state.check_invariants();
        }
        state.line.add_horizontal_reorders(segments, eps);

        // Process all the exit events at this y.
        while state.events.next_is_at(&y) {
            state.step();
            // This is a bit yucky, but we don't check the invariants after
            // processing exit events, because the intersection checking is
            // deferred until we advance the line.
        }
        state
            .line
            .segs_needing_positions
            .extend(state.line.exits.iter().copied());
        ret.push((old_line, state.line.clone()));
    }

    dbg!(ret)
}

impl<F: Float> SweepLine<F> {
    /// Adds to this sweep-line all horizontal segments that belong in it.
    fn add_horizontals(&mut self, horizontals: &[SegIdx], segments: &Segments<F>) {
        for &idx in horizontals {
            let seg = segments.get(idx);

            self.segs.push(SweepLineEntry {
                x: SweepLineSeg::EnterExit(
                    seg.start.x.clone().min(seg.end.x.clone()),
                    seg.start.x.clone().max(seg.end.x.clone()),
                ),
                idx,
            });
        }
    }
}

/// Converts a sequence of weakly-ordered sweep lines into a sequence
/// of actual sweep lines, in the naivest possibly way: subdividing every
/// segment at every sweep line.
pub fn weaks_to_sweeps_dense<F: Float>(
    weaks: &[(WeakSweepLine<F>, WeakSweepLine<F>)],
    segments: &Segments<F>,
    eps: &F,
) -> Vec<SweepLine<F>> {
    // The first sweep-line just has a single entry for everything
    let mut first_line = SweepLine {
        y: weaks[0].1.y.clone(),
        segs: weaks[0]
            .1
            .ordered_xs(segments, eps)
            .map(|(idx, x)| SweepLineEntry {
                idx,
                x: SweepLineSeg::Single(x),
            })
            .collect(),
    };

    first_line.add_horizontals(&weaks[0].1.horizontals, segments);

    let mut ret = vec![first_line];

    for (prev, line) in &weaks[1..] {
        // TODO: should be able to build things up in order by iterating over
        // both `prev` and `line` in one pass. But it isn't quite trivial
        // because we need to keep track of segments that were in one but
        // haven't yet been encountered in the other.
        let mut entries: HashMap<_, _> = prev
            .ordered_xs(segments, eps)
            .map(|(idx, x)| (idx, SweepLineSeg::Single(x)))
            .collect();

        for (idx, x) in line.ordered_xs(segments, eps) {
            match entries.entry(idx) {
                std::collections::hash_map::Entry::Occupied(mut occ) => {
                    let SweepLineSeg::Single(enter_x) = occ.get().clone() else {
                        unreachable!()
                    };
                    *occ.get_mut() = SweepLineSeg::EnterExit(enter_x, x);
                }
                std::collections::hash_map::Entry::Vacant(vac) => {
                    vac.insert(SweepLineSeg::Single(x));
                }
            }
        }

        let entries: Vec<_> = entries
            .into_iter()
            .map(|(idx, x)| SweepLineEntry { idx, x })
            .collect();

        let mut sweep_line = SweepLine {
            y: line.y.clone(),
            segs: entries,
        };
        sweep_line.add_horizontals(&line.horizontals, segments);
        sweep_line.segs.sort();
        ret.push(sweep_line);
    }

    ret
}

/// Converts a sequence of weakly-ordered sweep lines into a sequence
/// of actual sweep lines, while trying not to add in two many subdivisions.
pub fn weaks_to_sweeps_sparse<F: Float>(
    weaks: &[(WeakSweepLine<F>, WeakSweepLine<F>)],
    segments: &Segments<F>,
    eps: &F,
) -> Vec<SweepLine<F>> {
    // The first sweep-line just has a single entry for everything
    let mut first_line = SweepLine {
        y: weaks[0].1.y.clone(),
        segs: weaks[0]
            .1
            .ordered_xs(segments, eps)
            .map(|(idx, x)| SweepLineEntry {
                idx,
                x: SweepLineSeg::Single(x),
            })
            .collect(),
    };
    first_line.add_horizontals(&weaks[0].1.horizontals, segments);

    let mut ret = vec![first_line];

    for (prev, line) in &weaks[1..] {
        let segs: Vec<_> = line.segs_needing_positions.iter().cloned().collect();
        let mut processed_segs = HashSet::new();

        let mut entries = HashMap::new();
        for &seg in &segs {
            if processed_segs.contains(&seg) {
                continue;
            }
            if let Some(range) = prev.influence_range(seg, segments, eps) {
                entries.extend(
                    prev.ordered_partial_xs(range.clone(), segments, eps)
                        .map(|(idx, x)| (idx, SweepLineSeg::Single(x))),
                );
                processed_segs.extend(prev.segs[range].iter().cloned());
            }
        }

        let mut processed_segs = HashSet::new();
        for &seg in &segs {
            if processed_segs.contains(&seg) {
                continue;
            }

            let Some(range) = line.influence_range(seg, segments, eps) else {
                continue;
            };
            for (idx, x) in line.ordered_partial_xs(range.clone(), segments, eps) {
                match entries.entry(idx) {
                    std::collections::hash_map::Entry::Occupied(mut occ) => {
                        let SweepLineSeg::Single(enter_x) = occ.get().clone() else {
                            unreachable!()
                        };
                        if !line.exits.contains(&idx) && !line.entrances.contains(&idx) {
                            *occ.get_mut() = SweepLineSeg::EnterExit(enter_x, x);
                        }
                    }
                    std::collections::hash_map::Entry::Vacant(vac) => {
                        vac.insert(SweepLineSeg::Single(x));
                    }
                }
            }
            processed_segs.extend(line.segs[range].iter().cloned());
        }

        let entries: Vec<_> = entries
            .into_iter()
            .map(|(idx, x)| SweepLineEntry { idx, x })
            .collect();

        let mut sweep_line = SweepLine {
            y: line.y.clone(),
            segs: entries,
        };
        sweep_line.add_horizontals(&line.horizontals, segments);
        sweep_line.segs.sort();
        ret.push(sweep_line);
    }

    ret
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum OutputEventKind<F: Float> {
    Enter(F),
    Exit(F),
    PassThrough(F),
    // Potentially, we could divide this variant up into:
    // - part of a real horizontal segment
    // - a horizontal part of a segment that continues through this sweep line
    // - a horizontal bit introduced to join two adjacent parts of the contour.
    // The bool is true if the order of this segment agrees with the sweep-order
    // (not the oriented order!) of the segment it's a part of.
    Horizontal(F, F, bool),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OutputEvent<F: Float> {
    pub seg: SegIdx,
    pub y: F,
    pub x: OutputEventKind<F>,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct HSeg<F: Float> {
    end: F,
    enter_first: bool,
    contour_connector: bool,
    seg: SegIdx,
}

/// Converts a sequence of weakly-ordered sweep lines into a sequence
/// of actual sweep lines, while trying not to add in two many subdivisions.
///
/// TODO: I started doing trying the lazy version of this, but I think it will
/// be easier with a refactored weak sweep structure. If we snapshot the line
/// (1) after the enter events, and (2) after the intersection events but before
/// the exit events, then the indices between the two snapshots will line up,
/// and make it easier to do the sparse processing to both lines at once.
///
/// First, in order to test the interface, here is an implementation that
/// first converts to sweep lines.
pub fn weaks_to_events_sparse<F: Float, C: FnMut(OutputEvent<F>)>(
    weaks: &[(WeakSweepLine<F>, WeakSweepLine<F>)],
    segments: &Segments<F>,
    eps: &F,
    mut callback: C,
) {
    let sweeps = weaks_to_sweeps_sparse(weaks, segments, eps);

    for line in sweeps {
        // TODO: We only need heap operations; maybe that's more efficient than a BTreeSet?
        let mut active_horizontals: BTreeSet<HSeg<F>> = BTreeSet::new();
        let positions: HashMap<SegIdx, usize> = line
            .segs
            .iter()
            .enumerate()
            .map(|(pos, seg)| (seg.idx, pos))
            .collect();
        let mut last_x: Option<F> = None;
        for seg in &line.segs {
            let x = seg.x.smaller_x().clone();
            for h in &active_horizontals {
                // unwrap: on the first event of this sweep line, active_horizontals is empty. So
                // we only get here after last_x is populated.
                callback(OutputEvent {
                    seg: h.seg,
                    y: line.y.clone(),
                    x: OutputEventKind::Horizontal(
                        last_x.clone().unwrap(),
                        h.end.clone().min(x.clone()),
                        h.enter_first,
                    ),
                });
            }

            // Drain the active horizontals, throwing away horizontal segments that end before
            // the new x position.
            while let Some(h) = active_horizontals.first() {
                if h.end <= x {
                    let event_x = h.end.clone().min(x.clone());
                    let kind = if h.enter_first {
                        OutputEventKind::Exit(event_x)
                    } else {
                        OutputEventKind::Enter(event_x)
                    };
                    if h.end < x || !h.contour_connector {
                        callback(OutputEvent {
                            seg: h.seg,
                            y: line.y.clone(),
                            x: kind,
                        });
                    }
                    active_horizontals.pop_first();
                } else {
                    break;
                }
            }

            match &seg.x {
                SweepLineSeg::Single(x) => {
                    let s = segments.get(seg.idx);
                    let kind = match (s.start.y < line.y, line.y < s.end.y) {
                        (true, false) => OutputEventKind::Enter(x.clone()),
                        (false, true) => OutputEventKind::Exit(x.clone()),
                        (true, true) => {
                            // We'd like this to be unreachable, but it actually gets reached. I think
                            // it's because of influence_range not always lining up between the previous
                            // line and the new one.
                            OutputEventKind::PassThrough(x.clone())
                        }

                        (false, false) => unreachable!(),
                    };

                    callback(OutputEvent {
                        seg: seg.idx,
                        y: line.y.clone(),
                        x: kind,
                    });

                    let next_nbr = segments.contour_next[seg.idx.0].and_then(|n| positions.get(&n));
                    if let Some(next_nbr) = next_nbr {
                        let next_nbr_start = line.segs[*next_nbr].x.smaller_x();
                        if next_nbr_start > x {
                            active_horizontals.insert(HSeg {
                                end: next_nbr_start.clone(),
                                enter_first: true,
                                seg: seg.idx,
                                contour_connector: true,
                            });
                        }
                    }

                    let prev_nbr = segments.contour_prev[seg.idx.0].and_then(|n| positions.get(&n));
                    if let Some(prev_nbr) = prev_nbr {
                        let prev_nbr_start = line.segs[*prev_nbr].x.smaller_x();
                        if prev_nbr_start > x {
                            active_horizontals.insert(HSeg {
                                end: prev_nbr_start.clone(),
                                enter_first: false,
                                seg: seg.idx,
                                contour_connector: true,
                            });
                        }
                    }
                }
                SweepLineSeg::EnterExit(enter_x, exit_x) => {
                    let kind = match enter_x.cmp(exit_x) {
                        std::cmp::Ordering::Less => {
                            active_horizontals.insert(HSeg {
                                end: seg.x.larger_x().clone(),
                                seg: seg.idx,
                                enter_first: true,
                                contour_connector: false,
                            });
                            OutputEventKind::Enter(enter_x.clone())
                        }
                        std::cmp::Ordering::Greater => {
                            active_horizontals.insert(HSeg {
                                end: seg.x.larger_x().clone(),
                                seg: seg.idx,
                                enter_first: false,
                                contour_connector: false,
                            });
                            OutputEventKind::Exit(exit_x.clone())
                        }
                        std::cmp::Ordering::Equal => OutputEventKind::PassThrough(enter_x.clone()),
                    };

                    callback(OutputEvent {
                        seg: seg.idx,
                        y: line.y.clone(),
                        x: kind,
                    });
                }
            }
            last_x = Some(x);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ordered_float::NotNan;
    use proptest::prelude::*;

    use crate::{
        geom::{Point, Segment},
        perturbation::{
            f32_perturbation, f64_perturbation, perturbation, rational_perturbation,
            realize_perturbation, FloatPerturbation, Perturbation,
        },
        sweep::Segments,
    };

    fn mk_segs(xs: &[(f64, f64)]) -> Segments<NotNan<f64>> {
        let y0: NotNan<f64> = 0.0.try_into().unwrap();
        let y1: NotNan<f64> = 1.0.try_into().unwrap();
        let mut segs = Segments::default();

        for &(x0, x1) in xs {
            segs.add_points(
                [
                    Point::new(x0.try_into().unwrap(), y0),
                    Point::new(x1.try_into().unwrap(), y1),
                ],
                false,
            );
        }
        segs
    }

    #[test]
    fn invalid_order() {
        fn check_order(xs: &[(f64, f64)], at: f64, eps: f64) -> Option<(usize, usize)> {
            let eps: NotNan<f64> = eps.try_into().unwrap();
            let y: NotNan<f64> = at.try_into().unwrap();
            let segs = mk_segs(xs);

            let line = WeakSweepLine::new_with_segs(y, (0..xs.len()).map(SegIdx).collect());

            line.find_invalid_order(&segs, &eps)
                .map(|(a, b)| (a.0, b.0))
        }

        let crossing = &[(-1.0, 1.0), (1.0, -1.0)];
        let eps = 1.0 / 128.0;
        assert!(check_order(crossing, 0.0, eps).is_none());
        assert!(check_order(crossing, 0.5, eps).is_none());
        assert_eq!(check_order(crossing, 1.0, eps), Some((0, 1)));

        let not_quite_crossing = &[(-0.75 * eps, 0.75 * eps), (0.75 * eps, -0.75 * eps)];
        assert!(check_order(not_quite_crossing, 0.0, eps).is_none());
        assert!(check_order(not_quite_crossing, 0.5, eps).is_none());
        assert!(check_order(not_quite_crossing, 1.0, eps).is_none());

        let barely_crossing = &[(-1.5 * eps, 1.5 * eps), (1.5 * eps, -1.5 * eps)];
        assert!(check_order(barely_crossing, 0.0, eps).is_none());
        assert!(check_order(barely_crossing, 0.5, eps).is_none());
        assert_eq!(check_order(barely_crossing, 1.0, eps), Some((0, 1)));

        let non_adj_crossing = &[(-1.5 * eps, 1.5 * eps), (0.0, 0.0), (1.5 * eps, -1.5 * eps)];
        assert!(check_order(non_adj_crossing, 0.0, eps).is_none());
        assert!(check_order(non_adj_crossing, 0.5, eps).is_none());
        assert_eq!(check_order(non_adj_crossing, 1.0, eps), Some((0, 2)));

        let flat_crossing = &[(-1e6, 1e6), (-10.0 * eps, -10.0 * eps)];
        assert_eq!(check_order(flat_crossing, 0.5, eps), None);

        let end_crossing_bevel = &[(2.5 * eps, 2.5 * eps), (-1e6, 0.0)];
        assert_eq!(check_order(end_crossing_bevel, 1.0, eps), Some((0, 1)));

        let start_crossing_bevel = &[(2.5 * eps, 2.5 * eps), (0.0, -1e6)];
        assert_eq!(check_order(start_crossing_bevel, 1.0, eps), Some((0, 1)));
    }

    #[test]
    fn insertion_idx() {
        fn insert(xs: &[(f64, f64)], new: (f64, f64), at: f64, eps: f64) -> usize {
            let eps: NotNan<f64> = eps.try_into().unwrap();
            let y: NotNan<f64> = at.try_into().unwrap();
            let y0: NotNan<f64> = 0.0.try_into().unwrap();
            let y1: NotNan<f64> = 1.0.try_into().unwrap();
            let segs = mk_segs(xs);

            let x0: NotNan<f64> = new.0.try_into().unwrap();
            let x1: NotNan<f64> = new.1.try_into().unwrap();
            let new = Segment {
                start: Point::new(x0, y0),
                end: Point::new(x1, y1),
            };

            let line = WeakSweepLine::new_with_segs(y, (0..xs.len()).map(SegIdx).collect());
            line.insertion_idx(&segs, &new, &eps)
        }

        let eps = 1.0 / 128.0;
        assert_eq!(
            insert(&[(-1.0, -1.0), (1.0, 1.0)], (-2.0, 0.0), 0.0, eps),
            0
        );
        assert_eq!(insert(&[(-1.0, -1.0), (1.0, 1.0)], (0.0, 0.0), 0.0, eps), 1);
        assert_eq!(insert(&[(-1.0, -1.0), (1.0, 1.0)], (2.0, 0.0), 0.0, eps), 2);

        assert_eq!(
            insert(
                &[(-1e6, 1e6), (-1.0, -1.0), (1.0, 1.0)],
                (0.0, 0.0),
                0.5,
                eps
            ),
            2
        );
        assert_eq!(
            insert(
                &[
                    (-1e6, 1e6),
                    (-1e6, 1e6),
                    (-1e6, 1e6),
                    (-1.0, -1.0),
                    (1.0, 1.0),
                    (-1e6, 1e6),
                    (-1e6, 1e6),
                    (-1e6, 1e6),
                ],
                (0.0, 0.0),
                0.5,
                eps
            ),
            4
        );
    }

    #[test]
    fn test_sweep() {
        let eps = NotNan::new(0.01).unwrap();

        let segs = mk_segs(&[(0.0, 0.0), (1.0, 1.0), (-2.0, 2.0)]);
        dbg!(&segs);
        let lines = sweep(&segs, &eps);
        dbg!(&lines);
        assert_eq!(4, lines.len());
        //dbg!(&weaks_to_sweeps_dense(&lines, &segs, &eps));
        weaks_to_events_sparse(&lines, &segs, &eps, |ev| {
            dbg!(ev);
        });
    }

    #[test]
    fn test_sweep_with_horizontals() {
        let eps = NotNan::new(0.01).unwrap();
        let h = |y: f64| -> [Point<NotNan<f64>>; 2] {
            [
                Point::new(
                    NotNan::try_from(-10.0).unwrap(),
                    NotNan::try_from(y).unwrap(),
                ),
                Point::new(
                    NotNan::try_from(10.0).unwrap(),
                    NotNan::try_from(y).unwrap(),
                ),
            ]
        };

        let segs = mk_segs(&[(0.0, 0.0), (1.0, 1.0), (-2.0, 2.0)]);

        let mut segs1 = segs.clone();
        segs1.add_points(h(-5.0), false);
        let lines = sweep(&segs1, &eps);
        let lines = &weaks_to_sweeps_dense(&lines, &segs1, &eps);
        // TODO: maybe snapshot tests?
        dbg!(&lines);
        assert_eq!(lines.len(), 5);

        let mut segs2 = segs.clone();
        segs2.add_points(h(0.75), false);
        let lines = sweep(&segs2, &eps);
        let lines = &weaks_to_sweeps_dense(&lines, &segs2, &eps);
        // TODO: maybe snapshot tests?
        dbg!(&lines);
        assert_eq!(lines.len(), 5);

        let mut segs3 = segs.clone();
        segs3.add_points(h(1.0), false);
        segs3.add_points(h(2.0), false);
        let lines = sweep(&segs3, &eps);
        let lines = &weaks_to_sweeps_dense(&lines, &segs3, &eps);
        // TODO: maybe snapshot tests?
        dbg!(&lines);
        assert_eq!(lines.len(), 5);
    }

    fn p<F: Float>(x: f32, y: f32) -> Point<F> {
        Point::new(F::from_f32(x), F::from_f32(y))
    }

    fn run_perturbation<P: FloatPerturbation>(ps: Vec<Perturbation<P>>) {
        let base = vec![vec![
            p(0.0, 0.0),
            p(1.0, 1.0),
            p(1.0, -1.0),
            p(2.0, 0.0),
            p(1.0, 1.0),
            p(1.0, -1.0),
        ]];

        let perturbed_polylines = ps
            .iter()
            .map(|p| realize_perturbation(&base, p))
            .collect::<Vec<_>>();
        let mut segs = Segments::default();
        for poly in perturbed_polylines {
            segs.add_points(poly, true);
        }
        let eps = P::Float::from_f32(0.1);
        let weaks = sweep(&segs, &eps);
        let _sweeps = weaks_to_sweeps_dense(&weaks, &segs, &eps);
    }

    proptest! {
    #[test]
    fn perturbation_test_f64(perturbations in prop::collection::vec(perturbation(f64_perturbation(0.1)), 1..5)) {
        run_perturbation(perturbations);
    }

    #[test]
    fn perturbation_test_f32(perturbations in prop::collection::vec(perturbation(f32_perturbation(0.1)), 1..5)) {
        run_perturbation(perturbations);
    }

    #[test]
    fn perturbation_test_rational(perturbations in prop::collection::vec(perturbation(rational_perturbation(0.1.try_into().unwrap())), 1..5)) {
        run_perturbation(perturbations);
    }
    }
}
