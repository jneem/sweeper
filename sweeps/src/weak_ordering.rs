//! A sweep-line implementation using weak orderings.
//!
//! This algorithm is documented in `docs/sweep.typ`.

// TODO:
// - investigate better insertion heuristics: if there are a bunch of insertions at the same point, we
//   currently put them in some arbitrary order and then later have to process a bunch of intersections

use std::collections::BTreeSet;
use std::ops::Range;
use std::{
    cmp::Reverse,
    collections::{HashMap, HashSet},
};

use malachite::Rational;

use crate::{
    geom::Segment,
    num::Float,
    segments::{SegIdx, Segments},
    sweep::{SweepEvent, SweepEventKind},
};

#[derive(Clone, Debug, Default)]
pub(crate) struct SegmentOrder {
    pub(crate) segs: Vec<SegIdx>,
}

impl FromIterator<SegIdx> for SegmentOrder {
    fn from_iter<T: IntoIterator<Item = SegIdx>>(iter: T) -> Self {
        SegmentOrder {
            segs: iter.into_iter().collect(),
        }
    }
}

#[derive(Clone, Debug)]
pub struct EventQueue<F: Float> {
    inner: std::collections::BinaryHeap<std::cmp::Reverse<SweepEvent<F>>>,
}

impl<F: Float> EventQueue<F> {
    /// Builds an event queue containing the starting and ending positions
    /// of all the  segments.
    ///
    /// The returned event queue will not contain any intersection events.
    pub fn from_segments(segments: &Segments<F>) -> Self {
        // Non-horizontal segments take up two events, so allocate for twice the number of segments.
        let mut inner = std::collections::BinaryHeap::with_capacity(segments.segs.len() * 2);

        for seg in segments.indices() {
            if segments.get(seg).is_horizontal() {
                inner.push(std::cmp::Reverse(SweepEvent {
                    y: segments.get(seg).start.y.clone(),
                    kind: SweepEventKind::Horizontal(seg),
                }));
            } else {
                let (a, b) = SweepEvent::from_segment(seg, segments);
                inner.push(std::cmp::Reverse(a));
                inner.push(std::cmp::Reverse(b));
            }
        }

        Self { inner }
    }

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
            && self.next_kind().is_some_and(|kind| match kind {
                SweepEventKind::Enter(_) | SweepEventKind::Horizontal(_) => true,
                SweepEventKind::Intersection { .. } | SweepEventKind::Exit(_) => false,
            })
    }

    pub fn next_is_stage_2(&self, y: &F) -> bool {
        self.next_y() == Some(y)
            && self.next_kind().is_some_and(|kind| match kind {
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
    pub y: F,
    pub eps: F,
    pub line: SegmentOrder,
    pub old_line: SegmentOrder,
    pub events: EventQueue<F>,
    // TODO: maybe borrow Segments?
    pub segments: Segments<F>,

    // For the sparse realization, this is the collection of segments that
    // we know need to be given explicit positions in the current sweep line.
    //
    // These include:
    // - any segments that changed order with any other segments
    // - any segments that entered or exited
    // - any segments that are between the endpoints of contour-adjacent segments.
    pub segs_needing_positions: HashSet<SegIdx>,
    // Segments marked as having exited the sweep-line. We don't remove them
    // immediately because that shifts indices around and makes it harder to
    // compare old vs. new sweep-lines. Instead, we remember that we're supposed
    // to remove them and then actually remove them when we advance `y`.
    //
    // This could potentially be part of the `segs` list instead of as a separate
    // map.
    pub exits: HashSet<SegIdx>,
    pub entrances: HashSet<SegIdx>,
}

impl<F: Float> State<F> {
    pub fn new(segments: &Segments<F>, eps: F) -> Self {
        let events = EventQueue::from_segments(segments);

        State {
            eps,
            old_line: SegmentOrder::default(),
            line: SegmentOrder::default(),
            y: events.next_y().unwrap().clone(),
            events,
            segments: segments.clone(),
            segs_needing_positions: HashSet::new(),
            exits: HashSet::new(),
            entrances: HashSet::new(),
        }
    }

    pub fn next_line(&mut self) -> Option<SweepLine<'_, F>> {
        // Process the exits from the last y position.
        self.process_exits();
        #[cfg(debug_assertions)]
        self.check_invariants();

        let y = self.events.next_y().cloned()?;
        self.advance(y.clone());
        #[cfg(debug_assertions)]
        self.check_invariants();

        // Process all the enter events at this y.
        while self.events.next_is_stage_1(&y) {
            self.step();
            #[cfg(debug_assertions)]
            self.check_invariants();
        }

        // Copy the new line to the old line. Basically self.old_line = self.line.clone(), but keeping the
        // old allocation.
        self.old_line.segs.clear();
        self.old_line.segs.extend_from_slice(&self.line.segs);

        // Process all the reorderings
        while self.events.next_is_stage_2(&y) {
            self.step();
            #[cfg(debug_assertions)]
            self.check_invariants();
        }

        // Process all the exit events at this y.
        while self.events.next_is_at(&y) {
            self.step();
            #[cfg(debug_assertions)]
            self.check_invariants();
        }
        self.segs_needing_positions
            .extend(self.exits.iter().copied());

        Some(SweepLine {
            y: &self.y,
            old_line: &self.old_line,
            new_line: &self.line,
            segs_needing_positions: &self.segs_needing_positions,
            exits: &self.exits,
            entrances: &self.entrances,
        })
    }

    fn process_exits(&mut self) {
        for &seg_idx in &self.exits {
            let pos = self
                .line
                .position(seg_idx)
                .expect("exit for a segment we don't have");
            self.line.segs.remove(pos);
        }
        self.exits.clear();
    }

    pub fn advance(&mut self, y: F) {
        self.process_exits();
        self.y = y;
        self.segs_needing_positions.clear();
        self.entrances.clear();
    }

    pub fn intersection_scan_right(&mut self, start_idx: usize) {
        let seg = self.segments.get(self.line.segs[start_idx]);
        let y = &self.y;

        // We're allowed to take a potentially-smaller height bound by taking
        // into account the current queue. A larger height bound is still ok,
        // just a little slower.
        let mut height_bound = seg.end.y.clone();

        for j in (start_idx + 1)..self.line.segs.len() {
            if self.exits.contains(&self.line.segs[j]) {
                continue;
            }
            let other = self.segments.get(self.line.segs[j]);
            height_bound = height_bound.min(other.end.y.clone());

            if let Some(int_y) = seg.crossing_y(other, &self.eps) {
                self.events.push(SweepEvent::intersection(
                    self.line.segs[start_idx],
                    self.line.segs[j],
                    int_y.clone().max(y.clone()),
                ));
                height_bound = int_y.min(height_bound);
            }

            // For the early stopping, we need to check whether `seg` is less than `other`'s lower
            // bound on the whole interesting `y` interval. Since they're lines, it's enough to check
            // at the two interval endpoints.
            let y1 = &height_bound;
            let threshold = self.eps.clone() / F::from_f32(4.0);
            if threshold <= other.lower(y, &self.eps) - seg.at_y(y)
                && threshold <= other.lower(y1, &self.eps) - seg.at_y(y1)
            {
                break;
            }
        }
    }

    pub fn intersection_scan_left(&mut self, start_idx: usize) {
        let seg = self.segments.get(self.line.segs[start_idx]);
        let y = &self.y;

        let mut height_bound = seg.end.y.clone();

        for j in (0..start_idx).rev() {
            if self.exits.contains(&self.line.segs[j]) {
                continue;
            }
            let other = self.segments.get(self.line.segs[j]);
            height_bound = height_bound.min(other.end.y.clone());
            if let Some(int_y) = other.crossing_y(seg, &self.eps) {
                self.events.push(SweepEvent::intersection(
                    self.line.segs[j],
                    self.line.segs[start_idx],
                    int_y.clone().max(self.y.clone()),
                ));
                height_bound = int_y.min(height_bound);
            }

            // For the early stopping, we need to check whether `seg` is greater than `other`'s upper
            // bound on the whole interesting `y` interval. Since they're lines, it's enough to check
            // at the two interval endpoints.
            let y1 = &height_bound;
            let threshold = self.eps.clone() / F::from_f32(4.0);
            if seg.at_y(y) - other.upper(y, &self.eps) > threshold
                && seg.at_y(y1) - other.upper(y1, &self.eps) > threshold
            {
                break;
            }
        }
    }

    fn scan_for_removal(&mut self, pos: usize) {
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

        assert!(self.y == ev.y);
        match ev.kind {
            SweepEventKind::Enter(seg_idx) => {
                let new_seg = self.segments.get(seg_idx);
                let pos = self
                    .line
                    .insertion_idx(&self.y, &self.segments, new_seg, &self.eps);
                self.insert(pos, seg_idx);
                self.segs_needing_positions.insert(seg_idx);
                self.mark_endpoint(seg_idx, pos, true);
                self.entrances.insert(seg_idx);
            }
            SweepEventKind::Exit(seg_idx) => {
                // It's important that this goes before `scan_for_removal`, so that
                // the scan doesn't get confused by the segment that should be marked
                // for exit.
                self.exits.insert(seg_idx);
                let pos = self
                    .line
                    .position(seg_idx)
                    .expect("exit for a segment we don't have");
                self.scan_for_removal(pos);
                self.segs_needing_positions.insert(seg_idx);
                self.mark_endpoint(seg_idx, pos, false);
            }
            SweepEventKind::Intersection { left, right } => {
                let left_idx = self.line.segs.iter().position(|&x| x == left).unwrap();
                let right_idx = self.line.segs.iter().position(|&x| x == right).unwrap();
                if left_idx < right_idx {
                    self.segs_needing_positions
                        .extend(&self.line.segs[left_idx..=right_idx]);
                    let left_seg = self.segments.get(left);
                    let eps = &self.eps;
                    let y = &self.y;

                    // We're going to put `left_seg` after `right_seg` in the
                    // sweep line, and while doing so we need to "push" along
                    // all segments that are strictly bigger than `left_seg`
                    // (slight false positives are allowed; no false negatives).
                    let mut to_move = vec![(left_idx, self.line.segs[left_idx])];
                    let threshold = eps.clone() / F::from_f32(-4.0);
                    for j in (left_idx + 1)..right_idx {
                        let seg = self.segments.get(self.line.segs[j]);
                        if seg.lower(y, eps) - left_seg.upper(y, eps) > threshold {
                            to_move.push((j, self.line.segs[j]));
                        }
                    }

                    // Remove them in reverse to make indexing easier.
                    for &(j, _) in to_move.iter().rev() {
                        self.line.segs.remove(j);
                        self.scan_for_removal(j);
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
                let new_seg = self.segments.get(seg_idx);
                let pos = self
                    .line
                    .insertion_idx(&self.y, &self.segments, new_seg, &self.eps);
                self.insert(pos, seg_idx);
                self.segs_needing_positions.insert(seg_idx);
                self.mark_endpoint(seg_idx, pos, true);
                self.mark_endpoint(seg_idx, pos, false);
                self.entrances.insert(seg_idx);
                self.exits.insert(seg_idx);
            }
        }
    }

    pub fn check_invariants(&self) {
        for ev in &self.events.inner {
            assert!(
                ev.0.y >= self.y,
                "at y={:?}, event {:?} occurred in the past",
                &self.y,
                &ev
            );
        }

        for &seg_idx in &self.line.segs {
            let seg = self.segments.get(seg_idx);
            assert!(
                (&seg.start.y..=&seg.end.y).contains(&&self.y),
                "segment {seg:?} out of range at y={:?}",
                self.y
            );
        }

        assert!(self
            .line
            .find_invalid_order(&self.y, &self.segments, &self.eps)
            .is_none());

        let eps = self.eps.to_exact();
        for i in 0..self.line.segs.len() {
            if self.exits.contains(&self.line.segs[i]) {
                continue;
            }
            for j in (i + 1)..self.line.segs.len() {
                if self.exits.contains(&self.line.segs[j]) {
                    continue;
                }
                let segi = self.segments.get(self.line.segs[i]).to_exact();
                let segj = self.segments.get(self.line.segs[j]).to_exact();

                if let Some(y_int) = segi.exact_eps_crossing(&segj, &eps) {
                    if y_int >= self.y.to_exact() {
                        // Find an event between i and j.
                        let is_between = |idx: SegIdx| -> bool {
                            self.line
                                .position(idx)
                                .is_some_and(|pos| i <= pos && pos <= j)
                        };
                        let has_witness = self.events.inner.iter().any(|ev| {
                            let is_between = match &ev.0.kind {
                                SweepEventKind::Enter(_) | SweepEventKind::Horizontal(_) => false,
                                SweepEventKind::Intersection { left, right } => {
                                    is_between(*left) && is_between(*right)
                                }
                                SweepEventKind::Exit(seg_idx) => is_between(*seg_idx),
                            };
                            let before_y = ev.0.y.to_exact() <= y_int;
                            is_between && before_y
                        });
                        assert!(
                            has_witness,
                            "segments {:?} and {:?} cross at {:?}, but there is no witness",
                            self.line.segs[i], self.line.segs[j], y_int
                        );
                    }
                }
            }
        }
    }

    /// The segment `idx` just entered (or exited) at index `idx`. If any of
    /// the nearby (in the sweep-line order) segments are nearby (physically),
    /// record the fact that they need to be given explicit horizontal
    /// positions.
    fn mark_endpoint(&mut self, idx: SegIdx, pos: usize, enter: bool) {
        let x = if enter {
            &self.segments.get(idx).start.x
        } else {
            &self.segments.get(idx).end.x
        };

        // We'll look at horizontal positions to figure out where to stop searching
        // for nearby points. Those are accurate to eps/8, so set a threshold at eps/4.
        let slack = self.eps.clone() / F::from_f32(4.0);
        for &seg_idx in &self.line.segs[(pos + 1)..] {
            if self.segments.get(seg_idx).lower(&self.y, &self.eps) - x.clone() > slack {
                break;
            }
            self.segs_needing_positions.insert(seg_idx);
        }
        for &seg_idx in self.line.segs[0..pos].iter().rev() {
            if self.segments.get(seg_idx).at_y(&self.y) - x.clone() < -slack.clone() {
                break;
            }
            self.segs_needing_positions.insert(seg_idx);
        }
    }
}

impl Segment<Rational> {
    // The moment our lower bound crosses to the right of `other`'s upper bound.
    // (Actually, it could give too large a value right now, because it doesn't take the
    // "chamfers" into account.)
    pub fn exact_eps_crossing(&self, other: &Self, eps: &Rational) -> Option<Rational> {
        let y0 = self.start.y.clone().max(other.start.y.clone());
        let y1 = self.end.y.clone().min(other.end.y.clone());
        let scaled_eps = self.scaled_eps(eps);

        assert!(y1 >= y0);

        let dx0 = other.at_y(&y0) - self.at_y(&y0) + scaled_eps.clone() * Rational::from(2);
        let dx1 = other.at_y(&y1) - self.at_y(&y1) + scaled_eps * Rational::from(2);
        if dx0 == dx1 {
            // They're parallel.
            (dx0 == 0).then_some(y0)
        } else if dx1 < 0 {
            let t = &dx0 / (&dx0 - dx1);
            (0..=1).contains(&t).then(|| &y0 + t * (y1 - &y0))
        } else {
            None
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
        assert!(self.start.y <= self.end.y);
        if self.start.y == self.end.y {
            // See `scaled_eps_bound`
            return eps.clone();
        }

        let dx = (self.end.x.clone() - &self.start.x).abs();
        let dy = self.end.y.clone() - &self.start.y;

        if dx <= dy {
            eps.clone()
        } else {
            (dx * eps) / dy
        }
    }

    /// The lower envelope of this segment at the given height.
    ///
    /// In the write-up this was called `alpha^-_(y,epsilon)`.
    fn lower(&self, y: &F, eps: &F) -> F {
        let min_x = self.end.x.clone().min(self.start.x.clone());

        (self.at_y(y) - self.scaled_eps(eps)).max(min_x - eps)
    }

    fn upper(&self, y: &F, eps: &F) -> F {
        let max_x = self.end.x.clone().max(self.start.x.clone());

        (self.at_y(y) + self.scaled_eps(eps)).min(max_x + eps)
    }
}

impl SegmentOrder {
    /// If the ordering invariants fail, returns a pair of indices witnessing that failure.
    fn find_invalid_order<F: Float>(
        &self,
        y: &F,
        segments: &Segments<F>,
        eps: &F,
    ) -> Option<(SegIdx, SegIdx)> {
        let eps = eps.to_exact();
        let y = y.to_exact();
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
    fn insertion_idx<F: Float>(
        &self,
        y: &F,
        segments: &Segments<F>,
        seg: &Segment<F>,
        eps: &F,
    ) -> usize {
        // Checks if `other` is smaller than `seg` with no false negatives: if `other` is actually smaller than `seg`
        // it will definitely return true.
        let maybe_strictly_smaller = |other: &SegIdx| -> bool {
            let other = segments.get(*other);
            // `at_y` is guaranteed to have accuracy eps/8, and in order to have a strict segment inequality there
            // needs to be a difference of at least 2*eps (more, if there's a slope).
            other.at_y(y) < seg.at_y(y)
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
            // `lower` is accurate to within eps/8, so if this test succeeds then other's lower bound is
            // definitely bigger.
            if other.lower(y, eps) - seg.lower(y, eps) >= eps.clone() / F::from_f32(4.0) {
                break;
            }
        }
        idx
    }

    // Find the position of the given segment in our array.
    //
    // TODO: if we're large, we could use a binary search.
    fn position(&self, seg: SegIdx) -> Option<usize> {
        self.segs.iter().position(|&x| x == seg)
    }

    /// Returns an iterator of the allowable x positions for a slice of segments.
    fn horizontal_positions<'a, F: Float>(
        &'a self,
        y: &F,
        range: Range<usize>,
        segments: &'a Segments<F>,
        eps: &'a F,
    ) -> Vec<(SegIdx, F, F)> {
        let segs = &self.segs[range];
        let mut max_so_far = segs
            .first()
            .map(|seg| segments.get(*seg).lower(y, eps))
            // If `self.segs` is empty our y doesn't matter; we're going to return
            // an empty vec.
            .unwrap_or(F::from_f32(0.0));

        let mut ret: Vec<_> = segs
            .iter()
            .map(move |seg_idx| {
                let x = segments.get(*seg_idx).lower(y, eps);
                max_so_far = max_so_far.clone().max(x);
                // Fill out the minimum allowed positions, with a placeholder for the maximum.
                (*seg_idx, max_so_far.clone(), F::from_f32(0.0))
            })
            .collect();

        let mut min_so_far = segs
            .last()
            .map(|seg| segments.get(*seg).upper(y, eps))
            // If `self.segs` is empty our y doesn't matter; we're going to return
            // an empty vec.
            .unwrap_or(F::from_f32(0.0));
        for (seg_idx, _, max_allowed) in ret.iter_mut().rev() {
            let x = segments.get(*seg_idx).upper(y, eps);
            min_so_far = min_so_far.clone().min(x);
            *max_allowed = min_so_far.clone();
        }

        ret
    }

    fn range_order(&self, range: (usize, usize)) -> HashMap<SegIdx, usize> {
        self.segs[range.0..range.1]
            .iter()
            .enumerate()
            .map(|(idx, seg)| (*seg, idx))
            .collect()
    }
}

#[derive(Clone, Debug)]
pub struct SweepLine<'a, F: Float> {
    pub y: &'a F,
    pub old_line: &'a SegmentOrder,
    pub new_line: &'a SegmentOrder,

    pub segs_needing_positions: &'a HashSet<SegIdx>,
    pub exits: &'a HashSet<SegIdx>,
    pub entrances: &'a HashSet<SegIdx>,
}

impl<F: Float> Copy for SweepLine<'_, F> {}

impl<F: Float> SweepLine<'_, F> {
    /// We've marked various segments that need to be given an explicit
    /// horizontal position in the new sweep line, but in order to do that we
    /// may need to consider the positions of other nearby segments. In this
    /// method we explore nearby segments, turning our list of segments needing
    /// positions into a disjoint list of intervals needing positions.
    pub fn changed_intervals(&self, segments: &Segments<F>, eps: &F) -> Vec<(usize, usize)> {
        let mut changed: BTreeSet<_> = self.segs_needing_positions.iter().cloned().collect();
        let mut ret = Vec::new();
        let y = &self.y;

        // We compare horizontal positions to decide when to stop iterating. Those positions
        // are each accurate to eps / 8, so we compare them with slack eps / 4 to ensure no
        // false negatives.
        let slack = eps.clone() / F::from_f32(4.0);

        // Copy-pasted from `influence_range`
        while let Some(seg_idx) = changed.pop_first() {
            // unwrap: segs_needing_positions should all be in the line.
            let idx = self.new_line.position(seg_idx).unwrap();
            let mut start_idx = idx;
            let mut seg_min = segments.get(seg_idx).lower(y, eps);

            for i in (0..idx).rev() {
                let prev_seg_idx = self.new_line.segs[i];
                let prev_seg = segments.get(prev_seg_idx);
                if seg_min - prev_seg.upper(y, eps) > slack {
                    break;
                } else {
                    seg_min = prev_seg.lower(y, eps);
                    changed.remove(&prev_seg_idx);
                    start_idx = i;
                }
            }

            let mut end_idx = idx + 1;
            let mut seg_max = segments.get(seg_idx).upper(y, eps);
            for i in (idx + 1)..self.new_line.segs.len() {
                let next_seg_idx = self.new_line.segs[i];
                let next_seg = segments.get(next_seg_idx);
                if next_seg.lower(y, eps) - seg_max > slack {
                    break;
                } else {
                    seg_max = next_seg.upper(y, eps);
                    changed.remove(&next_seg_idx);
                    end_idx = i + 1;
                }
            }
            ret.push((start_idx, end_idx))
        }
        ret.sort();

        // By merging adjacent intervals, we ensure that there is no horizontal segment
        // that spans two ranges. That's because horizontal segments mark everything they
        // cross as needing a position. Any collection of subranges that are crossed by
        // a horizontal segment are therefore adjacent and will be merged here.
        merge_adjacent(ret)
    }

    pub fn range_orders(
        &self,
        range: (usize, usize),
    ) -> (HashMap<SegIdx, usize>, HashMap<SegIdx, usize>) {
        (
            self.old_line.range_order(range),
            self.new_line.range_order(range),
        )
    }

    pub fn position_range(
        &self,
        range: (usize, usize),
        segments: &Segments<F>,
        eps: &F,
    ) -> OutputEventBatcher<F> {
        let old_xs = self
            .old_line
            // TODO: decide whether to use (usize, usize) or std::ops::Range or something else
            .horizontal_positions(self.y, range.0..range.1, segments, eps);
        let new_xs = self
            .new_line
            .horizontal_positions(self.y, range.0..range.1, segments, eps);

        // The two positioning arrays should have the same segments, but possibly in a different
        // order. Group them by segment id.
        let mut seg_positions: HashMap<SegIdx, (F, Option<F>)> = HashMap::new();
        let mut max_so_far = old_xs
            .first()
            .map_or(F::from_f32(0.0), |(_idx, min_x, _max_x)| {
                min_x.clone() - F::from_f32(1.0)
            });
        for (idx, min_x, max_x) in old_xs {
            let preferred_x = if self.exits.contains(&idx) {
                // The best possible position is the true segment-ending position.
                // (This could change if we want to be more sophisticated at joining contours.)
                segments.get(idx).end.x.clone()
            } else if self.entrances.contains(&idx) {
                // The best possible position is the true segment-ending position.
                // (This could change if we want to be more sophisticated at joining contours.)
                segments.get(idx).start.x.clone()
            } else if max_so_far >= min_x {
                // The second best possible position is snapping to the neighbor that we
                // just positioned.
                max_so_far.clone()
            } else {
                segments.get(idx).at_y(self.y)
            };
            let x = preferred_x
                .max(min_x.clone())
                .max(max_so_far.clone())
                .min(max_x.clone());
            max_so_far = x.clone();
            seg_positions.insert(idx, (x, None));
        }

        let mut max_so_far = new_xs
            .first()
            .map_or(F::from_f32(0.0), |(_idx, min_x, _max_x)| {
                min_x.clone() - F::from_f32(1.0)
            });
        for (idx, min_x, max_x) in new_xs {
            let pos = seg_positions
                .get_mut(&idx)
                .expect("the two ranges should have the same segments");
            let preferred_x = if min_x <= pos.0 && pos.0 <= max_x {
                // Try snapping to the previous position if possible.
                pos.0.clone()
            } else if max_so_far >= min_x {
                // Try snapping to the neighbor we just positioned.
                max_so_far.clone()
            } else {
                segments.get(idx).at_y(self.y)
            };
            let x = preferred_x
                .max(min_x.clone())
                .max(max_so_far.clone())
                .min(max_x.clone());
            max_so_far = x.clone();
            pos.1 = Some(x);
        }

        let mut positions: Vec<OutputEvent<F>> = Vec::new();
        for (idx, (x0, x1)) in seg_positions {
            let Some(x1) = x1 else {
                panic!("the two ranges should have the same segments");
            };

            let entrance = self.entrances.contains(&idx);
            let exit = self.exits.contains(&idx);
            let seg = segments.get(idx);
            let kind = match (entrance, exit) {
                (true, true) => {
                    // A horizontal segment. We can ignore the inferred position, and
                    // go with the original bounds.
                    debug_assert!(seg.is_horizontal());
                    OutputEventKind::from_points(
                        seg.start.x.clone(),
                        false,
                        seg.end.x.clone(),
                        false,
                    )
                }
                (true, false) => {
                    // The segment enters at this sweep-line. The actual entrance position
                    // will be the segment's true start position, and then we will move
                    // to the adjusted position before leaving this sweep-line.
                    OutputEventKind::from_points(seg.start.x.clone(), false, x1, true)
                }
                (false, true) => {
                    // The segment terminates at this sweep-line. The actual final position
                    // will be the segment's true end position, but the segment will enter
                    // the sweep-line at the adjusted position.
                    OutputEventKind::from_points(x0, true, seg.end.x.clone(), false)
                }
                (false, false) => OutputEventKind::from_points(x0, true, x1, true),
            };

            positions.push(OutputEvent { kind, seg_idx: idx });
        }
        positions.sort();

        OutputEventBatcher {
            positions: positions.into_iter(),
            last_x: None,
            active_horizontals: BTreeSet::new(),
        }
    }
}

/// Given a sorted list of disjoint, endpoint-exclusive intervals, merge adjacent ones.
///
/// For example, [1..2, 4..5, 5..6] is turned into [1..2, 4..6].
fn merge_adjacent(intervals: impl IntoIterator<Item = (usize, usize)>) -> Vec<(usize, usize)> {
    let mut intervals = intervals.into_iter();
    let mut ret = Vec::new();
    let Some(mut last) = intervals.next() else {
        return ret;
    };
    for iv in intervals {
        if last.1 < iv.0 {
            ret.push(last);
            last = iv;
        } else {
            last.1 = iv.1;
        }
    }
    ret.push(last);
    ret
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct HSeg<F: Float> {
    pub end: F,
    pub connected_at_start: bool,
    pub connected_at_end: bool,
    pub enter_first: bool,
    pub seg: SegIdx,
    pub start: F,
}

impl<F: Float> HSeg<F> {
    pub fn from_position(pos: OutputEvent<F>) -> Option<Self> {
        let OutputEventKind::Horizontal {
            x0,
            connected_above,
            x1,
            connected_below,
        } = pos.kind
        else {
            return None;
        };

        let enter_first = x0 < x1;
        let (start, end, connected_at_start, connected_at_end) = if enter_first {
            (x0, x1, connected_above, connected_below)
        } else {
            (x1, x0, connected_below, connected_above)
        };
        Some(HSeg {
            end,
            start,
            enter_first,
            seg: pos.seg_idx,
            connected_at_start,
            connected_at_end,
        })
    }
    pub fn connected_above_at(&self, x: &F) -> bool {
        (*x == self.start && self.enter_first && self.connected_at_start)
            || (*x == self.end && !self.enter_first && self.connected_at_end)
    }

    pub fn connected_below_at(&self, x: &F) -> bool {
        (*x == self.start && !self.enter_first && self.connected_at_start)
            || (*x == self.end && self.enter_first && self.connected_at_end)
    }
}

/// The different ways in which a line segment can "interact" with a sweep-line.
///
/// In exact math, a non-horizontal line segment can interact with a sweep-line
/// in exactly one way: by intersecting it at a point. When dealing with inexact
/// math, intersections and re-orderings between line segments might force
/// our sweep-line algorithm to perturb the line segment. In that case, even
/// a non-horizontal line segment might enter and leave the sweep-line at two
/// different points.
///
/// `OutputEventKind` is ordered by the smallest horizontal coordinate where
/// it intersects the sweep-line (i.e. [`OutputEventKind::smaller_x`]).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum OutputEventKind<F: Float> {
    /// The line segment in question meets the sweep-line in exactly one point.
    ///
    /// That point might be the start or end of the line segment, or it could
    /// be an intermediate point.
    Point {
        /// The horizontal coordinate of the intersection.
        x: F,
        /// Does this line segment extend "above" (i.e. smaller `y`) this sweep-line?
        connected_above: bool,
        /// Does this line segment extend "below" (i.e. larger `y`) this sweep-line?
        connected_below: bool,
    },
    /// The line segment in question meets the sweep-line along a segment.
    ///
    /// The two points, `x0` and `x1`, are in sweep-line order. This doesn't
    /// necessarily mean that `x0` is smaller than `x1`! Instead, it means that
    /// when traversing the segment in sweep-line order (i.e. in increasing `y`,
    /// and increasing `x` if the segment is horizontal) then it visits `x0`
    /// before `x1`.
    Horizontal {
        /// The first horizontal coordinate on this sweep-line that we'd hit if
        /// we were traversing the segment in sweep-line orientation.
        x0: F,
        /// Does this line segment extend "above" (i.e. smaller `y`) this sweep-line?
        ///
        /// If so, it will extend up from `x0`, because that's what the "sweep-line order"
        /// means.
        connected_above: bool,
        /// The last horizontal coordinate on this sweep-line that we'd hit if
        /// we were traversing the segment in sweep-line orientation.
        x1: F,
        /// Does this line segment extend "below" (i.e. larger `y`) this sweep-line?
        ///
        /// If so, it will extend down from `x1`, because that's what the "sweep-line order"
        /// means.
        connected_below: bool,
    },
}

impl<F: Float> OutputEventKind<F> {
    /// The smallest `x` coordinate at which the line segment touches the sweep-line.
    pub fn smaller_x(&self) -> &F {
        match self {
            Self::Point { x, .. } => x,
            Self::Horizontal { x0, x1, .. } => x0.min(x1),
        }
    }

    /// The largest `x` coordinate at which the line segment touches the sweep-line.
    pub fn larger_x(&self) -> &F {
        match self {
            Self::Point { x, .. } => x,
            Self::Horizontal { x0, x1, .. } => x0.max(x1),
        }
    }

    fn from_points(x0: F, connected_above: bool, x1: F, connected_below: bool) -> Self {
        if x0 == x1 {
            OutputEventKind::Point {
                x: x0,
                connected_above,
                connected_below,
            }
        } else {
            // Honestly, is it worth having the two variants? Maybe just have one and
            // allow the points to be equal...
            OutputEventKind::Horizontal {
                x0,
                x1,
                connected_above,
                connected_below,
            }
        }
    }

    /// Does the line segment extend up from the horizontal coordinate `x`?
    pub fn connected_above_at(&self, x: &F) -> bool {
        match self {
            OutputEventKind::Point {
                x: x0,
                connected_above,
                ..
            }
            | OutputEventKind::Horizontal {
                x0,
                connected_above,
                ..
            } => x == x0 && *connected_above,
        }
    }

    /// Does the line segment extend down from the horizontal coordinate `x`?
    pub fn connected_below_at(&self, x: &F) -> bool {
        match self {
            OutputEventKind::Point {
                x: x1,
                connected_below,
                ..
            }
            | OutputEventKind::Horizontal {
                x1,
                connected_below,
                ..
            } => x == x1 && *connected_below,
        }
    }
}

impl<F: Float> Ord for OutputEventKind<F> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.smaller_x()
            .cmp(other.smaller_x())
            .then_with(|| self.larger_x().cmp(other.larger_x()))
    }
}

impl<F: Float> PartialOrd for OutputEventKind<F> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

/// An `OutputEvent` records the interaction between a line segment and a sweep-line.
///
/// See [`OutputEventKind`] for more details. `OutputEvent` is ordered primarily
/// by the smallest horizontal coordinate where it intersects the sweep-line
/// (i.e. [`OutputEventKind::smaller_x`]).
#[derive(Clone, Debug, PartialEq, PartialOrd, Eq, Ord)]
pub struct OutputEvent<F: Float> {
    /// The kind of interaction.
    pub kind: OutputEventKind<F>,
    /// The segment that's interacting with the sweep line.
    pub seg_idx: SegIdx,
}

#[derive(Clone, Debug)]
pub struct OutputEventBatcher<F: Float> {
    last_x: Option<F>,
    pub positions: std::vec::IntoIter<OutputEvent<F>>,
    pub active_horizontals: BTreeSet<HSeg<F>>,
}

impl<F: Float> OutputEventBatcher<F> {
    pub fn next_x(&self) -> Option<F> {
        match (
            self.active_horizontals.first(),
            self.positions.as_slice().first(),
        ) {
            (None, None) => None,
            (None, Some(pos)) => Some(pos.kind.smaller_x().clone()),
            (Some(h), None) => Some(h.end.clone()),
            (Some(h), Some(pos)) => Some(h.end.clone().min(pos.kind.smaller_x().clone())),
        }
    }

    pub fn positions_at_current_x(&self) -> Option<impl Iterator<Item = &OutputEvent<F>>> {
        let x = self.next_x()?;
        Some(
            self.positions
                .as_slice()
                .iter()
                .take_while(move |p| p.kind.smaller_x() == &x),
        )
    }

    // TODO: instead of collecting the output events, we could return something referencing self
    // that allows iteration
    pub fn next_events(&mut self) -> Option<Vec<OutputEvent<F>>> {
        let next_x = self.next_x()?;

        let mut ret = Vec::new();
        for h in &self.active_horizontals {
            // unwrap: on the first event of this sweep line, active_horizontals is empty. So
            // we only get here after last_x is populated.
            let x0 = self.last_x.clone().unwrap();
            let x1 = next_x.clone().min(h.end.clone());
            let connected_end = x1 == h.end && h.connected_at_end;
            let connected_start = x0 == h.start && h.connected_at_start;
            if h.enter_first {
                ret.push(OutputEvent {
                    seg_idx: h.seg,
                    kind: OutputEventKind::from_points(x0, connected_start, x1, connected_end),
                });
            } else {
                ret.push(OutputEvent {
                    seg_idx: h.seg,
                    kind: OutputEventKind::from_points(x1, connected_end, x0, connected_start),
                });
            }
        }

        // Drain the active horizontals, throwing away horizontal segments that end before
        // the new x position.
        while let Some(h) = self.active_horizontals.first() {
            if h.end <= next_x {
                self.active_horizontals.pop_first();
            } else {
                break;
            }
        }

        while let Some(pos) = self.positions.as_slice().first() {
            if pos.kind.smaller_x() > &next_x {
                break;
            }
            // unwrap: we just peeked at this element.
            let pos = self.positions.next().unwrap();

            if matches!(&pos.kind, OutputEventKind::Point { .. }) {
                // We push output event for points immediately.
                ret.push(pos);
            } else if let Some(hseg) = HSeg::from_position(pos) {
                // For horizontal segments, we don't output anything straight
                // away. When we update the horizontal position and visit our
                // horizontal segments, we'll output something.
                self.active_horizontals.insert(hseg);
            }
        }
        self.last_x = Some(next_x);
        Some(ret)
    }

    pub fn drain_active_horizontals(&mut self, x: &F) {
        while let Some(h) = self.active_horizontals.first() {
            if h.end <= *x {
                self.active_horizontals.pop_first();
            } else {
                break;
            }
        }
    }
}

/// Runs the sweep-line algorithm, calling the provided callback on every output point.
pub fn sweep<F: Float, C: FnMut(F, OutputEvent<F>)>(
    segments: &Segments<F>,
    eps: &F,
    mut callback: C,
) {
    let mut state = State::new(segments, eps.clone());
    while let Some(line) = state.next_line() {
        for (start, end) in line.changed_intervals(segments, eps) {
            let mut positions = line.position_range((start, end), segments, eps);
            while let Some(events) = positions.next_events() {
                for ev in events {
                    callback(line.y.clone(), ev);
                }
            }
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
        segments::Segments,
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
    fn merge_adjacent() {
        assert_eq!(
            super::merge_adjacent([(1, 2), (3, 4)]),
            vec![(1, 2), (3, 4)]
        );

        assert_eq!(super::merge_adjacent([(1, 2), (2, 4)]), vec![(1, 4)]);

        assert_eq!(
            super::merge_adjacent([(1, 2), (3, 4), (4, 5)]),
            vec![(1, 2), (3, 5)]
        );
    }

    #[test]
    fn invalid_order() {
        fn check_order(xs: &[(f64, f64)], at: f64, eps: f64) -> Option<(usize, usize)> {
            let eps: NotNan<f64> = eps.try_into().unwrap();
            let y: NotNan<f64> = at.try_into().unwrap();
            let segs = mk_segs(xs);

            let line: SegmentOrder = (0..xs.len()).map(SegIdx).collect();

            line.find_invalid_order(&y, &segs, &eps)
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

            let line: SegmentOrder = (0..xs.len()).map(SegIdx).collect();
            line.insertion_idx(&y, &segs, &new, &eps)
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
        sweep(&segs, &eps, |_, ev| {
            dbg!(ev);
        });
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
        sweep(&segs, &eps, |_, _| {});
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
