use std::{
    cmp::{Ordering, Reverse},
    collections::{BinaryHeap, HashMap, HashSet},
};

use malachite::Rational;
use ordered_float::NotNan;

pub type Float = NotNan<f64>;

pub mod equivalence;
pub mod exact;
pub mod types;

pub use types::{Crosses, Interaction, Point, Segment, Vector};

#[derive(Debug, Clone, Copy, PartialOrd, Ord, PartialEq, Eq, Hash)]
pub struct SegRef(usize);

#[derive(Clone, Copy, PartialOrd, Ord, PartialEq, Eq)]
pub struct SweepEvent {
    y: Float,
    payload: SweepEventPayload,
}

#[derive(Debug)]
pub struct Intersection {
    pub y: Float,
    pub i: SegRef,
    pub j: SegRef,
}

// "clockwise" if we're doing the positive-y = up convention
fn clockwise(p0: Point, p1: Point, p2: Point) -> bool {
    let v1 = p1 - p0;
    let v2 = p2 - p0;

    v1.x * v2.y - v1.y * v2.x < NotNan::try_from(0.0).unwrap()
}

impl SweepEvent {
    fn intersection(left: SegRef, right: SegRef, y: Float) -> SweepEvent {
        SweepEvent {
            y,
            payload: SweepEventPayload::Intersection { left, right },
        }
    }

    fn from_adjacent_segments(i0: SegRef, i1: SegRef, arena: &SegmentArena) -> SweepEvent {
        let (s0, orient0) = (arena.get(i0), arena.in_order(i0));
        let (s1, orient1) = (arena.get(i1), arena.in_order(i1));
        use SweepEventPayload::*;
        let (y, payload) = match (orient0, orient1) {
            (true, true) => (
                s0.end.y,
                ExitEnter {
                    exit: i0,
                    enter: i1,
                },
            ),
            (true, false) => {
                assert_eq!(s0.end, s1.end);
                let (left, right) = if clockwise(s0.start, s0.end, s1.start) {
                    // The name "clockwise" assumes positive-y is up. The two segments
                    // meet at the upper point, so clockwise means that the second segment
                    // is the the right.
                    (i0, i1)
                } else {
                    (i1, i0)
                };
                (s0.end.y, ExitExit { left, right })
            }
            (false, true) => {
                assert_eq!(s0.start, s1.start);
                let (left, right) = if clockwise(s0.start, s0.end, s1.end) {
                    (i0, i1)
                } else {
                    (i1, i0)
                };
                (s0.start.y, EnterEnter { left, right })
            }
            (false, false) => (
                s1.end.y,
                ExitEnter {
                    exit: i1,
                    enter: i0,
                },
            ),
        };
        SweepEvent { y, payload }
    }
}

impl std::fmt::Debug for SweepEvent {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?} -> {:?}", self.y.into_inner(), self.payload)
    }
}

#[derive(Clone, Copy, PartialOrd, Ord, PartialEq, Eq)]
pub enum SweepEventPayload {
    Intersection { left: SegRef, right: SegRef },
    EnterEnter { left: SegRef, right: SegRef },
    ExitEnter { exit: SegRef, enter: SegRef },
    ExitExit { left: SegRef, right: SegRef },
}

impl std::fmt::Debug for SweepEventPayload {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SweepEventPayload::Intersection { left, right, .. } => {
                write!(f, "left({left:?}) x right({right:?})")
            }
            SweepEventPayload::EnterEnter { left, right } => {
                write!(f, "enter({left:?}), enter({right:?})")
            }
            SweepEventPayload::ExitExit { left, right } => {
                write!(f, "exit({left:?}), exit({right:?})")
            }
            SweepEventPayload::ExitEnter { exit, enter } => {
                write!(f, "exit({exit:?}), enter({enter:?})")
            }
        }
    }
}

#[derive(Clone)]
pub struct SweepLine {
    pub y: Float,
    pub segments: Vec<SegRef>,
}

impl Default for SweepLine {
    fn default() -> Self {
        SweepLine {
            y: std::f64::NEG_INFINITY.try_into().unwrap(),
            segments: Vec::new(),
        }
    }
}

impl std::fmt::Debug for SweepLine {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let segs = self.segments.iter().map(|SegRef(i)| i).collect::<Vec<_>>();
        write!(f, "{} -> {:?}", self.y.into_inner(), segs)
    }
}

#[derive(Clone, Debug)]
pub enum InvariantViolation {
    SegmentDomain {
        seg: Segment,
        y: Float,
    },
    SegmentOrder {
        before: Segment,
        after: Segment,
        y: Float,
    },
    MissingEvent {
        left: Segment,
        right: Segment,
    },
}

#[derive(Default)]
pub struct EventQueue {
    inner: BinaryHeap<Reverse<SweepEvent>>,
}

impl EventQueue {
    pub fn extend(&mut self, iter: impl IntoIterator<Item = SweepEvent>) {
        self.inner.extend(iter.into_iter().map(Reverse));
    }

    pub fn push(&mut self, x: SweepEvent) {
        self.inner.push(Reverse(x));
    }

    pub fn is_empty(&self) -> bool {
        self.inner.is_empty()
    }

    pub fn pop(&mut self) -> Option<SweepEvent> {
        self.inner.pop().map(|Reverse(x)| x)
    }

    pub fn peek(&self) -> Option<&SweepEvent> {
        self.inner.peek().map(|Reverse(x)| x)
    }
}

impl std::fmt::Debug for EventQueue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_list()
            .entries(self.inner.iter().map(|Reverse(x)| x))
            .finish()
    }
}

pub struct SweepContext<'a> {
    pub eps: Float,
    pub segments: &'a SegmentArena,
    pub queue: &'a mut EventQueue,
    pub intersections: &'a mut Vec<Intersection>,
}

impl<'a> SweepContext<'a> {
    fn emit_intersection(&mut self, y: Float, i: SegRef, j: SegRef) {
        self.intersections.push(Intersection { y, i, j });
    }
}

impl SweepLine {
    pub fn check_invariants(
        &self,
        eps: Float,
        arena: &SegmentArena,
        queue: &EventQueue,
    ) -> Result<(), InvariantViolation> {
        let y = Rational::try_from(self.y.into_inner()).unwrap();
        let eps = Rational::try_from(eps.into_inner()).unwrap();
        for i in 0..self.segments.len() {
            let seg_i_approx = arena.get(self.segments[i]);
            let seg_i = exact::Segment::from(seg_i_approx);
            if !(&seg_i.start.y..=&seg_i.end.y).contains(&&y) {
                return Err(InvariantViolation::SegmentDomain {
                    seg: seg_i_approx,
                    y: self.y,
                });
            }

            for j in (i + 1)..self.segments.len() {
                let seg_j_approx = arena.get(self.segments[j]);
                let seg_j = exact::Segment::from(seg_j_approx);

                if seg_i.at_y(&y) > seg_j.at_y(&y) + &eps {
                    return Err(InvariantViolation::SegmentOrder {
                        before: seg_i_approx,
                        after: seg_j_approx,
                        y: self.y,
                    });
                }

                if let Some(y_int) = seg_j.intersection_y(&seg_j) {
                    // The segments between i and j. There has to be some event that involves them.
                    let between_segs: HashSet<_> = (i..=j).map(|k| self.segments[k]).collect();
                    let good_ev = |Reverse(ev): &Reverse<SweepEvent>| {
                        let (a, b) = match ev.payload {
                            SweepEventPayload::Intersection { left, right } => (left, right),
                            SweepEventPayload::EnterEnter { left, right } => (left, right),
                            SweepEventPayload::ExitEnter { exit, enter } => (exit, enter),
                            SweepEventPayload::ExitExit { left, right } => (left, right),
                        };
                        ev.y.into_inner() <= y_int
                            && (between_segs.contains(&a) || between_segs.contains(&b))
                    };
                    if y_int > y && !queue.inner.iter().any(good_ev) {
                        return Err(InvariantViolation::MissingEvent {
                            left: seg_i_approx,
                            right: seg_j_approx,
                        });
                    }
                }
            }
        }

        Ok(())
    }

    /// Find a valid insertion index for a segment at position x.
    fn search_x(&self, x: Float, arena: &SegmentArena) -> usize {
        // Custom binary search. (The std version assumes a strict order, which we don't have.)

        let mut low = 0;
        let mut high = self.segments.len();

        while high > low {
            let mid = (low + high) / 2;
            let mid_seg = arena.get(self.segments[mid]);
            match mid_seg.at_y(self.y).cmp(&x) {
                Ordering::Less => low = mid + 1,
                Ordering::Equal => return mid,
                Ordering::Greater => high = mid,
            }
        }

        high
    }

    fn find_seg_ref(&self, seg: SegRef) -> usize {
        self.maybe_find_seg_ref(seg).expect("missing seg ref")
    }

    fn maybe_find_seg_ref(&self, seg: SegRef) -> Option<usize> {
        // TODO: should be able to do this in logarithmic time
        self.segments.iter().position(|s| s == &seg)
    }

    fn scan_left(&mut self, ctx: &mut SweepContext, mut idx: usize, allow_swap: bool) -> usize {
        let scanning_seg = ctx.segments.get(self.segments[idx]);

        for j in (0..idx).rev() {
            let seg = ctx.segments.get(self.segments[j]);
            // TODO: this also counts crossings of segments that are adjacent in
            // the contour. It's harmless, but we can filter them out
            let (crosses, interaction) = scanning_seg.compare_to_the_left(&seg, self.y, ctx.eps);
            match crosses {
                Crosses::At { y } => ctx.queue.push(SweepEvent::intersection(
                    self.segments[j],
                    self.segments[idx],
                    y,
                )),
                Crosses::Now if allow_swap => {
                    // Take the segment that crosses us now and move it to our right, crossing everything in between.
                    for k in (j + 1)..=idx {
                        ctx.emit_intersection(self.y, self.segments[j], self.segments[k]);
                    }
                    // TODO: does it matter which way we rotate? Everything in between is supposed to be eps-close anyway...
                    self.segments[j..=idx].rotate_left(1);
                    idx -= 1;
                }
                Crosses::Now | Crosses::Never => {}
            }
            if matches!(interaction, Interaction::Blocks) {
                break;
            }
        }
        idx
    }

    fn scan_right(&mut self, ctx: &mut SweepContext, mut idx: usize, allow_swap: bool) -> usize {
        let scanning_seg = ctx.segments.get(self.segments[idx]);

        for j in (idx + 1)..self.segments.len() {
            let seg = ctx.segments.get(self.segments[j]);
            // TODO: this also counts crossings of segments that are adjacent in
            // the contour. It's harmless, but we can filter them out
            let (crosses, interaction) = scanning_seg.compare_to_the_right(&seg, self.y, ctx.eps);
            match crosses {
                Crosses::At { y } => ctx.queue.push(SweepEvent::intersection(
                    self.segments[idx],
                    self.segments[j],
                    y,
                )),
                Crosses::Now if allow_swap => {
                    for k in idx..j {
                        ctx.emit_intersection(self.y, self.segments[k], self.segments[j]);
                    }
                    self.segments[idx..=j].rotate_right(1);
                    idx -= 1;
                }
                Crosses::Now | Crosses::Never => {}
            }
            if matches!(interaction, Interaction::Blocks) {
                break;
            }
        }
        idx
    }

    fn scan_both(&mut self, ctx: &mut SweepContext, idx: usize) {
        let idx = self.scan_right(ctx, idx, true);
        self.scan_left(ctx, idx, true);
    }

    pub fn process_event(&mut self, ctx: &mut SweepContext, event: SweepEvent) {
        dbg!(&event);
        self.y = event.y;
        match event.payload {
            SweepEventPayload::EnterEnter { left, right } => {
                ctx.emit_intersection(self.y, left, right);
                let left_seg = ctx.segments.get(left);
                let right_seg = ctx.segments.get(right);

                assert_eq!(left_seg.start, right_seg.start);
                let start = left_seg.start;

                let idx = self.search_x(start.x, ctx.segments);
                self.segments.insert(idx, right);
                self.segments.insert(idx, left);
                dbg!(idx, &self.segments);

                self.scan_left(ctx, idx, true);
                dbg!(&self.segments);
                self.scan_right(ctx, idx + 1, true);
                dbg!(&self.segments);
            }
            SweepEventPayload::ExitEnter { exit, enter } => {
                ctx.emit_intersection(self.y, exit, enter);
                let idx = self.find_seg_ref(exit);
                self.segments[idx] = enter;

                self.scan_both(ctx, idx);
            }
            SweepEventPayload::ExitExit { left, right } => {
                ctx.emit_intersection(self.y, left, right);
                let left_idx = self.find_seg_ref(left);
                let right_idx = self.find_seg_ref(right);

                // If these last segments are almost parallel, it's probably possible for them to be in the "wrong" order.
                let (left_idx, mut right_idx) = (left_idx.min(right_idx), left_idx.max(right_idx));
                self.segments.remove(left_idx);
                right_idx -= 1;
                self.segments.remove(right_idx);
                if let Some(left_left) = left_idx.checked_sub(1) {
                    self.scan_left(ctx, left_left, false);
                }
                if right_idx < self.segments.len() {
                    self.scan_right(ctx, right_idx, false);
                }
            }
            SweepEventPayload::Intersection { left, right, .. } => {
                let left_idx = self.find_seg_ref(left);
                let right_idx = self.find_seg_ref(right);

                // I don't expect this test to fail, but I'm not sure it's actually impossible.
                if left_idx < right_idx {
                    for j in left_idx..right_idx {
                        ctx.emit_intersection(self.y, self.segments[j], right);
                    }
                    for j in (left_idx + 1)..right_idx {
                        ctx.emit_intersection(self.y, left, self.segments[j]);
                    }
                    self.segments.swap(left_idx, right_idx);
                    let (left_idx, right_idx) = (right_idx, left_idx);
                    self.scan_both(ctx, left_idx);

                    // It should be impossible for the two just-intersected segments to swap.
                    assert_eq!(right_idx, self.find_seg_ref(right));
                    self.scan_both(ctx, right_idx);
                }
            }
        }
    }

    // FIXME: this approach of using equivalence classes of intersections is ok topologically
    // but not geometrically: it might end up moving segments more than epsilon horizontally.
    // In order to fix this, I think we might need to allow extra horizontal pieces.
    pub fn realize_intersections(
        &self,
        intersections: &[Intersection],
        arena: &SegmentArena,
    ) -> Vec<GroupedIntersection> {
        assert!(intersections.iter().all(|int| int.y == self.y));

        // All segments that intersect at this scan line get divided into equivalence classes,
        // so that we can declare a common intersection point for each class.
        let mut equiv = equivalence::Equiv::default();
        let mut horizontals = Vec::new();
        let mut grouped = Vec::new();
        for int in intersections {
            let i_horiz = arena.get(int.i).is_exactly_horizontal();
            let j_horiz = arena.get(int.j).is_exactly_horizontal();

            // Don't mark horizontal segments as being equivalent to the thing
            // they intersect, or we will end up marking too many things as
            // equivalent. We'll handle the horizontal intersections later.
            // FIXME: If one path has two horizontal segments in a row, we'll miss
            // their intersection point. We should handle that in an additional
            // preprocessing step, where we merge those adjacent horizontal segments.
            match (i_horiz, j_horiz) {
                (true, true) => {
                    horizontals.push(int.i);
                    horizontals.push(int.j);
                }
                (true, false) => {
                    horizontals.push(int.i);
                    equiv.add_singleton(int.j);
                }
                (false, true) => {
                    horizontals.push(int.j);
                    equiv.add_singleton(int.i);
                }
                (false, false) => {
                    equiv.add_equivalence(int.i, int.j);
                }
            }
        }

        // Assign an initial point to each intersection group. They might not have the right order.
        for set in equiv.equivalences() {
            grouped.push(GroupedIntersection {
                segments: set.clone(),
                p: Point {
                    x: (mid_range(set.iter().map(|seg| arena.get(*seg).at_y(self.y)))),
                    y: self.y,
                },
            })
        }

        // Note that not every segment in our intersections is still in the sweep line; there
        // might be a segment that just exited.
        //
        // Ignoring the horizontal segments, the intersection groups should be strictly ordered
        // by our sweep line order, in that if any member of group 1 comes before any member of group 2,
        // then all members of group 1 come before all members of group 2. The intersection groups can
        // also be ordered by x coordinate. However, there is no guarantee that the ordering by sweep line
        // agrees with the ordering by x coordinate. Here, we force that to be the case by modifying the
        // x coordinates if necessary.
        grouped.sort_by(|g, h| {
            // Find the sweep-line position of *some* segment from the group. It shouldn't matter which.
            // The group might not have any segment in the sweep line (e.g. if it's from an exit-exit intersection).
            let g_idx = g
                .segments
                .iter()
                .find_map(|seg| self.maybe_find_seg_ref(*seg));
            let h_idx = h
                .segments
                .iter()
                .find_map(|seg| self.maybe_find_seg_ref(*seg));
            if let (Some(g_idx), Some(h_idx)) = (g_idx, h_idx) {
                g_idx.cmp(&h_idx)
            } else {
                g.p.x.cmp(&h.p.x)
            }
        });

        let mut running_max = Float::new(f64::NEG_INFINITY).unwrap();
        let mut grouped_and_ordered = Vec::new();
        for g in grouped {
            if g.p.x > running_max {
                running_max = g.p.x;
                grouped_and_ordered.push(g);
            } else {
                // We could assert here that g.p.x is at least running_max - eps, but we don't know eps here...
                //
                // running_max starts at negative infinity, and all coordinates are finite.
                // So if we get here then grouped_and_ordered is non-empty.
                grouped_and_ordered
                    .last_mut()
                    .unwrap()
                    .segments
                    .extend(g.segments);
            }
        }
        grouped = grouped_and_ordered;

        for seg_ref in horizontals {
            let seg = arena.get(seg_ref);
            // TODO: could use a binary search here
            let interval = seg.start.x..=seg.end.x;
            for group in &mut grouped {
                if interval.contains(&group.p.x) {
                    group.segments.insert(seg_ref);
                }
            }
        }

        grouped
    }

    /// Finds the first (non-horizontal) segment before an intersection.
    ///
    /// Returns None if this intersection has no non-horizontal segments on this scan line.
    fn segment_before_grouped_intersection(
        &self,
        int: &GroupedIntersection,
        segments: &SegmentArena,
    ) -> Option<SegRef> {
        // FIXME: what if the group only contains horizontal segments?
        // unwrap: grouped intersections should always be non-empty.
        let idx = int
            .segments
            .iter()
            .filter(|seg| !segments.get(**seg).is_exactly_horizontal())
            .find_map(|seg| self.maybe_find_seg_ref(*seg))?;

        (0..idx)
            .rev()
            .map(|i| self.segments[i])
            .find(|seg| !int.segments.contains(seg) && !segments.get(*seg).is_exactly_horizontal())
    }
}

// All the vecs here have the same length and same indexing.
#[derive(Debug, Default)]
pub struct SegmentArena {
    pub all_segments: Vec<Segment>,
    in_order: Vec<bool>,
    contour_next: Vec<SegRef>,
    contour_prev: Vec<SegRef>,
    // (maybe this should go elsewhere? everything else in SegmentArena is constructed
    // before sweeping the line...)
    subdivision: Vec<Vec<Point>>,
    // This is a bit confusing right now. For each endpoint e, let f be the next endpoint
    // in the subdivision list (i.e. the adjacent endpoint whose point is lexicographically
    // larger than e). We take that segment and look at it in its original orientation. We
    // take the winding number to the right of the oriented segment, and we store it in the
    // index corresponding to e.
    winding: Vec<Vec<i32>>,
}

impl SegmentArena {
    pub fn get(&self, seg_ref: SegRef) -> Segment {
        self.all_segments[seg_ref.0]
    }

    pub fn in_order(&self, seg_ref: SegRef) -> bool {
        self.in_order[seg_ref.0]
    }

    pub fn insert(&mut self, p0: Point, p1: Point) -> SegRef {
        if p0 < p1 {
            self.all_segments.push(Segment { start: p0, end: p1 });
            self.in_order.push(true);
        } else {
            assert!(p1 < p0);
            self.all_segments.push(Segment { start: p1, end: p0 });
            self.in_order.push(false);
        }
        let seg = SegRef(self.all_segments.len() - 1);
        self.contour_next.push(seg);
        self.contour_prev.push(seg);
        self.subdivision.push(Vec::new());
        self.winding.push(Vec::new());
        seg
    }

    /// Mark s1 as following s0 in a contour.
    pub fn add_contour_link(&mut self, s0: SegRef, s1: SegRef) {
        self.contour_next[s0.0] = s1;
        self.contour_prev[s1.0] = s0;
    }

    pub fn add_segment_point(&mut self, s: SegRef, p: Point) {
        self.subdivision[s.0].push(p);
    }

    /// As long as the intersections are sorted (y increasing and then x
    /// increasing), the subdivisions of each segment will also be sorted.
    pub fn add_subdivisions(&mut self, intersections: &[GroupedIntersection]) {
        for int in intersections {
            for seg in &int.segments {
                self.subdivision[seg.0].push(int.p);
            }
        }
    }

    pub fn subdivisions(&self, s: SegRef) -> &[Point] {
        &self.subdivision[s.0]
    }

    pub fn subdivision_endpoint(&self, e: EndpointRef) -> Point {
        self.subdivisions(e.seg)[e.subdivision_idx]
    }

    pub fn subdivision_winding(&self, e: EndpointRef) -> i32 {
        self.windings(e.seg)[e.subdivision_idx]
    }

    pub fn windings(&self, s: SegRef) -> &[i32] {
        &self.winding[s.0]
    }

    pub fn add_winding(&mut self, s: SegRef, w: i32) {
        self.winding[s.0].push(w);
    }

    pub fn extend_windings(
        &mut self,
        intersections: &[GroupedIntersection],
        ordered: &[OrderedIntersection],
        prev_sweep: &SweepLine,
        sweep: &SweepLine,
    ) {
        // The winding number of the region to the right (and slightly above) the previous intersection.
        let mut prev_right_winding: Option<i32> = None;
        for (int, ordered) in intersections.iter().zip(ordered) {
            dbg!(ordered);
            let left_winding = if let Some(prev_seg) =
                sweep.segment_before_grouped_intersection(int, self)
            {
                let order_offset = if self.in_order(prev_seg) { 0 } else { -1 };
                // We're computing winding numbers in order, so the previous one should have been computed.
                dbg!(self.windings(dbg!(prev_seg)).last().unwrap() + order_offset)
            } else if let Some(prev_winding) = prev_right_winding {
                // This intersection has nothing pointing up, so
                // its winding number is the same as the right winding of the
                // preceding intersection. There can't be a segment between
                // this intersection and the preceding one, because that segment
                // would intersect with the horizontal segment leading left from
                // this intersection.
                dbg!(prev_winding)
            } else if let Some(prev_seg) = prev_sweep.segment_before_grouped_intersection(int, self)
            {
                let order_offset = if self.in_order(prev_seg) { 0 } else { -1 };
                // There's no intersection before us (which implies that we
                // don't have a horizontal segment pointing left) and we have
                // something coming from below. Our winding number comes from
                // the previous segment in the previous sweep-line.
                // It's the last subdivision of that segment, because if there were
                // a newer subdivision, we would have had a prior intersection.
                dbg!(self.windings(prev_seg).last().unwrap() + order_offset)
            } else {
                // We must be left-most.
                dbg!(0)
            };

            for (e, local) in ordered.endpoints.iter().zip(&ordered.winding) {
                let subs = self.subdivisions(e.seg);
                let increasing =
                    e.subdivision_idx >= subs.len() || subs[e.subdivision_idx] > ordered.p;
                let outwards = increasing == self.in_order(e.seg);

                // We only add windings numbers for increasing segments (so we only add each one once).
                // left_winding + local is the winding number of the region just counter-clockwise of this
                // segment. If we're oriented inwards, that's the region to the right of the segment.
                if increasing {
                    let w = if outwards {
                        left_winding + *local + 1
                    } else {
                        left_winding + *local
                    };
                    self.add_winding(e.seg, w);
                }
            }

            prev_right_winding = Some(left_winding + ordered.right_winding(self));
        }
    }

    /// This can only be called after creating all the subdivisions.
    /// (TODO: better API)
    pub fn path_iter(&self, seg: SegRef) -> PathIter<'_> {
        PathIter::new(self, seg)
    }

    /// This can only be called after creating all the subdivisions.
    /// (TODO: better API)
    pub fn walk_winding(&self, ordered: &[OrderedIntersection], winding: i32) -> Vec<Vec<Point>> {
        let mut walker = Walker::new(self, ordered, winding);
        let mut ret = Vec::new();
        while let Some(contour) = walker.walk_next_contour() {
            ret.push(contour);
        }
        ret
    }
}

pub struct PathIter<'a> {
    arena: &'a SegmentArena,
    start_seg: SegRef,
    seg: SegRef,
    points: std::slice::Iter<'a, Point>,
}

impl<'a> PathIter<'a> {
    pub fn new(arena: &'a SegmentArena, seg: SegRef) -> Self {
        PathIter {
            arena,
            start_seg: seg,
            seg,
            points: arena.subdivision[seg.0].iter(),
        }
    }

    fn next_on_current_seg(&mut self) -> Option<Point> {
        if self.arena.in_order[self.seg.0] {
            self.points.next().copied()
        } else {
            self.points.next_back().copied()
        }
    }
}

impl<'a> Iterator for PathIter<'a> {
    type Item = Point;
    fn next(&mut self) -> Option<Point> {
        match self.next_on_current_seg() {
            Some(p) => Some(p),
            None => {
                self.seg = self.arena.contour_next[self.seg.0];
                if self.seg == self.start_seg {
                    return None;
                }
                self.points = self.arena.subdivision[self.seg.0].iter();

                // Discard the first point on this segment because it was also
                // the last point on the previous one.
                self.next_on_current_seg();
                self.next_on_current_seg()
            }
        }
    }
}

fn cyclic_pairs<T>(xs: &[T]) -> impl Iterator<Item = (&T, &T)> {
    xs.windows(2)
        .map(|pair| (&pair[0], &pair[1]))
        .chain(xs.last().zip(xs.first()))
}

#[derive(Debug)]
pub struct Sweeper {
    pub sweep_line: SweepLine,
    pub queue: EventQueue,
    pub segments: SegmentArena,
    pub intersections: Vec<Intersection>,
    pub ordered_intersections: Vec<OrderedIntersection>,
    pub eps: Float,
}

impl Sweeper {
    pub fn new(eps: Float) -> Self {
        Sweeper {
            sweep_line: SweepLine::default(),
            queue: EventQueue::default(),
            segments: SegmentArena::default(),
            intersections: Vec::new(),
            ordered_intersections: Vec::new(),
            eps,
        }
    }

    pub fn step(&mut self) {
        if let Some(event) = self.queue.pop() {
            let mut ctx = SweepContext {
                eps: self.eps,
                segments: &self.segments,
                queue: &mut self.queue,
                intersections: &mut self.intersections,
            };
            self.sweep_line.process_event(&mut ctx, event);
        }
    }

    pub fn run(&mut self) {
        dbg!(&self);
        while !self.queue.is_empty() {
            let last_sweep = self.sweep_line.clone();
            let intersections = self.run_one_y();
            self.segments.add_subdivisions(&intersections);
            let ordered_intersections: Vec<_> = intersections
                .iter()
                .map(|int| int.sort(&last_sweep, &self.sweep_line, &self.segments))
                .collect();
            dbg!(&ordered_intersections);
            self.segments.extend_windings(
                &intersections,
                &ordered_intersections,
                &last_sweep,
                &self.sweep_line,
            );
            self.ordered_intersections.extend(ordered_intersections);
            //dbg!(&self.sweep_line, &self.queue, &intersections);
            dbg!(&self.sweep_line);
            self.sweep_line
                .check_invariants(self.eps, &self.segments, &self.queue)
                .unwrap();
        }
        // Every segment should have at least a start and an endpoint.
        assert!(self.segments.subdivision.iter().all(|s| s.len() >= 2));
        //dbg!(&self.intersections);
        dbg!(&self.segments);
    }

    pub fn run_one_y(&mut self) -> Vec<GroupedIntersection> {
        let intersection_len = self.intersections.len();
        self.step();
        let y = self.sweep_line.y;
        while let Some(ev) = self.queue.peek() {
            if ev.y > y {
                break;
            }
            self.step();
        }

        self.sweep_line
            .realize_intersections(&self.intersections[intersection_len..], &self.segments)
    }

    pub fn add_closed_polyline(&mut self, points: &[Point]) {
        assert!(points.len() >= 2);

        let mut new_segs = Vec::new();
        for (p0, p1) in cyclic_pairs(points) {
            new_segs.push(self.segments.insert(*p0, *p1));
        }

        for (&i, &j) in cyclic_pairs(&new_segs) {
            self.segments.add_contour_link(i, j);
            self.queue
                .push(SweepEvent::from_adjacent_segments(i, j, &self.segments));
        }
    }
}

/// Eliminates almost horizontal segments by replacing them with an exactly horizontal
/// segment followed by a vertical segment.
pub fn preprocess_horizontal_segments(points: &[Point]) -> Vec<Point> {
    let mut ret = Vec::new();

    for (p0, p1) in cyclic_pairs(points) {
        let (seg, _) = Segment::from_unordered_points(*p0, *p1);
        ret.push(*p0);
        if seg.is_almost_horizontal() && !seg.is_exactly_horizontal() {
            ret.push(Point { x: p1.x, y: p0.y });
        }
    }
    ret
}

#[derive(Debug)]
pub struct GroupedIntersection {
    pub p: Point,
    pub segments: HashSet<SegRef>,
}

impl GroupedIntersection {
    fn winding_increment(
        &self,
        seg: SegRef,
        subdivision_idx: usize,
        segments: &SegmentArena,
    ) -> i32 {
        let subs = segments.subdivisions(seg);
        // Is the endpoint of this segment "larger" than self.p?
        // For segments going from the current sweep line to the next, subdivision_idx can
        // point past the end.
        let increasing = subdivision_idx >= subs.len() || subs[subdivision_idx] > self.p;

        if increasing == segments.in_order(seg) {
            1
        } else {
            -1
        }
    }

    // Assumes we have just added next_sweep's subdivisions to the segment arena.
    pub fn sort(
        &self,
        prev_sweep: &SweepLine,
        next_sweep: &SweepLine,
        segments: &SegmentArena,
    ) -> OrderedIntersection {
        let mut endpoints = Vec::new();

        let horiz_segments: Vec<_> = self
            .segments
            .iter()
            // TODO: if we allow for horizontal subdivisions in a non-horizontal segment,
            // we'll need to test for horizontalness at the subdivision level
            .filter(|seg| segments.get(**seg).is_exactly_horizontal())
            .filter_map(|seg| {
                next_sweep.maybe_find_seg_ref(*seg)?;
                let sub_idx = segments
                    .subdivisions(*seg)
                    .binary_search_by_key(&self.p.x, |q| q.x)
                    .unwrap();
                Some((*seg, sub_idx, segments.subdivisions(*seg).len()))
            })
            .collect();

        // Add segments from the next sweep line, from left to right (because they're above us).
        let mut next_segments: Vec<_> = self
            .segments
            .iter()
            .filter_map(|seg| {
                if segments.get(*seg).is_exactly_horizontal() {
                    None
                } else {
                    next_sweep.maybe_find_seg_ref(*seg).map(|idx| (idx, seg))
                }
            })
            .collect();
        next_segments.sort();
        endpoints.extend(next_segments.into_iter().map(|(_, &seg)| {
            assert_eq!(&self.p, segments.subdivisions(seg).last().unwrap());
            EndpointRef {
                seg,
                // Because we've just added next_sweep's subdivisions to the segment arena,
                // the last subdivision of this segment should be self.p; we want the next subdivision
                // (which hasn't been added yet, because this segment extends past the current sweep-line).
                subdivision_idx: segments.subdivisions(seg).len(),
            }
        }));

        // Add right-pointing horizontal segments from the current sweep line.
        endpoints.extend(
            horiz_segments
                .iter()
                .filter(|&&(_seg, sub_idx, sub_idx_count)| {
                    // As long as we aren't at the last subdivision point, there's a segment to the right.
                    sub_idx + 1 < sub_idx_count
                })
                .map(|&(seg, sub_idx, _sub_idx_count)| EndpointRef {
                    seg,
                    subdivision_idx: sub_idx + 1,
                }),
        );

        let mut prev_segments: Vec<_> = self
            .segments
            .iter()
            .filter_map(|seg| prev_sweep.maybe_find_seg_ref(*seg).map(|idx| (idx, seg)))
            .collect();
        prev_segments.sort();

        // Add segments from the previous sweep line, from right to left (because they're below us).
        endpoints.extend(prev_segments.into_iter().rev().map(|(_, &seg)| {
            assert_eq!(&self.p, segments.subdivisions(seg).last().unwrap());
            EndpointRef {
                seg,
                // Because we've just added next_sweep's subdivisions to the segment arena,
                // the last subdivision of this segment should be self.p; we want the previous segment.
                subdivision_idx: segments.subdivisions(seg).len() - 2,
            }
        }));

        // Add left-pointing horizontal segments from the current sweep line.
        endpoints.extend(
            horiz_segments
                .iter()
                .filter_map(|(seg, sub_idx, _sub_idx_count)| {
                    // The subdivisions are listed left to right. As long as we aren't at the first subdivision
                    // point, there's a segment to the left.
                    sub_idx.checked_sub(1).map(|i| EndpointRef {
                        seg: *seg,
                        subdivision_idx: i,
                    })
                }),
        );

        let mut winding = Vec::new();
        let mut w = 0;
        for e in &endpoints {
            winding.push(w);
            w += self.winding_increment(e.seg, e.subdivision_idx, segments);
        }

        OrderedIntersection {
            p: self.p,
            endpoints,
            winding,
        }
    }
}

#[derive(Copy, Clone, Hash, Eq, PartialEq)]
pub struct EndpointRef {
    pub seg: SegRef,
    pub subdivision_idx: usize,
}

impl std::fmt::Debug for EndpointRef {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Seg({}.{})", self.seg.0, self.subdivision_idx)
    }
}

impl EndpointRef {
    pub fn pred(&self) -> Option<EndpointRef> {
        self.subdivision_idx.checked_sub(1).map(|i| EndpointRef {
            seg: self.seg,
            subdivision_idx: i,
        })
    }

    // Without access to the segment arena, there's no way to tell if
    // the next endpoint reference is valid.
    pub fn next(&self) -> EndpointRef {
        EndpointRef {
            seg: self.seg,
            subdivision_idx: self.subdivision_idx + 1,
        }
    }

    // Panics if this is the last endpoint on its segment.
    pub fn next_on_path(&self, segments: &SegmentArena) -> EndpointRef {
        if segments.in_order(self.seg) {
            self.next()
        } else {
            self.pred().unwrap()
        }
    }
}

#[derive(Debug)]
pub struct OrderedIntersection {
    pub p: Point,

    // Other endpoints of segment subdivisions, in clockwise order.
    pub endpoints: Vec<EndpointRef>,

    // "Local" winding numbers. TODO: picture and explanation
    pub winding: Vec<i32>,
}

impl OrderedIntersection {
    /// Find the local winding number to the right of (and above) this intersection point.
    pub fn right_winding(&self, segments: &SegmentArena) -> i32 {
        let idx = self.endpoints.iter().position(|e| {
            let subs = segments.subdivisions(e.seg);
            e.subdivision_idx < subs.len() && subs[e.subdivision_idx].y < self.p.y
        });

        // If this intersection points doesn't stick out anything below, its right winding number is the same as its left one.
        idx.map(|idx| self.winding[idx]).unwrap_or(0)
    }

    // TODO: can build some structure to make this faster
    pub fn counter_clockwise_from(&self, endpoint: EndpointRef) -> EndpointRef {
        let idx = self.endpoints.iter().position(|e| e == &endpoint).unwrap();
        self.endpoints[idx.checked_sub(1).unwrap_or(self.endpoints.len() - 1)]
    }
}

fn mid_range(xs: impl Iterator<Item = Float>) -> Float {
    let (min, max) = xs
        .map(|x| (x, x))
        .reduce(|(lo, hi), (x, y)| (lo.min(x), hi.max(y)))
        .unwrap();
    (min + max) / 2.0
}

pub struct Walker<'a> {
    segments: &'a SegmentArena,
    next_endpoint: HashMap<EndpointRef, EndpointRef>,
    subdivisions: Vec<EndpointRef>,
    visited: HashSet<EndpointRef>,
}

impl<'a> Walker<'a> {
    pub fn new(segments: &'a SegmentArena, ints: &'a [OrderedIntersection], winding: i32) -> Self {
        let mut next_endpoint = HashMap::new();

        for int in ints {
            for (&e0, &e1) in cyclic_pairs(&int.endpoints) {
                // We consider the segment from the intersection center point to e1.
                // To find that segment's winding number, we need to find the smaller (lexicographically)
                // endpoint of the segment.
                let e1_less = segments.subdivision_endpoint(e1) < int.p;
                let seg_start = if e1_less { e1 } else { e1.pred().unwrap() };
                if winding != segments.subdivision_winding(seg_start) {
                    continue;
                }
                // We only add next_endpoint mappings for segments that are oriented into the intersection.
                let oriented_in = e1_less == segments.in_order(e1.seg);
                if !oriented_in {
                    continue;
                }

                // the endpoint at p of the segment whose other endpoint is e0
                let e0_at_p = if segments.subdivision_endpoint(e0) < int.p {
                    e0.next()
                } else {
                    e0.pred().unwrap()
                };
                next_endpoint.insert(e1, e0_at_p);
            }
        }
        dbg!(&next_endpoint);
        dbg!(&ints);

        Self {
            segments,
            subdivisions: next_endpoint.keys().copied().collect(),
            next_endpoint,
            visited: HashSet::new(),
        }
    }

    fn starting_endpoint(&mut self) -> Option<EndpointRef> {
        while let Some(e) = self.subdivisions.pop() {
            if self.visited.insert(e) {
                return Some(e);
            }
        }
        None
    }

    pub fn walk_next_contour(&mut self) -> Option<Vec<Point>> {
        let mut ret = Vec::new();
        let mut e = self.starting_endpoint()?;
        let start_point = self.segments.subdivision_endpoint(e);
        let mut p = start_point;

        loop {
            ret.push(p);
            dbg!(e);
            e = *self.next_endpoint.get(&e).unwrap();
            dbg!(e);
            self.visited.insert(e);

            p = self.segments.subdivision_endpoint(e);
            if p == start_point {
                break;
            }
        }

        Some(ret)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // TODO: test these small examples with perturbations
    #[test]
    fn small_example_basic() {
        let mut sweeper = Sweeper::new(0.1.try_into().unwrap());

        sweeper.add_closed_polyline(&[
            Point::new(0.0, 0.0),
            Point::new(1.0, 1.0),
            Point::new(3.0, -1.0),
            Point::new(4.0, 0.0),
            Point::new(3.0, 1.0),
            Point::new(1.0, -1.0),
        ]);

        sweeper.run();
        dbg!(sweeper.segments.path_iter(SegRef(0)).collect::<Vec<_>>());
        dbg!(sweeper
            .segments
            .walk_winding(&sweeper.ordered_intersections, 1));
    }

    #[test]
    fn small_example_with_vertical() {
        let mut sweeper = Sweeper::new(0.1.try_into().unwrap());

        sweeper.add_closed_polyline(&[
            Point::new(0.0, 0.0),
            Point::new(1.0, 1.0),
            Point::new(1.0, -1.0),
            Point::new(2.0, 0.0),
            Point::new(1.0, 1.0),
            Point::new(1.0, -1.0),
        ]);

        sweeper.run();
        dbg!(sweeper.segments.path_iter(SegRef(0)).collect::<Vec<_>>());
    }

    #[test]
    fn small_example_with_horizontal() {
        let mut sweeper = Sweeper::new(0.1.try_into().unwrap());

        sweeper.add_closed_polyline(&[
            Point::new(0.0, 1.0),
            Point::new(1.0, 1.0),
            Point::new(1.0, -1.0),
            Point::new(2.0, -1.0),
            Point::new(2.0, 1.0),
            Point::new(1.0, 1.0),
            Point::new(1.0, -1.0),
            Point::new(0.0, -1.0),
        ]);

        sweeper.run();
        dbg!(sweeper.segments.path_iter(SegRef(0)).collect::<Vec<_>>());
    }

    #[test]
    fn clockwise() {
        assert!(super::clockwise(
            Point::new(1.0, -1.0),
            Point::new(0.0, 0.0),
            Point::new(2.0, 0.0)
        ));
    }
}
