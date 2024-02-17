use std::{
    cmp::{Ordering, Reverse},
    collections::{BinaryHeap, HashSet},
};

use malachite::Rational;
use ordered_float::NotNan;

type Float = NotNan<f64>;

pub mod equivalence;
pub mod exact;

// Points are sorted by `y` and then by `x`
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Point {
    pub y: Float,
    pub x: Float,
}

impl Point {
    pub fn new(x: f64, y: f64) -> Point {
        Point {
            x: NotNan::new(x).unwrap(),
            y: NotNan::new(y).unwrap(),
        }
    }

    // Panics on nans. Should be fine as long as everything is finite.
    pub fn affine(self, other: Point, t: Float) -> Point {
        let one = NotNan::new(1.0).unwrap();
        Point {
            x: (one - t) * self.x + t * other.x,
            y: (one - t) * self.y + t * other.y,
        }
    }
}

impl std::ops::Sub for Point {
    type Output = Vector;

    fn sub(self, rhs: Self) -> Self::Output {
        Vector {
            x: self.x - rhs.x,
            y: self.y - rhs.y,
        }
    }
}

impl std::fmt::Debug for Point {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "({:?}, {:?})", self.x.into_inner(), self.y.into_inner())
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct Vector {
    pub x: Float,
    pub y: Float,
}

impl Vector {
    pub fn cross(&self, other: Vector) -> f64 {
        self.x.into_inner() * other.y.into_inner() - self.y.into_inner() * other.x.into_inner()
    }

    pub fn dot(&self, other: Vector) -> f64 {
        self.x.into_inner() * other.x.into_inner() + self.y.into_inner() * other.y.into_inner()
    }
}

// The start point of a line is always strictly less than its end point.
// This is the right representation for most of the sweep-line operations,
// but it's a little clunky for other things because we need to keep track of
// the original orientation.
#[derive(Copy, Clone, PartialEq, Eq)]
pub struct Segment {
    pub start: Point,
    pub end: Point,
}

impl Segment {
    /// The second return value is true if the original point order was preserved.
    ///
    /// Panics if the points are equal.
    pub fn from_unordered_points(p0: Point, p1: Point) -> (Segment, bool) {
        match p0.cmp(&p1) {
            Ordering::Less => (Segment { start: p0, end: p1 }, true),
            Ordering::Greater => (Segment { start: p1, end: p0 }, false),
            Ordering::Equal => panic!("empty segment"),
        }
    }
}

impl std::fmt::Debug for Segment {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?} -- {:?}", self.start, self.end)
    }
}

impl Segment {
    pub fn eval(&self, t: Float) -> Point {
        self.start.affine(self.end, t)
    }

    /// Our `x` coordinate at the given `y` coordinate.
    ///
    /// Horizontal segments will return their largest `x` coordinate.
    ///
    /// Panics if `y` is outside the `y` range of this segment.
    pub fn at_y(&self, y: Float) -> Float {
        assert!((self.start.y..=self.end.y).contains(&y));

        if self.start.y == self.end.y {
            self.end.x
        } else {
            // Even if the segment is *almost* horizontal, t is guaranteed
            // to be in [0.0, 1.0].
            let t = (y - self.start.y) / (self.end.y - self.start.y);
            self.eval(t).x
        }
    }

    /// Returns the x difference between segments at the last y position that they share.
    /// Returns a positive value if `other` is to the right.
    ///
    /// (Returns nonsense if they don't share a y position.)
    pub fn end_offset(&self, other: &Segment) -> Float {
        if self.end.y < other.end.y {
            other.at_y(self.end.y) - self.end.x
        } else {
            other.end.x - self.at_y(other.end.y)
        }
    }

    /// Returns the x difference between segments at the first y position that they share.
    /// Returns a positive value if `other` is to the right.
    ///
    /// (Returns nonsense if they don't share a y position.)
    pub fn start_offset(&self, other: &Segment) -> Float {
        if self.start.y >= other.start.y {
            other.at_y(self.start.y) - self.start.x
        } else {
            other.start.x - self.at_y(other.start.y)
        }
    }

    /// Returns the y-coordinate of the intersection between this segment and the other, if
    /// there is one and we can get an accurate estimate of it.
    ///
    /// We guarantee that if this returns a y value, the two line segments have approximately
    /// the same x-coordinate (within eps/2) at that y value.
    ///
    /// (Actually, we don't guarantee anything of the sort because I haven't done the analysis
    /// yet. But that's the guarantee we need. We're allowed to assume that the lines aren't
    /// close to horizontal.)
    ///
    /// This function is allowed to have false negatives (i.e. fail to find an intersection if
    /// there is one but just barely). In this case the intersection will be caught by comparing
    /// x coordinates along the sweep line.
    pub fn approx_intersection_y(&self, other: &Segment, eps: Float) -> Option<Float> {
        let u = self.end - self.start;
        let v = other.end - other.start;
        let w = other.start - self.start;

        let det = u.cross(v);

        // This probably isn't the right test. The guarantee we want is: at the y coordinate
        // of intersection, guarantee that the x coordinates are at most eps/2 apart.
        // Probably the real bound will need some assumption on the magnitudes of all the coordinates?
        if det.abs() > eps.sqrt() {
            let s = w.cross(v) / det;
            let t = w.cross(u) / det;
            if (0.0..=1.0).contains(&s) && (0.0..=1.0).contains(&t) {
                return Some(self.start.y + s * (self.end.y - self.start.y).into_inner());
            }
        }
        None
    }

    pub fn is_exactly_horizontal(&self) -> bool {
        self.start.y == self.end.y
    }

    // TODO: should this depend on epsilon? probably.
    pub fn is_almost_horizontal(&self) -> bool {
        (self.start.x - self.end.x).abs() >= 1e3 * (self.start.y - self.end.y).abs()
    }

    /// If the other segment starts to the left of us, what is the interaction like?
    pub fn compare_to_the_left(
        &self,
        other: &Segment,
        y: Float,
        eps: Float,
    ) -> (Crosses, Interaction) {
        let start_offset = other.at_y(y) - self.at_y(y);
        let end_offset = self.end_offset(other);

        // TODO: explain why we shift the other guy
        let y_int = self.approx_intersection_y(&other.shift_horizontal(eps / 2.0), eps);
        let y_int = y_int
            .filter(|z| z >= &y && !self.is_exactly_horizontal() && !other.is_exactly_horizontal());

        if let Some(y) = y_int {
            // Because of the shift, maybe there wasn't really an intersection. Or maybe
            // the intersection was in the wrong direction.
            if end_offset.into_inner() > 0.0 {
                (Crosses::At { y }, Interaction::Blocks)
            } else {
                (Crosses::Never, Interaction::Ignores)
            }
        } else {
            // No intersection, or there was an intersection but we're more-or-less parallel.
            let crosses = if end_offset >= eps {
                Crosses::Now
            } else {
                Crosses::Never
            };
            #[allow(clippy::if_same_then_else)]
            let interact = if end_offset < eps && end_offset >= start_offset + eps {
                // TODO: the condition above needs to be compatible with the bound in
                // approx_intersection_y. We need to ensure that if we failed to find
                // an intersection and the above condition holds, they really are
                // disjoint after y.
                Interaction::Blocks
            } else if end_offset < -eps {
                Interaction::Blocks
            } else {
                Interaction::Ignores
            };
            (crosses, interact)
        }
    }

    pub fn compare_to_the_right(
        &self,
        other: &Segment,
        y: Float,
        eps: Float,
    ) -> (Crosses, Interaction) {
        self.reflect().compare_to_the_left(&other.reflect(), y, eps)
    }

    /// Reflect this segment horizontally.
    pub fn reflect(&self) -> Segment {
        Segment {
            start: Point {
                x: -self.start.x,
                y: self.start.y,
            },
            end: Point {
                x: -self.end.x,
                y: self.end.y,
            },
        }
    }

    pub fn shift_horizontal(&self, delta: Float) -> Segment {
        Segment {
            start: Point {
                x: self.start.x + delta,
                y: self.start.y,
            },
            end: Point {
                x: self.end.x + delta,
                y: self.end.y,
            },
        }
    }
}

#[derive(Debug, Clone, Copy, PartialOrd, Ord, PartialEq, Eq, Hash)]
pub struct SegRef(usize);

#[derive(Clone, Copy, PartialOrd, Ord, PartialEq, Eq)]
pub struct SweepEvent {
    y: Float,
    payload: SweepEventPayload,
}

#[derive(Debug)]
pub enum Crosses {
    Now,
    At { y: Float },
    Never,
}

#[derive(Debug)]
pub enum Interaction {
    Blocks,
    Ignores,
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
                Ordering::Less => low = mid,
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

                self.scan_left(ctx, idx, true);
                self.scan_right(ctx, idx + 1, true);
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
                ctx.emit_intersection(self.y, left, right);
                let left_idx = self.find_seg_ref(left);
                let right_idx = self.find_seg_ref(right);

                // I don't expect this test to fail, but I'm not sure it's actually impossible.
                if left_idx < right_idx {
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
}

#[derive(Debug, Default)]
pub struct SegmentArena {
    pub all_segments: Vec<Segment>,
    in_order: Vec<bool>,
    contour_next: Vec<SegRef>,
    contour_prev: Vec<SegRef>,
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
        seg
    }

    /// Mark s1 as following s0 in a contour.
    pub fn add_contour_link(&mut self, s0: SegRef, s1: SegRef) {
        self.contour_next[s0.0] = s1;
        self.contour_prev[s1.0] = s0;
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
    pub eps: Float,
}

impl Sweeper {
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
            let intersections = self.run_one_y();
            dbg!(&self.sweep_line, &self.queue, &intersections);
            self.sweep_line
                .check_invariants(self.eps, &self.segments, &self.queue)
                .unwrap();
        }
        dbg!(&self.intersections);
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

fn mid_range(xs: impl Iterator<Item = Float>) -> Float {
    let (min, max) = xs
        .map(|x| (x, x))
        .reduce(|(lo, hi), (x, y)| (lo.min(x), hi.max(y)))
        .unwrap();
    (min + max) / 2.0
}

#[cfg(test)]
mod tests {
    use super::*;

    // TODO: test these small examples with perturbations
    #[test]
    fn small_example_basic() {
        let mut sweeper = Sweeper {
            sweep_line: SweepLine::default(),
            queue: EventQueue::default(),
            segments: SegmentArena::default(),
            intersections: Vec::new(),
            eps: 0.1.try_into().unwrap(),
        };

        sweeper.add_closed_polyline(&[
            Point::new(0.0, 0.0),
            Point::new(1.0, 1.0),
            Point::new(3.0, -1.0),
            Point::new(4.0, 0.0),
            Point::new(3.0, 1.0),
            Point::new(1.0, -1.0),
        ]);

        sweeper.run();
    }

    #[test]
    fn small_example_with_vertical() {
        let mut sweeper = Sweeper {
            sweep_line: SweepLine::default(),
            queue: EventQueue::default(),
            segments: SegmentArena::default(),
            intersections: Vec::new(),
            eps: 0.1.try_into().unwrap(),
        };

        sweeper.add_closed_polyline(&[
            Point::new(0.0, 0.0),
            Point::new(1.0, 1.0),
            Point::new(1.0, -1.0),
            Point::new(2.0, 0.0),
            Point::new(1.0, 1.0),
            Point::new(1.0, -1.0),
        ]);

        sweeper.run();
    }

    #[test]
    fn small_example_with_horizontal() {
        let mut sweeper = Sweeper {
            sweep_line: SweepLine::default(),
            queue: EventQueue::default(),
            segments: SegmentArena::default(),
            intersections: Vec::new(),
            eps: 0.1.try_into().unwrap(),
        };

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
    }

    #[test]
    fn clockwise() {
        assert!(super::clockwise(
            Point::new(1.0, -1.0),
            Point::new(0.0, 0.0),
            Point::new(2.0, 0.0)
        ));
    }

    #[test]
    fn approx_intersection_y() {
        let a = Segment {
            start: Point::new(0.0, 0.0),
            end: Point::new(0.0, 10.0),
        };
        let b = Segment {
            start: Point::new(-5.0, 0.0),
            end: Point::new(5.0, 10.0),
        };
        let c = Segment {
            start: Point::new(-5.0, 2.0),
            end: Point::new(5.0, 8.0),
        };

        let eps = Float::try_from(0.1).unwrap();
        assert_eq!(a.approx_intersection_y(&b, eps).unwrap(), 5.0);
        assert_eq!(b.approx_intersection_y(&a, eps).unwrap(), 5.0);
        assert_eq!(a.approx_intersection_y(&c, eps).unwrap(), 5.0);
        assert_eq!(c.approx_intersection_y(&a, eps).unwrap(), 5.0);
        assert_eq!(b.approx_intersection_y(&c, eps).unwrap(), 5.0);
        assert_eq!(c.approx_intersection_y(&b, eps).unwrap(), 5.0);
    }
}
