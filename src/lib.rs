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

#[derive(Clone, Copy, PartialOrd, Ord, PartialEq, Eq, Hash)]
pub struct SegRef(usize);

impl std::fmt::Debug for SegRef {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "s_{}", self.0)
    }
}

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

    fn from_segment(i: SegRef, arena: &SegmentArena) -> (SweepEvent, SweepEvent) {
        let s = arena.get(i);
        (
            SweepEvent {
                y: s.start.y,
                payload: SweepEventPayload::Enter(i),
            },
            SweepEvent {
                y: s.end.y,
                payload: SweepEventPayload::Exit(i),
            },
        )
    }
}

impl std::fmt::Debug for SweepEvent {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?} -> {:?}", self.y.into_inner(), self.payload)
    }
}

#[derive(Clone, Copy, PartialOrd, Ord, PartialEq, Eq)]
pub enum SweepEventPayload {
    Enter(SegRef),
    Intersection { left: SegRef, right: SegRef },
    Exit(SegRef),
}

impl std::fmt::Debug for SweepEventPayload {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SweepEventPayload::Intersection { left, right, .. } => {
                write!(f, "left({left:?}) x right({right:?})")
            }
            SweepEventPayload::Enter(seg) => {
                write!(f, "enter({seg:?})")
            }
            SweepEventPayload::Exit(seg) => {
                write!(f, "exit({seg:?})")
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
        // Multiplying by 2 is a bit sloppier than necessary, but in the actual algorithm we
        // compare to epsilon using inexact math...
        let eps = Rational::try_from(2.0 * eps.into_inner()).unwrap();
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
                        let ev_segs = match ev.payload {
                            SweepEventPayload::Intersection { left, right } => vec![left, right],
                            SweepEventPayload::Enter(s) => vec![s],
                            SweepEventPayload::Exit(s) => vec![s],
                        };
                        ev.y.into_inner() <= y_int
                            && ev_segs.iter().any(|s| between_segs.contains(&s))
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
                    idx += 1;
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

    // For debugging...
    pub fn segment_positions(&self, ctx: &SweepContext) -> Vec<f64> {
        self.segments
            .iter()
            .map(|s| ctx.segments.get(*s).at_y(self.y).into_inner())
            .collect()
    }

    pub fn process_event(&mut self, ctx: &mut SweepContext, event: SweepEvent) {
        dbg!(&event);
        self.y = event.y;
        match event.payload {
            SweepEventPayload::Enter(s) => {
                // TODO: add an intersection between this new event and anything in the
                // sweep-line that's adjacent to it in the original contour.
                let seg = ctx.segments.get(s);

                let idx = self.search_x(seg.start.x, ctx.segments);
                self.segments.insert(idx, s);

                let idx = self.scan_left(ctx, idx, true);
                self.scan_right(ctx, idx, true);
            }
            SweepEventPayload::Exit(s) => {
                let idx = self.find_seg_ref(s);

                self.segments.remove(idx);
                if let Some(left_nbr) = idx.checked_sub(1) {
                    self.scan_right(ctx, left_nbr, false);
                }
                if idx < self.segments.len() {
                    // Since we removed a segment, `idx` now points at what was previously to its right.
                    self.scan_left(ctx, idx, false);
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
}

// All the vecs here have the same length and same indexing.
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
            //assert!(p1 < p0);
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
    pub fn new(eps: Float) -> Self {
        Sweeper {
            sweep_line: SweepLine::default(),
            queue: EventQueue::default(),
            segments: SegmentArena::default(),
            intersections: Vec::new(),
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

    // Like run, but doesn't resolve intersections.
    pub fn sweep(&mut self) {
        dbg!(&self);
        while !self.queue.is_empty() {
            self.step();
            self.sweep_line
                .check_invariants(self.eps, &self.segments, &self.queue)
                .unwrap();
        }
    }

    pub fn add_closed_polyline(&mut self, points: &[Point]) {
        assert!(points.len() >= 2);

        let mut new_segs = Vec::new();
        for (p0, p1) in cyclic_pairs(points) {
            new_segs.push(self.segments.insert(*p0, *p1));
        }

        for (&i, &j) in cyclic_pairs(&new_segs) {
            self.segments.add_contour_link(i, j);
            let (enter, exit) = SweepEvent::from_segment(i, &self.segments);
            self.queue.push(enter);
            self.queue.push(exit);
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
        let mut sweeper = Sweeper::new(0.1.try_into().unwrap());

        sweeper.add_closed_polyline(&[
            Point::new(0.0, 0.0),
            Point::new(1.0, 1.0),
            Point::new(3.0, -1.0),
            Point::new(4.0, 0.0),
            Point::new(3.0, 1.0),
            Point::new(1.0, -1.0),
        ]);

        sweeper.sweep();
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

        sweeper.sweep();
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

        sweeper.sweep();
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
