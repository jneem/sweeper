use std::{
    cmp::{Ordering, Reverse},
    collections::BinaryHeap,
};

use ordered_float::NotNan;

type Float = NotNan<f64>;

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
#[derive(Copy, Clone, PartialEq, Eq)]
pub struct Segment {
    pub start: Point,
    pub end: Point,
}

impl std::fmt::Debug for Segment {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?} -- {:?}", self.start, self.end)
    }
}

// A closed, axis-aligned rectangle.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct Rect {
    pub xmin: Float,
    pub xmax: Float,
    pub ymin: Float,
    pub ymax: Float,
}

impl Rect {
    pub fn intersect(&self, other: &Rect) -> Rect {
        Rect {
            xmin: self.xmin.max(other.xmin),
            xmax: self.xmax.min(other.xmax),
            ymin: self.ymin.max(other.ymin),
            ymax: self.ymax.min(other.ymax),
        }
    }

    pub fn is_empty(&self) -> bool {
        self.xmin > self.xmax || self.ymin > self.ymax
    }

    // Panics if we're empty.
    pub fn constrain(&self, p: Point) -> Point {
        Point {
            x: p.x.clamp(self.xmin, self.xmax),
            y: p.y.clamp(self.ymin, self.ymax),
        }
    }
}

impl Segment {
    pub fn bounding_box(&self) -> Rect {
        Rect {
            xmin: self.start.x,
            xmax: self.end.x,
            ymin: self.start.y.min(self.end.y),
            ymax: self.start.y.max(self.end.y),
        }
    }

    pub fn eval(&self, t: Float) -> Point {
        self.start.affine(self.end, t)
    }

    pub fn at_y(&self, y: Float) -> Float {
        assert!((self.start.y..=self.end.y).contains(&y));

        // FIXME: handle horizontal-ish segments
        let t = (y - self.start.y) / (self.end.y - self.start.y);
        self.eval(t).x
    }

    pub fn end_offset(&self, other: &Segment) -> Float {
        // TODO: assert that the domains intersect?
        if self.end.y < other.end.y {
            other.at_y(self.end.y) - self.end.x
        } else {
            other.end.x - self.at_y(other.end.y)
        }
    }

    /// Does the other segment cross us by at least epsilon to the right?
    pub fn crossed_right_by(&self, other: &Segment, eps: Float) -> bool {
        self.end_offset(other) >= eps
    }

    /// Does the other segment cross us by at least epsilon to the right?
    pub fn robustly_crossed_right_by(&self, other: &Segment, initial_y: Float, eps: Float) -> bool {
        let start_offset = other.at_y(initial_y) - self.at_y(initial_y);
        let end_offset = self.end_offset(other);

        end_offset >= -eps / 4.0 && end_offset >= start_offset + eps / 2.0
    }

    /// Does the other segment cross us by at least epsilon to the left?
    pub fn crossed_left_by(&self, other: &Segment, eps: Float) -> bool {
        self.end_offset(other) <= -eps
    }

    /// Does the other segment cross us by at least epsilon to the left?
    pub fn robustly_crossed_left_by(&self, other: &Segment, initial_y: Float, eps: Float) -> bool {
        let start_offset = other.at_y(initial_y) - self.at_y(initial_y);
        let end_offset = self.end_offset(other);

        end_offset <= eps / 4.0 && end_offset <= start_offset - eps / 2.0
    }

    pub fn intersection_y(&self, other: &Segment) -> Float {
        let u = self.end - self.start;
        let v = other.end - other.start;
        let w = other.start - self.start;

        let det = u.cross(v);
        let s = (w.cross(v) / det).clamp(0.0, 1.0);
        self.start.y + s * (self.end.y - self.start.y).into_inner()
    }

    pub fn interaction_from_left(&self, _other: &Segment) -> Interaction {
        todo!()
    }
}

#[derive(Debug, Clone, Copy, PartialOrd, Ord, PartialEq, Eq)]
pub struct SegRef(usize);

#[derive(Clone, Copy, PartialOrd, Ord, PartialEq, Eq)]
pub struct SweepEvent {
    y: Float,
    payload: SweepEventPayload,
}

pub enum Interaction {
    Close,
    CloseCrosses,
    Crosses,
    Covers,
    Ignores,
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
            payload: SweepEventPayload::Intersection { y, left, right },
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
    Intersection {
        // TODO: remove this? It's in SweepEvent anyway. Or maybe remove that one...
        y: Float,
        left: SegRef,
        right: SegRef,
    },
    EnterEnter {
        left: SegRef,
        right: SegRef,
    },
    ExitExit {
        left: SegRef,
        right: SegRef,
    },
    ExitEnter {
        exit: SegRef,
        enter: SegRef,
    },
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

pub enum InvariantViolation {
    SegmentDomain { seg: Segment, y: Float },
    SegmentOrder { before: Segment, after: Segment },
    MissingEvent { left: Segment, right: Segment },
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
}

impl std::fmt::Debug for EventQueue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_list()
            .entries(self.inner.iter().map(|Reverse(x)| x))
            .finish()
    }
}

impl SweepLine {
    pub fn check_invariants(&self) -> Result<(), InvariantViolation> {
        todo!()
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
        // TODO: should be able to do this in logarithmic time
        self.segments.iter().position(|s| s == &seg).unwrap()
    }

    fn scan_left(
        &mut self,
        mut idx: usize,
        eps: Float,
        allow_swap: bool,
        arena: &SegmentArena,
    ) -> (usize, Option<SweepEvent>) {
        let scanning_seg = arena.get(self.segments[idx]);
        let x = scanning_seg.at_y(self.y);

        for j in (0..idx).rev() {
            let seg = arena.get(self.segments[j]);
            // TODO: this also counts crossings of segments that are adjacent in
            // the contour. It's harmless, but we can filter them out
            if scanning_seg.robustly_crossed_right_by(&seg, self.y, eps) {
                let int_y = scanning_seg.intersection_y(&seg);
                assert!(int_y > self.y);
                return (
                    idx,
                    Some(SweepEvent::intersection(
                        self.segments[j],
                        self.segments[idx],
                        int_y,
                    )),
                );
            } else if seg.at_y(self.y) < x - eps {
                return (idx, None);
            } else if allow_swap && scanning_seg.crossed_right_by(&seg, eps * 0.75) {
                self.segments[j..=idx].rotate_right(1);
                idx = j;
            }
        }
        (idx, None)
    }

    fn scan_right(
        &mut self,
        mut idx: usize,
        eps: Float,
        allow_swap: bool,
        arena: &SegmentArena,
    ) -> (usize, Option<SweepEvent>) {
        let scanning_seg = arena.get(self.segments[idx]);
        let x = scanning_seg.at_y(self.y);

        for j in (idx + 1)..self.segments.len() {
            let seg = arena.get(self.segments[j]);
            if scanning_seg.robustly_crossed_left_by(&seg, self.y, eps) {
                let int_y = scanning_seg.intersection_y(&seg);
                assert!(int_y > self.y);
                return (
                    idx,
                    Some(SweepEvent::intersection(
                        self.segments[idx],
                        self.segments[j],
                        int_y,
                    )),
                );
            } else if seg.at_y(self.y) > x + eps {
                return (idx, None);
            } else if allow_swap && scanning_seg.crossed_left_by(&seg, eps * 0.75) {
                self.segments[idx..=j].rotate_left(1);
                idx = j;
            }
        }
        (idx, None)
    }

    fn scan_both(
        &mut self,
        idx: usize,
        eps: Float,
        arena: &SegmentArena,
    ) -> impl Iterator<Item = SweepEvent> {
        let (idx, ev1) = self.scan_right(idx, eps, true, arena);
        let (_, ev2) = self.scan_left(idx, eps, true, arena);
        ev1.into_iter().chain(ev2)
    }

    pub fn process_event(
        &mut self,
        event: SweepEvent,
        eps: Float,
        arena: &SegmentArena,
        queue: &mut EventQueue,
    ) {
        self.y = event.y;
        match event.payload {
            SweepEventPayload::EnterEnter { left, right } => {
                let left_seg = arena.get(left);
                let right_seg = arena.get(right);

                assert_eq!(left_seg.start, right_seg.start);
                let start = left_seg.start;

                let idx = self.search_x(start.x, arena);
                self.segments.insert(idx, right);
                self.segments.insert(idx, left);

                queue.extend(self.scan_left(idx, eps, true, arena).1);
                queue.extend(self.scan_right(idx + 1, eps, true, arena).1);
            }
            SweepEventPayload::ExitEnter { exit, enter } => {
                let idx = self.find_seg_ref(exit);
                self.segments[idx] = enter;

                queue.extend(self.scan_both(idx, eps, arena));
            }
            SweepEventPayload::ExitExit { left, right } => {
                let left_idx = self.find_seg_ref(left);
                let right_idx = self.find_seg_ref(right);

                // If these last segments are almost parallel, it's probably possible for them to be in the "wrong" order.
                let (left_idx, mut right_idx) = (left_idx.min(right_idx), left_idx.max(right_idx));
                self.segments.remove(left_idx);
                right_idx -= 1;
                self.segments.remove(right_idx);
                if let Some(left_left) = left_idx.checked_sub(1) {
                    queue.extend(self.scan_left(left_left, eps, false, arena).1);
                }
                if right_idx < self.segments.len() {
                    queue.extend(self.scan_right(right_idx, eps, false, arena).1);
                }
            }
            SweepEventPayload::Intersection { left, right, .. } => {
                let left_idx = self.find_seg_ref(left);
                let right_idx = self.find_seg_ref(right);

                // I don't expect this test to fail, but I'm not sure it's actually impossible.
                if left_idx < right_idx {
                    self.segments.swap(left_idx, right_idx);
                    let (left_idx, right_idx) = (right_idx, left_idx);
                    queue.extend(self.scan_both(left_idx, eps, arena));

                    // It should be impossible for the two just-intersected segments to swap.
                    assert_eq!(right_idx, self.find_seg_ref(right));
                    queue.extend(self.scan_both(right_idx, eps, arena));
                }
            }
        }
    }
}

#[derive(Debug, Default)]
pub struct SegmentArena {
    pub all_segments: Vec<Segment>,
    in_order: Vec<bool>,
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
        SegRef(self.all_segments.len() - 1)
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
    pub eps: Float,
}

impl Sweeper {
    pub fn step(&mut self) {
        if let Some(event) = self.queue.pop() {
            self.sweep_line
                .process_event(event, self.eps, &self.segments, &mut self.queue)
        }
    }

    pub fn run(&mut self) {
        dbg!(&self);
        while !self.queue.is_empty() {
            self.step();
            dbg!(&self.sweep_line, &self.queue);
        }
    }

    pub fn add_closed_polyline(&mut self, points: &[Point]) {
        assert!(points.len() >= 2);

        let mut new_segs = Vec::new();
        for (p0, p1) in cyclic_pairs(points) {
            new_segs.push(self.segments.insert(*p0, *p1));
        }

        for (&i, &j) in cyclic_pairs(&new_segs) {
            self.queue
                .push(SweepEvent::from_adjacent_segments(i, j, &self.segments));
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn small_example() {
        let mut sweeper = Sweeper {
            sweep_line: SweepLine::default(),
            queue: EventQueue::default(),
            segments: SegmentArena::default(),
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
    fn clockwise() {
        assert!(super::clockwise(
            Point::new(1.0, -1.0),
            Point::new(0.0, 0.0),
            Point::new(2.0, 0.0)
        ));
    }

    #[test]
    fn robust_crossing() {
        let s0 = Segment {
            start: Point::new(1.0, -1.0),
            end: Point::new(3.0, 1.0),
        };
        let s1 = Segment {
            start: Point::new(3.0, -1.0),
            end: Point::new(1.0, 1.0),
        };
        let y = NotNan::new(-1.0).unwrap();
        let eps = NotNan::new(0.1).unwrap();

        assert!(s0.robustly_crossed_left_by(&s1, y, eps));
        assert!(s1.robustly_crossed_right_by(&s0, y, eps));
    }

    #[test]
    fn intersection_y() {
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

        assert_eq!(a.intersection_y(&b), 5.0);
        assert_eq!(b.intersection_y(&a), 5.0);
        assert_eq!(a.intersection_y(&c), 5.0);
        assert_eq!(c.intersection_y(&a), 5.0);
        assert_eq!(b.intersection_y(&c), 5.0);
        assert_eq!(c.intersection_y(&b), 5.0);
    }
}
