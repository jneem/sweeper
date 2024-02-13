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

        if self.start.y == self.end.y {
            self.start.x
        } else {
            // Even if the segment is *almost* horizontal, t is guaranteed
            // to be in [0.0, 1.0].
            let t = (y - self.start.y) / (self.end.y - self.start.y);
            self.eval(t).x
        }
    }

    pub fn end_offset(&self, other: &Segment) -> Float {
        // TODO: assert that the domains intersect?
        if self.end.y < other.end.y {
            other.at_y(self.end.y) - self.end.x
        } else {
            other.end.x - self.at_y(other.end.y)
        }
    }

    pub fn start_offset(&self, other: &Segment) -> Float {
        // TODO: assert that the domains intersect?
        if self.start.y >= other.start.y {
            other.at_y(self.start.y) - self.start.x
        } else {
            other.start.x - self.at_y(other.start.y)
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
            if (0.0..=1.0).contains(&s) {
                return Some(self.start.y + s * (self.end.y - self.start.y).into_inner());
            }
        }
        None
    }

    pub fn is_exactly_horizontal(&self) -> bool {
        self.start.y == self.end.y
    }

    // TODO: should this depend on epsilon?
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
        let y_int = y_int.filter(|z| z >= &y);

        match (self.is_almost_horizontal(), other.is_almost_horizontal()) {
            (true, true) => todo!(),
            (true, false) => todo!(),
            (false, true) => todo!(),
            (false, false) => {
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
                    let interact = if end_offset < eps && end_offset >= start_offset + eps {
                        // TODO: the condition above needs to be compatible with the bound in
                        // approx_intersection_y. We need to ensure that if we failed to find
                        // an intersection and the above condition holds, they really are
                        // disjoint after y.
                        Interaction::Blocks
                    } else {
                        Interaction::Ignores
                    };
                    (crosses, interact)
                }
            }
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

#[derive(Debug, Clone, Copy, PartialOrd, Ord, PartialEq, Eq)]
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
        queue: &mut EventQueue,
    ) -> usize {
        let scanning_seg = arena.get(self.segments[idx]);

        for j in (0..idx).rev() {
            let seg = arena.get(self.segments[j]);
            // TODO: this also counts crossings of segments that are adjacent in
            // the contour. It's harmless, but we can filter them out
            let (crosses, interaction) = scanning_seg.compare_to_the_left(&seg, self.y, eps);
            match crosses {
                Crosses::At { y } => queue.push(SweepEvent::intersection(
                    self.segments[j],
                    self.segments[idx],
                    y,
                )),
                Crosses::Now if allow_swap => {
                    // TODO: does it matter which way we rotate? Everything in between is supposed to be eps-close anyway...
                    // It might matter for almost-horizontal segments
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

    fn scan_right(
        &mut self,
        mut idx: usize,
        eps: Float,
        allow_swap: bool,
        arena: &SegmentArena,
        queue: &mut EventQueue,
    ) -> usize {
        let scanning_seg = arena.get(self.segments[idx]);

        for j in (idx + 1)..self.segments.len() {
            let seg = arena.get(self.segments[j]);
            // TODO: this also counts crossings of segments that are adjacent in
            // the contour. It's harmless, but we can filter them out
            let (crosses, interaction) = scanning_seg.compare_to_the_right(&seg, self.y, eps);
            match crosses {
                Crosses::At { y } => queue.push(SweepEvent::intersection(
                    self.segments[idx],
                    self.segments[j],
                    y,
                )),
                Crosses::Now if allow_swap => {
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

    fn scan_both(&mut self, idx: usize, eps: Float, arena: &SegmentArena, queue: &mut EventQueue) {
        let idx = self.scan_right(idx, eps, true, arena, queue);
        self.scan_left(idx, eps, true, arena, queue);
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

                self.scan_left(idx, eps, true, arena, queue);
                self.scan_right(idx + 1, eps, true, arena, queue);
            }
            SweepEventPayload::ExitEnter { exit, enter } => {
                let idx = self.find_seg_ref(exit);
                self.segments[idx] = enter;

                self.scan_both(idx, eps, arena, queue);
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
                    self.scan_left(left_left, eps, false, arena, queue);
                }
                if right_idx < self.segments.len() {
                    self.scan_right(right_idx, eps, false, arena, queue);
                }
            }
            SweepEventPayload::Intersection { left, right, .. } => {
                let left_idx = self.find_seg_ref(left);
                let right_idx = self.find_seg_ref(right);

                // I don't expect this test to fail, but I'm not sure it's actually impossible.
                if left_idx < right_idx {
                    self.segments.swap(left_idx, right_idx);
                    let (left_idx, right_idx) = (right_idx, left_idx);
                    self.scan_both(left_idx, eps, arena, queue);

                    // It should be impossible for the two just-intersected segments to swap.
                    assert_eq!(right_idx, self.find_seg_ref(right));
                    self.scan_both(right_idx, eps, arena, queue);
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
