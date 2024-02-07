use std::{
    cmp::{Ordering, Reverse},
    collections::{BTreeSet, BinaryHeap},
};

use ordered_float::NotNan;

type Float = NotNan<f64>;

// Points are sorted in lexicographic order.
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Point {
    pub x: Float,
    pub y: Float,
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

// The left point of a line is always strictly less than its right point.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct Line {
    pub left: Point,
    pub right: Point,
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

impl PartialOrd for Line {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Line {
    fn cmp(&self, other: &Self) -> Ordering {
        self.left
            .cmp(&other.left)
            .then_with(|| orient(self.left, self.right, other.right))
            .then_with(|| self.right.cmp(&other.right))
    }
}

impl Line {
    pub fn bounding_box(&self) -> Rect {
        Rect {
            xmin: self.left.x,
            xmax: self.right.x,
            ymin: self.left.y.min(self.right.y),
            ymax: self.left.y.max(self.right.y),
        }
    }

    pub fn eval(&self, t: Float) -> Point {
        self.left.affine(self.right, t)
    }

    // TODO: is this complete? Like, if we have one collection of polylines
    // that starts below and ends above some other collection of polylines,
    // are we guaranteed to have an intersection in between? I doubt this is
    // guaranteed, and we probably need to fall back to orient() at some point
    // to make sure intersections are consistent with orderings.
    pub fn intersection(&self, other: &Line) -> LineIntersection {
        let bbox = self.bounding_box().intersect(&other.bounding_box());
        let unit_interval = 0.0..=1.0;
        if bbox.is_empty() {
            return LineIntersection::None;
        }

        let v = self.right - self.left;
        let w = other.right - other.left;
        let d = other.left - self.left;

        let cross = v.cross(w);
        if cross * cross > 0.0 {
            // Solve for the intersection parametrization along v.
            let s = d.cross(w) / cross;
            if !unit_interval.contains(&s) {
                return LineIntersection::None;
            }

            // Solve for the intersection parametrization along w.
            let t = d.cross(v) / cross;
            if !unit_interval.contains(&t) {
                return LineIntersection::None;
            }

            // Since cross*cross > 0, cross is non-zero. Could there
            // be a NaN from inf / inf, though? TODO: we can ensure that
            // there isn't by disallowing points that are too big. As long
            // as the dimensions squared fit in a f64, it should be fine.
            let s = NotNan::new(s).unwrap();
            let t = NotNan::new(t).unwrap();

            // Try to return an exact endpoint if we can.
            let p = if t == 0.0 || t == 1.0 {
                other.eval(t)
            } else {
                self.eval(s)
            };
            LineIntersection::Point(bbox.constrain(p))
        } else {
            // The two lines are (approximately) colinear.
            let cross = d.cross(v);
            if cross * cross > 0.0 {
                return LineIntersection::None;
            }

            // FIXME: nothing prevents denom from being zero here...
            let denom = v.dot(v);
            let s0 = v.dot(d) / denom;
            let s1 = s0 + v.dot(w) / denom;
            let smin = s0.min(s1);
            let smax = s0.max(s1);

            if smin <= 1.0 && smax >= 0.0 {
                let p = bbox.constrain(self.eval(NotNan::new(smin.max(0.0)).unwrap()));
                let q = bbox.constrain(self.eval(NotNan::new(smax.min(1.0)).unwrap()));
                if p == q {
                    LineIntersection::Point(p)
                } else {
                    LineIntersection::Overlap(Line { left: p, right: q })
                }
            } else {
                LineIntersection::None
            }
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum LineIntersection {
    None,
    Point(Point),
    Overlap(Line),
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct SweepEvent {
    pt: Point,
    // We guarantee that this will never equal `pt`.
    other: Point,
    idx: usize,
}

impl SweepEvent {
    pub fn is_left(&self) -> bool {
        self.pt < self.other
    }

    /// Returns (left endpoint, right endpoint).
    pub fn to_line(&self) -> Line {
        if self.is_left() {
            Line {
                left: self.pt,
                right: self.other,
            }
        } else {
            Line {
                left: self.other,
                right: self.pt,
            }
        }
    }
}

impl PartialOrd for SweepEvent {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

// Returns Ordering::Less if c is below the line spanned by a and b.
fn orient(a: Point, b: Point, c: Point) -> Ordering {
    let coord = |p: Point| robust::Coord {
        x: f64::from(p.x),
        y: f64::from(p.y),
    };
    let area = robust::orient2d(coord(a), coord(b), coord(c));

    if area == 0.0 {
        // This special case returns Equal for positive *or negative* zero, which is
        // the behavior we want. By itself, total_cmp would give the wrong result for
        // negative zero.
        Ordering::Equal
    } else {
        area.total_cmp(&0.0)
    }
}

impl Ord for SweepEvent {
    fn cmp(&self, other: &Self) -> Ordering {
        self.pt
            .cmp(&other.pt)
            .then_with(|| self.is_left().cmp(&other.is_left()))
            .then_with(|| {
                let line = self.to_line();
                orient(line.left, line.right, other.pt)
            })
            .then_with(|| self.idx.cmp(&other.idx))
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct SweepLineEntry(SweepEvent);

impl PartialOrd for SweepLineEntry {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

// TODO: understand this ordering, and test some examples
impl Ord for SweepLineEntry {
    fn cmp(&self, other: &Self) -> Ordering {
        debug_assert!(self.0.is_left() && other.0.is_left());

        if other.0.idx == self.0.idx {
            debug_assert!(self == other);
            return Ordering::Equal;
        }
        // It's more convenient to assume that `self` is "before" `other`.
        if self.0 > other.0 {
            return other.cmp(self).reverse();
        }

        let left_orient = orient(self.0.pt, self.0.other, other.0.pt);
        let right_orient = orient(self.0.pt, self.0.other, other.0.other);

        if left_orient.is_ne() || right_orient.is_ne() {
            if self.0.pt == other.0.pt {
                return self.0.other.cmp(&other.0.other);
            } else if self.0.pt.x == other.0.pt.x {
                return self.0.pt.y.cmp(&other.0.pt.y);
            } else if left_orient == right_orient {
                return left_orient.reverse();
            } else if left_orient.is_eq() {
                return right_orient.reverse();
            }

            // According to the orientation, the segments cross (but not necessarily within
            // the bounds of `self`).
            match self.0.to_line().intersection(&other.0.to_line()) {
                LineIntersection::None => {
                    return left_orient.reverse();
                }
                LineIntersection::Point(p) => {
                    if p == self.0.pt {
                        return right_orient.reverse();
                    } else {
                        return left_orient.reverse();
                    }
                }
                LineIntersection::Overlap(_) => {}
            }
        }

        // The two lines are collinear. Fall back to the temporal-based
        // comparison of left endpoint (and in this comparison, we already
        // know that `self` comes first).
        if self.0.pt != other.0.pt {
            Ordering::Less
        } else {
            // Bit arbitrary, but what else do we have to fallback to?
            self.0.idx.cmp(&other.0.idx)
        }
    }
}

pub struct SweepState {
    // These three have the same length.
    pub segments: Vec<Line>,
    pub live: Vec<bool>,
    pub parent: Vec<usize>,

    pub finished_events: Vec<SweepEvent>,
    pub events: BinaryHeap<Reverse<SweepEvent>>,
    pub sweep_line: BTreeSet<SweepLineEntry>,
}

impl SweepState {
    pub fn tick(&mut self) {
        let Some(Reverse(event)) = self.events.pop() else {
            return;
        };

        if !self.live[event.idx] {
            return;
        }

        self.finished_events.push(event);
        if event.is_left() {
            let line = SweepLineEntry(event);
            self.sweep_line.insert(line);

            let maybe_prev = self.sweep_line.range(..line).next_back();
            let maybe_next = self
                .sweep_line
                .range((std::ops::Bound::Excluded(&line), std::ops::Bound::Unbounded))
                .next();

            if let Some(next) = maybe_next {}
            todo!()
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_orient() {
        assert_eq!(
            Ordering::Less,
            orient(
                Point::new(0.0, 0.0),
                Point::new(1.0, 0.0),
                Point::new(0.5, -0.5)
            )
        );

        assert_eq!(
            Ordering::Greater,
            orient(
                Point::new(0.0, 0.0),
                Point::new(1.0, 0.0),
                Point::new(0.5, 0.5)
            )
        );

        assert_eq!(
            Ordering::Equal,
            orient(
                Point::new(0.0, 0.0),
                Point::new(1.0, 0.0),
                Point::new(0.5, 0.0,)
            )
        );
    }
}
