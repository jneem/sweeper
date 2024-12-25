use std::collections::{HashMap, VecDeque};

use crate::{
    geom::Point,
    num::Float,
    segments::{SegIdx, Segments},
    weak_ordering::{self, HSeg, PositionIter, WeakSweepLinePair},
};

/// We support boolean operations, so a "winding number" for us is two winding
/// numbers, one for each shape.
#[derive(Clone, Copy, Hash, PartialEq, Eq, Default, serde::Serialize)]
pub struct WindingNumber {
    pub shape_a: i32,
    pub shape_b: i32,
}

impl std::fmt::Debug for WindingNumber {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}a + {}b", self.shape_a, self.shape_b)
    }
}

/// For a segment, we store two winding numbers (one on each side of the segment).
///
/// For simple segments, the winding numbers on two sides only differ by one. Once
/// we merge segments, they can differ by more.
#[derive(Clone, Copy, Hash, PartialEq, Eq, Default, serde::Serialize)]
pub struct HalfSegmentWindingNumbers {
    /// This half-segment is incident to a point. Imagine you're standing at
    /// that point, looking out along the segment. This is the winding number of
    /// the area just counter-clockwise (to the left, from your point of view)
    /// of the segment.
    pub counter_clockwise: WindingNumber,
    /// This half-segment is incident to a point. Imagine you're standing at
    /// that point, looking out along the segment. This is the winding number of
    /// the area just clockwise (to the right, from your point of view) of the segment.
    pub clockwise: WindingNumber,
}

impl HalfSegmentWindingNumbers {
    /// A half-segment's winding numbers are trivial if they're the same on both sides.
    /// In this case, the segment is invisible to the topology of the sets.
    fn is_trivial(&self) -> bool {
        self.counter_clockwise == self.clockwise
    }

    /// Returns the winding numbers of our opposite half-segment.
    fn flipped(self) -> Self {
        Self {
            counter_clockwise: self.clockwise,
            clockwise: self.counter_clockwise,
        }
    }
}

impl std::fmt::Debug for HalfSegmentWindingNumbers {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?} | {:?}", self.clockwise, self.counter_clockwise)
    }
}

/// An index into the set of output segments.
///
/// There's no compile-time magic preventing misuse of this index, but you
/// should only use this to index into the [`Topology`] that you got it from.
#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq, serde::Serialize)]
pub struct OutputSegIdx(pub usize);

impl OutputSegIdx {
    pub fn first_half(self) -> HalfOutputSegIdx {
        HalfOutputSegIdx {
            idx: self,
            first_half: true,
        }
    }
    pub fn second_half(self) -> HalfOutputSegIdx {
        HalfOutputSegIdx {
            idx: self,
            first_half: false,
        }
    }
}

#[derive(Clone, Copy, Hash, PartialEq, Eq, serde::Serialize)]
pub struct HalfOutputSegIdx {
    idx: OutputSegIdx,
    first_half: bool,
}

impl HalfOutputSegIdx {
    fn other_half(self) -> Self {
        Self {
            idx: self.idx,
            first_half: !self.first_half,
        }
    }
}

impl std::fmt::Debug for HalfOutputSegIdx {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.first_half {
            write!(f, "s{}->", self.idx.0)
        } else {
            write!(f, "s{}<-", self.idx.0)
        }
    }
}

/// A vector indexed by half-output segments.
#[derive(Clone, Debug, Hash, PartialEq, Eq, serde::Serialize)]
pub struct HalfOutputSegVec<T> {
    pub start: Vec<T>,
    pub end: Vec<T>,
}

impl<T> Default for HalfOutputSegVec<T> {
    fn default() -> Self {
        Self {
            start: Vec::new(),
            end: Vec::new(),
        }
    }
}

impl<T> std::ops::Index<HalfOutputSegIdx> for HalfOutputSegVec<T> {
    type Output = T;

    fn index(&self, index: HalfOutputSegIdx) -> &Self::Output {
        if index.first_half {
            &self.start[index.idx.0]
        } else {
            &self.end[index.idx.0]
        }
    }
}

impl<T> std::ops::IndexMut<HalfOutputSegIdx> for HalfOutputSegVec<T> {
    fn index_mut(&mut self, index: HalfOutputSegIdx) -> &mut T {
        if index.first_half {
            &mut self.start[index.idx.0]
        } else {
            &mut self.end[index.idx.0]
        }
    }
}

#[derive(Clone, Debug, Hash, PartialEq, Eq, serde::Serialize)]
pub struct OutputSegVec<T> {
    inner: Vec<T>,
}

impl<T> Default for OutputSegVec<T> {
    fn default() -> Self {
        Self { inner: Vec::new() }
    }
}

impl<T> std::ops::Index<OutputSegIdx> for OutputSegVec<T> {
    type Output = T;

    fn index(&self, index: OutputSegIdx) -> &Self::Output {
        &self.inner[index.0]
    }
}

impl<T> std::ops::IndexMut<OutputSegIdx> for OutputSegVec<T> {
    fn index_mut(&mut self, index: OutputSegIdx) -> &mut T {
        &mut self.inner[index.0]
    }
}

#[derive(Clone, Copy, Hash, PartialEq, Eq, serde::Serialize)]
pub struct PointNeighbors {
    clockwise: HalfOutputSegIdx,
    counter_clockwise: HalfOutputSegIdx,
}

impl std::fmt::Debug for PointNeighbors {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?} o {:?}", self.counter_clockwise, self.clockwise)
    }
}

#[derive(Clone, Debug, serde::Serialize)]
pub struct Topology<F: Float> {
    /// Indexed by `SegIdx`.
    pub shape_a: Vec<bool>,
    /// Indexed by `SegIdx`.
    ///
    /// For each input segment, this is the list of output segments that we've started
    /// recording but haven't finished with. There can be up to three of them, because
    /// consider a segment that passes through a sweep-line like this:
    ///
    /// ```text
    ///           /
    ///          /
    /// (*) /---/
    ///    /
    ///   /
    /// ```
    ///
    /// When we come to process the sweep-line at height (*), we'll already have the
    /// unfinished output segment coming from above. But before dealing with it, we'll
    /// first encounter the output segment pointing down and add an unfinished segment
    /// for that. Then we'll add an output segment for the horizontal line and so
    /// at that point there will be three unfinished output segments.
    pub open_segs: Vec<VecDeque<OutputSegIdx>>,
    /// This is sort of logically indexed by `HalfOutputSegIdx`, because we can look at the
    /// `HalfSegmentWindingNumbers` for each `HalfOutputSegIdx`. But since the two halves of
    /// the winding numbers are determined by one another, we only store the winding numbers
    /// for the start half of the output segment.
    pub winding: OutputSegVec<HalfSegmentWindingNumbers>,
    pub point: HalfOutputSegVec<Point<F>>,
    pub point_neighbors: HalfOutputSegVec<PointNeighbors>,
    /// Marks the output segments that have been deleted due to merges of coindident segments.
    pub deleted: OutputSegVec<bool>,
    /// The map from a segment to its scan-left neighbor is always strictly decreasing (in the
    /// index). This ensures that a scan will always terminate, and it also means that we can
    /// build the contours in increasing `OutputSegIdx` order.
    pub scan_east: OutputSegVec<Option<OutputSegIdx>>,
}

impl<F: Float> Topology<F> {
    fn add_segs_clockwise(
        &mut self,
        first_seg: &mut Option<HalfOutputSegIdx>,
        last_seg: &mut Option<HalfOutputSegIdx>,
        segs: impl Iterator<Item = HalfOutputSegIdx>,
        p: &Point<F>,
    ) {
        for seg in segs {
            self.point[seg] = p.clone();
            if first_seg.is_none() {
                *first_seg = Some(seg);
            }
            if let Some(last) = last_seg {
                self.point_neighbors[*last].clockwise = seg;
                self.point_neighbors[seg].counter_clockwise = *last;
            }
            *last_seg = Some(seg);
        }
        if let Some((first, last)) = first_seg.zip(*last_seg) {
            self.point_neighbors[last].clockwise = first;
            self.point_neighbors[first].counter_clockwise = last;
        }
    }

    fn add_segs_counter_clockwise(
        &mut self,
        first_seg: &mut Option<HalfOutputSegIdx>,
        last_seg: &mut Option<HalfOutputSegIdx>,
        segs: impl Iterator<Item = HalfOutputSegIdx>,
        p: &Point<F>,
    ) {
        for seg in segs {
            self.point[seg] = p.clone();
            if last_seg.is_none() {
                *last_seg = Some(seg);
            }
            if let Some(first) = first_seg {
                self.point_neighbors[*first].counter_clockwise = seg;
                self.point_neighbors[seg].clockwise = *first;
            }
            *first_seg = Some(seg);
        }
        if let Some((first, last)) = first_seg.zip(*last_seg) {
            self.point_neighbors[last].clockwise = first;
            self.point_neighbors[first].counter_clockwise = last;
        }
    }

    fn second_half_segs<'a, 'slf: 'a>(
        &'slf mut self,
        segs: impl Iterator<Item = SegIdx> + 'a,
    ) -> impl Iterator<Item = HalfOutputSegIdx> + 'a {
        segs.map(|s| {
            self.open_segs[s.0]
                .pop_front()
                .expect("should be open")
                .second_half()
        })
    }

    fn new_half_seg(
        &mut self,
        idx: SegIdx,
        p: Point<F>,
        winding: HalfSegmentWindingNumbers,
        horizontal: bool,
    ) -> OutputSegIdx {
        let out_idx = OutputSegIdx(self.winding.inner.len());
        if horizontal {
            self.open_segs[idx.0].push_front(out_idx);
        } else {
            self.open_segs[idx.0].push_back(out_idx);
        }
        self.point.start.push(p);
        self.point
            .end
            // TODO: maybe an option instead of this weird sentinel
            .push(Point::new(F::from_f32(-42.0), F::from_f32(-42.0)));

        let no_nbrs = PointNeighbors {
            clockwise: out_idx.first_half(),
            counter_clockwise: out_idx.first_half(),
        };
        self.point_neighbors.start.push(no_nbrs);
        self.point_neighbors.end.push(no_nbrs);
        self.winding.inner.push(winding);
        self.deleted.inner.push(false);
        self.scan_east.inner.push(None);
        out_idx
    }

    pub fn from_segments(segments: &Segments<F>) -> Self {
        let mut ret = Self {
            shape_a: vec![false; segments.segs.len()],
            open_segs: vec![VecDeque::new(); segments.segs.len()],
            winding: OutputSegVec::default(),
            point: HalfOutputSegVec::default(),
            point_neighbors: HalfOutputSegVec::default(),
            deleted: OutputSegVec::default(),
            scan_east: OutputSegVec::default(),
        };

        // Mark the first contour as shape a.
        let start = SegIdx(0);
        ret.shape_a[0] = true;
        // FIXME: unwrap. This topology stuff only works with closed contours, but we should
        // have a more robust API.
        let mut idx = segments.contour_next[start.0].unwrap();
        while idx != start {
            ret.shape_a[idx.0] = true;
            idx = segments.contour_next[idx.0].unwrap();
        }
        ret
    }

    pub fn build(segments: &Segments<F>, eps: &F) -> Self {
        let mut ret = Self::from_segments(segments);
        let mut sweep_state = weak_ordering::State::new(segments, eps.clone());
        while let Some(line) = sweep_state.next_line() {
            for (start, end) in line.changed_intervals(segments, eps) {
                let positions = line.position_range((start, end), segments, eps);
                let scan_left_seg = if start == 0 {
                    None
                } else {
                    let prev_seg = line.old_line.segs[start - 1];
                    debug_assert!(!ret.open_segs[prev_seg.0].is_empty());
                    ret.open_segs[prev_seg.0].front().copied()
                };
                ret.update_from_positions(positions, segments, line, (start, end), scan_left_seg);
            }
        }
        ret.merge_coincident();
        ret
    }

    fn update_from_positions(
        &mut self,
        mut pos: PositionIter<F>,
        segments: &Segments<F>,
        lines: WeakSweepLinePair<'_, F>,
        range: (usize, usize),
        mut scan_left: Option<OutputSegIdx>,
    ) {
        let y = &lines.new_line.y;
        let mut winding = scan_left
            .map(|idx| self.winding[idx].counter_clockwise)
            .unwrap_or_default();
        let (old_order, new_order) = lines.range_orders(range);
        while let Some(next_x) = pos.next_x() {
            let p = Point::new(next_x.clone(), y.clone());
            // The first segment at our current point, in clockwise order.
            let mut first_seg = None;
            // The last segment at our current point, in clockwise order.
            let mut last_seg = None;

            // Close off the horizontal segments from the previous point in this sweep-line.
            let mut hsegs: Vec<_> = pos.active_horizontals.iter().map(|hseg| hseg.seg).collect();
            hsegs.sort_by_key(|s| new_order[s]);
            let hsegs: Vec<_> = self.second_half_segs(hsegs.into_iter()).collect();
            self.add_segs_clockwise(&mut first_seg, &mut last_seg, hsegs.into_iter(), &p);

            // Find all the segments that are connected to something above this sweep-line at next_x.
            // This is (a) all the horizontal segments terminating here, plus (b) the single-point
            // positions in our position iterator.
            let mut segments_connected_up: Vec<_> = pos
                .active_horizontals
                .iter()
                .filter(|hseg| hseg.connected_above_at(&next_x))
                .map(|hseg| hseg.seg)
                .collect();
            if let Some(positions) = pos.positions_at_current_x() {
                segments_connected_up.extend(
                    positions
                        .filter(|pos| pos.kind.connected_above_at(&next_x))
                        .map(|pos| pos.seg_idx),
                );
            }

            // Sorting the connected-up segments by the old sweep-line's order means that they'll
            // be in clockwise order when seen from the current point.
            segments_connected_up.sort_by_key(|s| old_order[s]);
            let open_segs: Vec<_> = self
                .second_half_segs(segments_connected_up.into_iter())
                .collect();

            self.add_segs_clockwise(&mut first_seg, &mut last_seg, open_segs.into_iter(), &p);

            // Then: gather the output segments from half-segments starting here and moving
            // to later sweep-lines. Sort them and allocate new output segments for them.
            // Also, calculate their winding numbers and update `winding`.
            let mut segments_connected_down: Vec<_> = pos
                .active_horizontals
                .iter()
                .filter(|hseg| hseg.connected_below_at(&next_x))
                .map(|hseg| hseg.seg)
                .collect();
            if let Some(positions) = pos.positions_at_current_x() {
                segments_connected_down.extend(
                    positions
                        .filter(|pos| pos.kind.connected_below_at(&next_x))
                        .map(|pos| pos.seg_idx),
                );
            }
            segments_connected_down.sort_by_key(|s| new_order[s]);
            let mut new_out_segs = Vec::new();
            for new_seg in segments_connected_down {
                let winding_dir = if segments.positively_oriented(new_seg) {
                    1
                } else {
                    -1
                };
                let prev_winding = winding;
                if self.shape_a[new_seg.0] {
                    winding.shape_a += winding_dir;
                } else {
                    winding.shape_b += winding_dir;
                }
                let windings = HalfSegmentWindingNumbers {
                    clockwise: prev_winding,
                    counter_clockwise: winding,
                };
                let half_seg = self.new_half_seg(new_seg, p.clone(), windings, false);
                self.scan_east[half_seg] = scan_left;
                scan_left = Some(half_seg);
                new_out_segs.push(half_seg);
            }
            self.add_segs_counter_clockwise(
                &mut first_seg,
                &mut last_seg,
                new_out_segs.into_iter().map(|s| s.first_half()),
                &p,
            );

            // Update the active horizontal segments, getting rid of ones ending here and
            // inserting new ones.
            pos.drain_active_horizontals(&next_x);
            while let Some(p) = pos.positions.as_slice().first() {
                if p.kind.smaller_x() > &next_x {
                    break;
                }
                // unwrap: we just peeked at this element.
                let p = pos.positions.next().unwrap();

                if let Some(hseg) = HSeg::from_position(p) {
                    // For horizontal segments, we don't output anything straight
                    // away. When we update the horizontal position and visit our
                    // horizontal segments, we'll output something.
                    pos.active_horizontals.insert(hseg);
                }
            }

            // Finally, gather the output segments from horizontal segments starting here.
            // Allocate new output segments for them and calculate their winding numbers.
            let mut hsegs: Vec<_> = pos.active_horizontals.iter().map(|hseg| hseg.seg).collect();
            hsegs.sort_by_key(|s| new_order[s]);

            // We don't want to update our "global" winding number state because that's supposed
            // to keep track of the winding number below the current sweep line.
            let mut w = winding;
            let mut new_out_segs = Vec::new();
            for new_seg in hsegs {
                let winding_dir = if segments.positively_oriented(new_seg) {
                    1
                } else {
                    -1
                };
                let prev_w = w;
                if self.shape_a[new_seg.0] {
                    w.shape_a += winding_dir;
                } else {
                    w.shape_b += winding_dir;
                }
                let windings = HalfSegmentWindingNumbers {
                    counter_clockwise: w,
                    clockwise: prev_w,
                };
                let half_seg = self.new_half_seg(new_seg, p.clone(), windings, true);
                self.scan_east[half_seg] = scan_left;
                new_out_segs.push(half_seg);
            }
            self.add_segs_counter_clockwise(
                &mut first_seg,
                &mut last_seg,
                new_out_segs.into_iter().map(|s| s.first_half()),
                &p,
            );
        }
    }

    fn delete_half(&mut self, half_seg: HalfOutputSegIdx) {
        let nbr = self.point_neighbors[half_seg];
        self.point_neighbors[nbr.clockwise].counter_clockwise = nbr.counter_clockwise;
        self.point_neighbors[nbr.counter_clockwise].clockwise = nbr.clockwise;
    }

    fn delete(&mut self, seg: OutputSegIdx) {
        self.deleted[seg] = true;
        self.delete_half(seg.first_half());
        self.delete_half(seg.second_half());
    }

    /// After generating the topology, there's a good chance we end up with
    /// coincident output segments. This method removes coincident segments. If
    /// a collection of coincident segments has a net winding number of zero,
    /// this method just removes them all. Otherwise, they are replaced by a
    /// single segment.
    ///
    /// In principle, we could do this as we build the topology. The thing that
    /// makes it a little bit tricky is that (except for horizontal segments)
    /// we don't know whether two segments are coincident until we've processed
    /// their second endpoint.
    fn merge_coincident(&mut self) {
        for idx in 0..self.winding.inner.len() {
            let idx = OutputSegIdx(idx);
            if self.deleted[idx] {
                continue;
            }
            let cc_nbr = self.point_neighbors[idx.first_half()].clockwise;
            if self.point[idx.second_half()] == self.point[cc_nbr.other_half()] {
                // All output segments are in sweep line order, so if they're
                // coincident then they'd better both be first halves.
                debug_assert!(cc_nbr.first_half);
                self.delete(idx);
                self.winding[cc_nbr.idx].counter_clockwise = self.winding[idx].counter_clockwise;

                if self.winding[cc_nbr.idx].is_trivial() {
                    self.delete(cc_nbr.idx);
                }
            }
        }
    }

    pub fn segment_indices(&self) -> impl Iterator<Item = OutputSegIdx> + '_ {
        (0..self.winding.inner.len())
            .map(OutputSegIdx)
            .filter(|i| !self.deleted[*i])
    }

    pub fn winding(&self, idx: HalfOutputSegIdx) -> HalfSegmentWindingNumbers {
        if idx.first_half {
            self.winding[idx.idx]
        } else {
            self.winding[idx.idx].flipped()
        }
    }

    // We walk contours in sweep-line order of their smallest point. This mostly ensures
    // that we visit outer contours before we visit their children. However, when the inner
    // and outer contours share a point, we run into a problem. For example:
    //
    // /------------------\
    // |        /\        |
    // |       /  \       |
    // \       \  /      /
    //  \       \/      /
    //   \             /
    //    -------------
    // (where the top-middle point is supposed to have 4 segments coming out of it; it's
    // a hard to draw it in ASCII). In this case, we'll "notice" the inner contour when
    // we realize that we've visited a point twice. At that point, we extract the inner part
    // into a separate contour and mark it as a child of the outer one. This requires some
    // slightly sketch indexing, because we need to refer to the outer contour even though
    // we haven't finished generating it. We solve this by reserving a slot for the unfinished
    // outer contour as soon as we start walking it.
    pub fn contours(&self, inside: impl Fn(WindingNumber) -> bool) -> Contours<F> {
        let mut ret = Contours::default();
        let mut seg_contour: Vec<Option<ContourIdx>> = vec![None; self.winding.inner.len()];

        let bdy = |idx: OutputSegIdx| -> bool {
            inside(self.winding[idx].clockwise) != inside(self.winding[idx].counter_clockwise)
        };

        let mut visited = vec![false; self.winding.inner.len()];
        for idx in self.segment_indices() {
            if visited[idx.0] {
                continue;
            }

            if !bdy(idx) {
                continue;
            }

            // Keep track of the points that were visited on this walk, so that if we re-visit a
            // point we can split out an additional contour. This might be more efficient if we
            // index our points instead of storing them physically.
            let mut last_visit: HashMap<Point<F>, usize> = HashMap::new();

            // We found a boundary segment. Let's start by scanning left to figure out where we
            // are relative to existing contours.
            let contour_idx = ContourIdx(ret.contours.len());
            let mut contour = Contour::default();
            let mut east_seg = self.scan_east[idx];
            while let Some(left) = east_seg {
                if self.deleted[left] || !bdy(left) {
                    east_seg = self.scan_east[left];
                } else {
                    break;
                }
            }
            if let Some(east) = east_seg {
                if let Some(east_contour) = seg_contour[east.0] {
                    // Is the thing just to our left inside or outside the output set?
                    let outside = !inside(self.winding(east.first_half()).counter_clockwise);
                    if outside == ret.contours[east_contour.0].outer {
                        // They're an outer contour, and there's exterior between us and them,
                        // or they're an inner contour and there's interior between us.
                        // That means they're our sibling.
                        contour.parent = ret.contours[east_contour.0].parent;
                        contour.outer = outside;
                        debug_assert!(outside || contour.parent.is_some());
                    } else {
                        contour.parent = Some(east_contour);
                        contour.outer = !ret.contours[east_contour.0].outer;
                    }
                } else {
                    panic!("I'm {idx:?}, east is {east:?}. Y u no have contour?");
                }
            };
            // Reserve a space for the unfinished outer contour, as described above.
            ret.contours.push(contour);

            // First, arrange the orientation so that the interior is on our
            // left as we walk.
            let (start, mut next) = if inside(self.winding[idx].counter_clockwise) {
                (idx.first_half(), idx.second_half())
            } else {
                (idx.second_half(), idx.first_half())
            };
            let mut segs = Vec::new();
            last_visit.insert(self.point[start].clone(), 0);

            debug_assert!(inside(self.winding(start).counter_clockwise));
            loop {
                visited[next.idx.0] = true;

                debug_assert!(inside(self.winding(next).clockwise));
                debug_assert!(!inside(self.winding(next).counter_clockwise));

                segs.push(next);

                // Walk clockwise around the point until we find the next segment
                // that's on the boundary.
                let mut nbr = self.point_neighbors[next].clockwise;
                debug_assert!(inside(self.winding(nbr).counter_clockwise));
                while inside(self.winding(nbr).clockwise) {
                    nbr = self.point_neighbors[nbr].clockwise;
                }

                if nbr == start {
                    break;
                }

                let p = self.point[nbr].clone();
                if let Some(seg_idx) = last_visit.get(&p) {
                    // We repeated a point, meaning that we've found an inner contour. Extract
                    // it and remove it from the current contour.

                    // seg_idx should point to the end of a segment whose start is at p.
                    debug_assert_eq!(self.point[segs[*seg_idx].other_half()], p);

                    let loop_contour_idx = ContourIdx(ret.contours.len());
                    for &seg in &segs[*seg_idx..] {
                        seg_contour[seg.idx.0] = Some(loop_contour_idx);
                    }
                    let mut points = Vec::with_capacity(segs.len() - seg_idx + 1);
                    points.push(p);
                    points.extend(segs[*seg_idx..].iter().map(|s| self.point[*s].clone()));
                    ret.contours.push(Contour {
                        points,
                        parent: Some(contour_idx),
                        outer: !ret.contours[contour_idx.0].outer,
                    });
                    segs.truncate(*seg_idx);
                    // In principle, we should also be unsetting `last_visit`
                    // for all points in the contour we just removed. I *think*
                    // we don't need to, because it's impossible for the outer
                    // contour to visit any of them anyway. Should check this
                    // more carefully.
                } else {
                    last_visit.insert(p, segs.len());
                }

                next = nbr.other_half();
            }
            let mut points = Vec::with_capacity(segs.len() + 1);
            points.push(self.point[start].clone());
            points.extend(segs.iter().map(|s| self.point[*s].clone()));
            for &seg in &segs {
                seg_contour[seg.idx.0] = Some(contour_idx);
            }
            ret.contours[contour_idx.0].points = points;
        }

        ret
    }
}

#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq, serde::Serialize)]
pub struct ContourIdx(pub usize);

#[derive(Clone, Debug, serde::Serialize)]
pub struct Contour<F: Float> {
    pub points: Vec<Point<F>>,
    pub outer: bool,
    pub parent: Option<ContourIdx>,
}

impl<F: Float> Default for Contour<F> {
    fn default() -> Self {
        Self {
            points: Vec::default(),
            outer: true,
            parent: None,
        }
    }
}

#[derive(Clone, Debug, serde::Serialize)]
pub struct Contours<F: Float> {
    pub contours: Vec<Contour<F>>,
}

impl<F: Float> Contours<F> {
    pub fn grouped(&self) -> Vec<Vec<ContourIdx>> {
        let mut children = vec![Vec::new(); self.contours.len()];
        let mut top_level = Vec::new();
        for i in 0..self.contours.len() {
            if let Some(parent) = self.contours[i].parent {
                children[parent.0].push(ContourIdx(i));
            } else {
                top_level.push(ContourIdx(i));
            }
        }

        let mut ret = Vec::with_capacity(top_level.len());
        for top in top_level {
            let mut tree = Vec::new();
            fn visit(idx: ContourIdx, children: &[Vec<ContourIdx>], acc: &mut Vec<ContourIdx>) {
                acc.push(idx);
                for &child in &children[idx.0] {
                    visit(child, children, acc);
                }
            }
            visit(top, &children, &mut tree);
            ret.push(tree);
        }

        ret
    }
}

impl<F: Float> std::ops::Index<ContourIdx> for Contours<F> {
    type Output = Contour<F>;

    fn index(&self, index: ContourIdx) -> &Self::Output {
        &self.contours[index.0]
    }
}

impl<F: Float> Default for Contours<F> {
    fn default() -> Self {
        Contours {
            contours: Vec::default(),
        }
    }
}

#[cfg(test)]
mod tests {
    use ordered_float::NotNan;

    use crate::{geom::Point, segments::Segments};

    use super::Topology;

    fn p(x: f64, y: f64) -> Point<NotNan<f64>> {
        Point::new(x.try_into().unwrap(), y.try_into().unwrap())
    }

    #[test]
    fn square() {
        let segs =
            Segments::from_closed_cycle([p(0.0, 0.0), p(1.0, 0.0), p(1.0, 1.0), p(0.0, 1.0)]);
        let eps = NotNan::try_from(0.01).unwrap();
        let top = Topology::build(&segs, &eps);

        insta::assert_ron_snapshot!(top);
    }

    #[test]
    fn diamond() {
        let segs =
            Segments::from_closed_cycle([p(0.0, 0.0), p(1.0, 1.0), p(0.0, 2.0), p(-1.0, 1.0)]);
        let eps = NotNan::try_from(0.01).unwrap();
        let top = Topology::build(&segs, &eps);

        insta::assert_ron_snapshot!(top);
    }

    #[test]
    fn square_and_diamond() {
        let mut segs =
            Segments::from_closed_cycle([p(0.0, 0.0), p(1.0, 0.0), p(1.0, 1.0), p(0.0, 1.0)]);
        segs.add_points([p(0.0, 0.0), p(1.0, 1.0), p(0.0, 2.0), p(-1.0, 1.0)], true);
        let eps = NotNan::try_from(0.01).unwrap();
        let top = Topology::build(&segs, &eps);

        insta::assert_ron_snapshot!(top);
    }

    #[test]
    fn square_with_double_back() {
        let segs = Segments::from_closed_cycle([
            p(0.0, 0.0),
            p(0.5, 0.0),
            p(0.5, 0.5),
            p(0.5, 0.0),
            p(1.0, 0.0),
            p(1.0, 1.0),
            p(0.0, 1.0),
        ]);
        let eps = NotNan::try_from(0.01).unwrap();
        let top = Topology::build(&segs, &eps);

        insta::assert_ron_snapshot!(top);
    }

    #[test]
    fn nested_squares() {
        let mut segs =
            Segments::from_closed_cycle([p(-2.0, -2.0), p(2.0, -2.0), p(2.0, 2.0), p(-2.0, 2.0)]);
        segs.add_points(
            [p(-1.0, -1.0), p(1.0, -1.0), p(1.0, 1.0), p(-1.0, 1.0)],
            true,
        );
        let eps = NotNan::try_from(0.01).unwrap();
        let top = Topology::build(&segs, &eps);
        let contours = top.contours(|w| (w.shape_a + w.shape_b) % 2 != 0);

        insta::assert_ron_snapshot!((top, contours));
    }

    #[test]
    fn inner_loop() {
        let mut segs =
            Segments::from_closed_cycle([p(-2.0, -2.0), p(2.0, -2.0), p(2.0, 2.0), p(-2.0, 2.0)]);
        segs.add_points([p(-1.5, -1.0), p(0.0, 2.0), p(1.5, -1.0)], true);
        segs.add_points([p(-0.1, 0.0), p(0.0, 2.0), p(0.1, 0.0)], true);
        let eps = NotNan::try_from(0.01).unwrap();
        let top = Topology::build(&segs, &eps);
        let contours = top.contours(|w| (w.shape_a + w.shape_b) % 2 != 0);

        insta::assert_ron_snapshot!((top, contours));
    }
}
