use std::collections::VecDeque;

use crate::{
    algorithms::weak::{HSeg, PositionIter, WeakSweepLinePair},
    geom::Point,
    num::Float,
    sweep::{SegIdx, Segments},
};

/// We support boolean operations, so a "winding number" for is is two winding
/// numbers, one for each shape.
#[derive(Clone, Copy, Hash, PartialEq, Eq, Default)]
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
#[derive(Clone, Copy, Hash, PartialEq, Eq, Default)]
pub struct SegmentWindingNumbers {
    pub counter_clockwise: WindingNumber,
    pub clockwise: WindingNumber,
}

impl SegmentWindingNumbers {
    fn is_trivial(&self) -> bool {
        self.counter_clockwise == self.clockwise
    }

    fn flipped(self) -> Self {
        Self {
            counter_clockwise: self.clockwise,
            clockwise: self.counter_clockwise,
        }
    }
}

impl std::fmt::Debug for SegmentWindingNumbers {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?} | {:?}", self.clockwise, self.counter_clockwise)
    }
}

#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
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

#[derive(Clone, Copy, Hash, PartialEq, Eq)]
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

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct OutputSegVec<T> {
    pub start: Vec<T>,
    pub end: Vec<T>,
}

impl<T> Default for OutputSegVec<T> {
    fn default() -> Self {
        Self {
            start: Vec::new(),
            end: Vec::new(),
        }
    }
}

impl<T> std::ops::Index<HalfOutputSegIdx> for OutputSegVec<T> {
    type Output = T;

    fn index(&self, index: HalfOutputSegIdx) -> &Self::Output {
        if index.first_half {
            &self.start[index.idx.0]
        } else {
            &self.end[index.idx.0]
        }
    }
}

impl<T> std::ops::IndexMut<HalfOutputSegIdx> for OutputSegVec<T> {
    fn index_mut(&mut self, index: HalfOutputSegIdx) -> &mut T {
        if index.first_half {
            &mut self.start[index.idx.0]
        } else {
            &mut self.end[index.idx.0]
        }
    }
}

#[derive(Clone, Copy, Hash, PartialEq, Eq)]
pub struct PointNeighbors {
    clockwise: HalfOutputSegIdx,
    counter_clockwise: HalfOutputSegIdx,
}

impl std::fmt::Debug for PointNeighbors {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?} o {:?}", self.counter_clockwise, self.clockwise)
    }
}

#[derive(Clone, Debug)]
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
    /// Indexed by `OutputSegIdx`
    pub winding: Vec<SegmentWindingNumbers>,
    pub point: OutputSegVec<Point<F>>,
    pub point_neighbors: OutputSegVec<PointNeighbors>,
    pub deleted: Vec<bool>,
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
        winding: SegmentWindingNumbers,
        horizontal: bool,
    ) -> OutputSegIdx {
        let out_idx = OutputSegIdx(self.winding.len());
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
        self.winding.push(winding);
        self.deleted.push(false);
        out_idx
    }

    pub fn from_segments(segments: &Segments<F>) -> Self {
        let mut ret = Self {
            shape_a: vec![false; segments.segs.len()],
            open_segs: vec![VecDeque::new(); segments.segs.len()],
            winding: Vec::new(),
            point: OutputSegVec::default(),
            point_neighbors: OutputSegVec::default(),
            deleted: Vec::new(),
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

    pub fn build(weaks: &[WeakSweepLinePair<F>], segments: &Segments<F>, eps: &F) -> Self {
        let mut ret = Self::from_segments(segments);
        for line in weaks {
            for (start, end) in line.changed_intervals(segments, eps) {
                let positions = line.position_range((start, end), segments, eps);
                let winding = if start == 0 {
                    WindingNumber::default()
                } else {
                    let prev_seg = line.old_line.segs[start - 1];
                    let last_output = ret.open_segs[prev_seg.0].front().expect("no open seg");
                    ret.winding[last_output.0].counter_clockwise
                };
                ret.update_from_positions(positions, segments, line, (start, end), winding);
            }
        }
        ret.merge_coincident();
        ret
    }

    fn update_from_positions(
        &mut self,
        mut pos: PositionIter<F>,
        segments: &Segments<F>,
        lines: &WeakSweepLinePair<F>,
        range: (usize, usize),
        init: WindingNumber,
    ) {
        let y = &lines.new_line.y;
        let mut winding = init;
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
                let windings = SegmentWindingNumbers {
                    clockwise: prev_winding,
                    counter_clockwise: winding,
                };
                new_out_segs.push(self.new_half_seg(new_seg, p.clone(), windings, false));
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
                let windings = SegmentWindingNumbers {
                    counter_clockwise: w,
                    clockwise: prev_w,
                };
                new_out_segs.push(self.new_half_seg(new_seg, p.clone(), windings, true));
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
        self.deleted[seg.0] = true;
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
        for idx in 0..self.winding.len() {
            if self.deleted[idx] {
                continue;
            }
            let idx = OutputSegIdx(idx);
            let cc_nbr = self.point_neighbors[idx.first_half()].clockwise;
            if self.point[idx.second_half()] == self.point[cc_nbr.other_half()] {
                // All output segments are in sweep line order, so if they're
                // coincident then they'd better both be first halves.
                debug_assert!(cc_nbr.first_half);
                self.delete(idx);
                self.winding[cc_nbr.idx.0].counter_clockwise =
                    self.winding[idx.0].counter_clockwise;

                if self.winding[cc_nbr.idx.0].is_trivial() {
                    self.delete(cc_nbr.idx);
                }
            }
        }
    }

    pub fn segment_indices(&self) -> impl Iterator<Item = OutputSegIdx> + '_ {
        (0..self.winding.len())
            .filter(|i| !self.deleted[*i])
            .map(OutputSegIdx)
    }

    pub fn winding(&self, idx: HalfOutputSegIdx) -> SegmentWindingNumbers {
        if idx.first_half {
            self.winding[idx.idx.0]
        } else {
            self.winding[idx.idx.0].flipped()
        }
    }

    pub fn contours(&self, inside: impl Fn(WindingNumber) -> bool) -> Vec<Vec<Point<F>>> {
        let bdy = |idx: OutputSegIdx| -> bool {
            inside(self.winding[idx.0].clockwise) != inside(self.winding[idx.0].counter_clockwise)
        };

        let mut visited = vec![false; self.winding.len()];
        let mut contours = Vec::new();
        for idx in self.segment_indices() {
            if visited[idx.0] {
                continue;
            }

            if !bdy(idx) {
                continue;
            }

            // We have a boundary segment; let's traverse its contour.
            let mut contour = Vec::new();
            // First, arrange the orientation so that the interior is on our
            // left as we walk.
            let (start, mut next) = if inside(self.winding[idx.0].counter_clockwise) {
                (idx.first_half(), idx.second_half())
            } else {
                (idx.second_half(), idx.first_half())
            };
            contour.push(self.point[start].clone());

            debug_assert!(inside(self.winding(start).counter_clockwise));
            dbg!(start, &self.point[start]);
            loop {
                visited[next.idx.0] = true;

                dbg!(next, &self.point[next]);
                debug_assert!(inside(self.winding(next).clockwise));
                debug_assert!(!inside(self.winding(next).counter_clockwise));

                contour.push(self.point[next].clone());

                // Walk clockwise around the point until we find the next segment
                // that's on the boundary.
                let mut nbr = self.point_neighbors[next].clockwise;
                //dbg!(self.winding(next), self.winding(nbr));
                debug_assert!(inside(self.winding(nbr).counter_clockwise));
                while inside(self.winding(nbr).clockwise) {
                    nbr = self.point_neighbors[nbr].clockwise;
                }

                if nbr == start {
                    break;
                }
                next = nbr.other_half();
            }
            contour.push(self.point[next].clone());
            contours.push(contour);
        }

        contours
    }
}

#[cfg(test)]
mod tests {
    use ordered_float::NotNan;

    use crate::{algorithms::weak::sweep, geom::Point, sweep::Segments};

    use super::Topology;

    fn p(x: f64, y: f64) -> Point<NotNan<f64>> {
        Point::new(x.try_into().unwrap(), y.try_into().unwrap())
    }

    // TODO: make these snapshot tests
    #[test]
    fn square() {
        let segs =
            Segments::from_closed_cycle([p(0.0, 0.0), p(1.0, 0.0), p(1.0, 1.0), p(0.0, 1.0)]);
        let eps = NotNan::try_from(0.01).unwrap();
        let weaks = sweep(&segs, &eps);
        let top = Topology::build(&weaks, &segs, &eps);
        dbg!(top);
    }

    #[test]
    fn diamond() {
        let segs =
            Segments::from_closed_cycle([p(0.0, 0.0), p(1.0, 1.0), p(0.0, 2.0), p(-1.0, 1.0)]);
        let eps = NotNan::try_from(0.01).unwrap();
        let weaks = sweep(&segs, &eps);
        let top = Topology::build(&weaks, &segs, &eps);
        dbg!(top);
    }

    #[test]
    fn square_and_diamond() {
        let mut segs =
            Segments::from_closed_cycle([p(0.0, 0.0), p(1.0, 0.0), p(1.0, 1.0), p(0.0, 1.0)]);
        segs.add_points([p(0.0, 0.0), p(1.0, 1.0), p(0.0, 2.0), p(-1.0, 1.0)], true);
        let eps = NotNan::try_from(0.01).unwrap();
        let weaks = sweep(&segs, &eps);
        let top = Topology::build(&weaks, &segs, &eps);
        dbg!(top);
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
        let weaks = sweep(&segs, &eps);
        let top = Topology::build(&weaks, &segs, &eps);
        dbg!(top);
    }
}
