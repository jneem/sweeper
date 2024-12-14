use crate::{
    algorithms::weak::{HSeg, PositionIter, WeakSweepLinePair},
    geom::Point,
    num::Float,
    sweep::{SegIdx, Segments},
};

/// We support boolean operations, so a "winding number" for is is two winding
/// numbers, one for each shape.
#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
pub struct WindingNumber {
    shape_a: i32,
    shape_b: i32,
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

#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
pub struct HalfOutputSegIdx {
    idx: OutputSegIdx,
    first_half: bool,
}

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct OutputSegVec<T> {
    pub start: Vec<T>,
    pub end: Vec<T>,
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

#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
pub struct PointNeighbors {
    clockwise: HalfOutputSegIdx,
    counter_clockwise: HalfOutputSegIdx,
}

pub struct Topology<F: Float> {
    /// Indexed by `SegIdx`.
    pub shape_a: Vec<bool>,
    /// Indexed by `SegIdx`.
    pub open_segs: Vec<Option<OutputSegIdx>>,
    /// Indexed by `OutputSegIdx`
    pub winding: Vec<WindingNumber>,
    pub point: OutputSegVec<Point<F>>,
    pub point_neighbors: OutputSegVec<PointNeighbors>,
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
                self.point_neighbors[*first].clockwise = seg;
                self.point_neighbors[seg].counter_clockwise = *first;
            }
            *last_seg = Some(seg);
        }
    }

    fn second_half_segs<'a, 'slf: 'a>(
        &'slf mut self,
        segs: impl Iterator<Item = SegIdx> + 'a,
    ) -> impl Iterator<Item = HalfOutputSegIdx> + 'a {
        segs.map(|s| {
            self.open_segs[s.0]
                .take()
                .expect("should be open")
                .second_half()
        })
    }

    fn new_half_seg(&mut self, idx: SegIdx, p: Point<F>, winding: WindingNumber) -> OutputSegIdx {
        let out_idx = OutputSegIdx(self.winding.len());
        self.open_segs[idx.0] = Some(out_idx);
        self.point[out_idx.first_half()] = p;
        self.winding.push(winding);
        out_idx
    }

    pub fn update_from_positions(
        &mut self,
        mut pos: PositionIter<F>,
        y: &F,
        segments: &Segments<F>,
        lines: &WeakSweepLinePair<F>,
        range: (usize, usize),
        init: WindingNumber,
    ) {
        let mut winding = init;
        let (old_order, new_order) = lines.range_orders(range);
        while let Some(next_x) = pos.next_x() {
            let p = Point::new(next_x.clone(), y.clone());
            let mut first_seg = None;
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
                if self.shape_a[new_seg.0] {
                    winding.shape_a += winding_dir;
                } else {
                    winding.shape_b += winding_dir;
                }
                new_out_segs.push(self.new_half_seg(new_seg, p.clone(), winding));
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
                if self.shape_a[new_seg.0] {
                    w.shape_a += winding_dir;
                } else {
                    w.shape_b += winding_dir;
                }
                new_out_segs.push(self.new_half_seg(new_seg, p.clone(), w));
            }
            self.add_segs_counter_clockwise(
                &mut first_seg,
                &mut last_seg,
                new_out_segs.into_iter().map(|s| s.first_half()),
                &p,
            );
        }
    }
}
