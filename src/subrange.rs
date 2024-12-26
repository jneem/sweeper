use std::collections::BTreeMap;

/// A data-structure for efficiently (well, at least in the asymptotic sense) incrementally
/// copying out a disjoint collection of subranges of an indexed collection.
#[derive(Default)]
pub struct Subranges {
    /// A collection of intervals of ranges.
    /// The ranges are guaranteed to be disjoint.
    intervals: BTreeMap<usize, usize>,
}

impl Subranges {
    /// If there's an interval containing the given index, returns its starting index.
    fn interval_containing(&self, idx: usize) -> Option<usize> {
        self.intervals
            .range(..=idx)
            .next_back()
            .and_then(|(start_idx, end_idx)| {
                if *end_idx > idx {
                    Some(*start_idx)
                } else {
                    None
                }
            })
    }

    /// Adds a range to this collection of ranges, possibly merging with existing ranges if there's overlap.
    pub fn add_range(&mut self, range: std::ops::Range<usize>) {
        // If we have something overlapping with the beginning of `range`, put that on the output first.
        let (start_pos, mut pos) = if let Some(before_idx) = self.interval_containing(range.start) {
            let interval_end = self.intervals.remove(&before_idx).unwrap();
            assert!(range.start < interval_end);

            (before_idx, interval_end)
        } else {
            (range.start, range.start)
        };

        // There doesn't seem to be a fast way to remove a range from a BTreeMap, so collect
        // the indices and remove them one-by-one.
        let overlapping_ranges: Vec<_> = self
            .intervals
            .range(pos..range.end.max(pos))
            .map(|(k, v)| (*k, *v))
            .collect();

        for (start, end) in overlapping_ranges {
            self.intervals.remove(&start);
            pos = pos.max(end);
        }
        self.intervals.insert(start_pos, pos.max(range.end));
    }

    pub fn ranges(&self) -> impl Iterator<Item = std::ops::Range<usize>> + '_ {
        self.intervals.iter().map(|(k, v)| (*k)..(*v))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn run_test(ranges_in: &[std::ops::Range<usize>], ranges_out: &[std::ops::Range<usize>]) {
        let mut subs = Subranges::default();
        for r in ranges_in {
            subs.add_range(r.clone());
        }

        let actual_out = subs.ranges().collect::<Vec<_>>();
        assert_eq!(ranges_out, actual_out);
    }

    #[test]
    fn disjoint() {
        run_test(&[1..3, 8..13, 4..6], &[1..3, 4..6, 8..13]);
        run_test(&[1..3, 8..13, 3..6], &[1..3, 3..6, 8..13]);
    }

    #[test]
    fn overlapping_a_little() {
        run_test(&[1..3, 8..13, 2..4], &[1..4, 8..13]);
        run_test(&[8..13, 2..4, 1..3], &[1..4, 8..13]);
        run_test(&[2..4, 1..3, 8..13], &[1..4, 8..13]);

        run_test(&[10..12, 8..13, 2..4], &[2..4, 8..13]);
        run_test(&[8..13, 2..4, 10..12], &[2..4, 8..13]);
    }

    #[test]
    fn overlapping_multiple() {
        #![allow(clippy::single_range_in_vec_init)]
        run_test(&[1..3, 8..13, 2..9], &[1..13]);
        run_test(&[1..3, 8..13, 2..15], &[1..15]);
    }
}
