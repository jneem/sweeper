use std::collections::BTreeMap;

/// A data-structure for efficiently (well, at least in the asymptotic sense) incrementally
/// copying out a disjoint collection of subranges of an indexed collection.
pub struct Subranges<T> {
    /// A collection of intervals of ranges.
    /// The ranges are guaranteed to be disjoint. We only store the start index of each range;
    /// the end index can be inferred by the length of the data.
    ///
    /// The values in this map are copies of the values indexed by the interval. (TODO: make
    /// this understandable)
    intervals: BTreeMap<usize, Vec<T>>,
}

impl<T> Default for Subranges<T> {
    fn default() -> Self {
        Self {
            intervals: BTreeMap::default(),
        }
    }
}

impl<T: Clone> Subranges<T> {
    /// If there's an interval containing the given index, returns its starting index.
    fn interval_containing(&self, idx: usize) -> Option<usize> {
        self.intervals
            .range(..=idx)
            .next_back()
            .and_then(|(start_idx, data)| {
                if *start_idx + data.len() > idx {
                    Some(*start_idx)
                } else {
                    None
                }
            })
    }

    /// Adds a range to this collection of ranges, possibly merging with existing ranges if there's overlap.
    ///
    /// We'd like this to be more-or-less linear in the number of new elements in `data` (i.e.
    /// the number that aren't in an existing range). We don't currently achieve this; I think
    /// it would require the values in Subranges::interval to be a linked list instead of a vector.
    ///
    /// Also, for this to be efficient `data` needs to have a fast `nth` function, to skip
    /// existing ranges.
    pub fn add_range(&mut self, range: std::ops::Range<usize>, mut data: impl Iterator<Item = T>) {
        // If we have something overlapping with the beginning of `range`, put that on the output first.
        let (start_pos, mut interval, mut pos) =
            if let Some(before_idx) = self.interval_containing(range.start) {
                let interval = self.intervals.remove(&before_idx).unwrap();
                let interval_end = before_idx + interval.len();
                assert!(range.start < interval_end);

                // Drop from `data` everything that overlaps with `interval`
                data.nth(interval_end - range.start - 1);
                (before_idx, interval, interval_end)
            } else {
                (range.start, Vec::new(), range.start)
            };

        // There doesn't seem to be a fast way to remove a range from a BTreeMap, so collect
        // the indices and remove them one-by-one.
        let existing_ranges: Vec<_> = self
            .intervals
            .range(pos..range.end)
            .map(|(k, _v)| *k)
            .collect();

        for next_idx in existing_ranges {
            let next_vec = self.intervals.remove(&next_idx).unwrap();
            let next_vec_len = next_vec.len();
            if pos < next_idx {
                interval.extend((&mut data).take(next_idx - pos));
            }
            interval.extend(next_vec.into_iter());
            if next_vec_len > 0 {
                data.nth(next_vec_len - 1);
            }
            pos = next_idx + next_vec_len;
        }
        interval.extend(data);

        self.intervals.insert(start_pos, interval);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn run_test(ranges_in: &[std::ops::Range<usize>], ranges_out: &[std::ops::Range<usize>]) {
        let mut subs = Subranges::default();
        for r in ranges_in {
            subs.add_range(r.clone(), r.clone());
        }

        for (idx, iv) in &subs.intervals {
            let expected = ((*idx)..(*idx + iv.len())).collect::<Vec<_>>();
            assert_eq!(&expected, iv);
        }

        let actual_out = subs
            .intervals
            .iter()
            .map(|(idx, iv)| (*idx)..(*idx + iv.len()))
            .collect::<Vec<_>>();
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
    }

    #[test]
    fn overlapping_multiple() {
        #![allow(clippy::single_range_in_vec_init)]
        run_test(&[1..3, 8..13, 2..9], &[1..13]);
        run_test(&[1..3, 8..13, 2..15], &[1..15]);
    }
}
