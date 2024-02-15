use std::collections::HashSet;

/// A quick (to write, not to execute) and hacky algorithm for resolving equivalence relations.
#[derive(Default)]
pub struct Equiv<T> {
    sets: Vec<HashSet<T>>,
}

impl<T: std::hash::Hash + Eq> Equiv<T> {
    fn find_set(&self, s: &T) -> Option<usize> {
        self.sets.iter().position(|set| set.contains(s))
    }

    pub fn add_equivalence(&mut self, s: T, t: T) {
        match (self.find_set(&s), self.find_set(&t)) {
            (None, None) => self.sets.push([s, t].into_iter().collect()),
            (None, Some(i)) => {
                self.sets[i].insert(s);
            }
            (Some(i), None) => {
                self.sets[i].insert(t);
            }
            (Some(i), Some(j)) if i != j => {
                let j_set = std::mem::take(&mut self.sets[j]);
                self.sets[i].extend(j_set);
                self.sets.remove(j);
            }
            (Some(i), Some(j)) => {
                assert_eq!(i, j);
            }
        }
    }

    pub fn equivalences(&self) -> impl Iterator<Item = &HashSet<T>> {
        self.sets.iter()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn equivs(pairs: impl IntoIterator<Item = (u64, u64)>) -> Vec<Vec<u64>> {
        let mut equiv = Equiv::default();
        for (s, t) in pairs {
            equiv.add_equivalence(s, t);
        }
        let mut equivs: Vec<_> = equiv
            .equivalences()
            .map(|set| {
                let mut vec: Vec<_> = set.iter().copied().collect();
                vec.sort();
                vec
            })
            .collect();
        equivs.sort();
        equivs
    }

    #[test]
    fn test_equivs() {
        assert_eq!(equivs([(1, 2), (3, 4)]), vec![vec![1, 2], vec![3, 4]]);
        assert_eq!(equivs([(1, 2), (3, 4), (1, 3)]), vec![vec![1, 2, 3, 4]]);
        assert_eq!(equivs([(1, 2), (1, 3), (3, 4)]), vec![vec![1, 2, 3, 4]]);
    }
}
