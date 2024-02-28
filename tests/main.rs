use arbitrary::Arbitrary;
use sweeps::{Float, Point};

/// We'd like a type to denote "arbitrary float between -eps and eps", but since
/// f64s can't be const generics, we instead take "arbitrary float between -1/D and 1/D."
#[derive(Clone, Copy, Debug)]
struct BoundedFloat<const D: u64>(f64);

impl<'a, const D: u64> Arbitrary<'a> for BoundedFloat<D> {
    fn arbitrary(u: &mut arbitrary::Unstructured<'a>) -> arbitrary::Result<Self> {
        let numerator: i64 = Arbitrary::arbitrary(u)?;
        let x = (numerator as f64) / i64::MAX as f64;
        Ok(BoundedFloat(x / D as f64))
    }
}

#[derive(Arbitrary, Clone, Copy, Debug)]
enum FloatPerturbation<const D: u64> {
    /// Perturb by between -128 and 127 ulps.
    Ulp(i8),
    /// Perturb by a bounded additive amount.
    Eps(BoundedFloat<D>),
}

impl<const D: u64> FloatPerturbation<D> {
    fn apply(&self, f: Float) -> Float {
        dbg!(self, f);
        match self {
            FloatPerturbation::Ulp(n) => {
                let same_sign = (*n > 0) == (f.into_inner() > 0.0);
                let sign_bit = 1 << 63;
                match f.classify() {
                    std::num::FpCategory::Nan => unreachable!(),
                    std::num::FpCategory::Infinite => f,
                    std::num::FpCategory::Zero => {
                        let mut bits = n.unsigned_abs() as u64;
                        if *n < 0 {
                            bits |= sign_bit;
                        }
                        Float::new(f64::from_bits(bits)).unwrap()
                    }
                    std::num::FpCategory::Subnormal => {
                        let bits = f.abs().to_bits();
                        let bits = if same_sign {
                            bits + n.unsigned_abs() as u64
                        } else {
                            bits.abs_diff(n.unsigned_abs() as u64)
                        };
                        Float::new(f.signum() * f64::from_bits(bits)).unwrap()
                    }
                    std::num::FpCategory::Normal => {
                        let delta = if same_sign {
                            (*n as i64).abs()
                        } else {
                            -(*n as i64).abs()
                        };
                        // Taking the absolute value sets the sign bit to zero, so the
                        // addition should never overflow.
                        let bits = f.abs().to_bits().checked_add_signed(delta).unwrap();
                        let x = if bits & sign_bit != 0 {
                            f64::INFINITY
                        } else {
                            f64::from_bits(bits)
                        };
                        Float::new(f.signum() * x).unwrap()
                    }
                }
            }
            FloatPerturbation::Eps(x) => f + x.0,
        }
    }
}

#[derive(Arbitrary, Clone, Copy, Debug)]
struct PointPerturbation<const D: u64> {
    x: FloatPerturbation<D>,
    y: FloatPerturbation<D>,
}

impl<const D: u64> PointPerturbation<D> {
    fn apply(&self, p: Point) -> Point {
        Point {
            x: self.x.apply(p.x),
            y: self.y.apply(p.y),
        }
    }
}

#[derive(Clone, Copy, Debug)]
struct Frac(f64);

impl<'a> Arbitrary<'a> for Frac {
    fn arbitrary(u: &mut arbitrary::Unstructured<'a>) -> arbitrary::Result<Self> {
        Ok(Frac(u64::arbitrary(u)? as f64 / u64::MAX as f64))
    }
}

#[derive(Arbitrary, Clone, Debug)]
enum Perturbation<const D: u64> {
    None {
        idx: usize,
    },
    Point {
        perturbation: PointPerturbation<D>,
        idx: usize,
        next: Box<Perturbation<D>>,
    },
    Subdivision {
        t: Frac,
        idx: usize,
        next: Box<Perturbation<D>>,
    },
    Superimposition {
        left: Box<Perturbation<D>>,
        right: Box<Perturbation<D>>,
    },
}

fn index<T>(arr: &[T], idx: usize) -> &T {
    &arr[idx % arr.len()]
}

fn index_mut<T>(arr: &mut [T], idx: usize) -> &mut T {
    &mut arr[idx % arr.len()]
}

fn realize_perturbation<const D: u64>(
    base_cases: &[Vec<Point>],
    pert: &Perturbation<D>,
) -> Vec<Point> {
    match pert {
        Perturbation::None { idx } => index(base_cases, *idx).to_owned(),
        Perturbation::Point {
            perturbation,
            idx,
            next,
        } => {
            let mut next = realize_perturbation(base_cases, next);
            let p = index_mut(&mut next, *idx);
            *p = perturbation.apply(*p);
            next
        }
        Perturbation::Subdivision { t, idx, next } => {
            let mut next = realize_perturbation(base_cases, next);
            let idx = *idx % next.len();
            let p0 = *index(&next, idx);
            let p1 = *index(&next, idx + 1);
            next.insert(idx + 1, p0.affine(p1, Float::new(t.0).unwrap()));
            next
        }
        Perturbation::Superimposition { left, right } => {
            let mut next = realize_perturbation(base_cases, left);
            next.extend(realize_perturbation(base_cases, right));
            next
        }
    }
}

#[test]
fn test_main() {
    let base = vec![vec![
        Point::new(0.0, 0.0),
        Point::new(1.0, 1.0),
        Point::new(1.0, -1.0),
        Point::new(2.0, 0.0),
        Point::new(1.0, 1.0),
        Point::new(1.0, -1.0),
    ]];

    arbtest::arbtest(|u| {
        let perturbation = Perturbation::<1>::arbitrary(u)?;
        let after = realize_perturbation(&base, &perturbation);
        dbg!(after);

        Ok(())
    });
}
