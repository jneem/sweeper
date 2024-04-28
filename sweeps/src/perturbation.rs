use ordered_float::NotNan;
use proptest::{arbitrary::any, prop_oneof, strategy::Strategy};

use crate::geom::Point;

// TODO: Support perturbations for more types
type Float = NotNan<f64>;

#[derive(Clone, Copy, Debug)]
pub enum FloatPerturbation {
    /// Perturb by between -128 and 127 ulps.
    Ulp(i8),
    /// Perturb by a bounded additive amount.
    Eps(f64),
}

impl FloatPerturbation {
    fn apply(&self, f: Float) -> Float {
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
            FloatPerturbation::Eps(x) => f + x,
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub struct PointPerturbation {
    pub x: FloatPerturbation,
    pub y: FloatPerturbation,
}

impl PointPerturbation {
    pub fn apply(&self, p: Point<Float>) -> Point<Float> {
        Point {
            x: self.x.apply(p.x),
            y: self.y.apply(p.y),
        }
    }
}

#[derive(Clone, Debug)]
pub enum Perturbation {
    Base {
        idx: usize,
    },
    Point {
        perturbation: PointPerturbation,
        idx: usize,
        next: Box<Perturbation>,
    },
    Subdivision {
        // Between 0.0 and 1.0
        t: f64,
        idx: usize,
        next: Box<Perturbation>,
    },
    Superimposition {
        left: Box<Perturbation>,
        right: Box<Perturbation>,
    },
}

pub fn float_perturbation(eps: f64) -> impl Strategy<Value = FloatPerturbation> {
    prop_oneof![
        any::<i8>().prop_map(FloatPerturbation::Ulp),
        (-eps..=eps).prop_map(FloatPerturbation::Eps)
    ]
}

pub fn point_perturbation(eps: f64) -> impl Strategy<Value = PointPerturbation> {
    (float_perturbation(eps), float_perturbation(eps)).prop_map(|(x, y)| PointPerturbation { x, y })
}

pub fn perturbation(eps: f64) -> impl Strategy<Value = Perturbation> {
    let leaf = any::<usize>().prop_map(|idx| Perturbation::Base { idx });
    leaf.prop_recursive(3, 16, 8, move |inner| {
        prop_oneof![
            (point_perturbation(eps), any::<usize>(), inner.clone()).prop_map(
                |(perturbation, idx, next)| {
                    Perturbation::Point {
                        perturbation,
                        idx,
                        next: Box::new(next),
                    }
                }
            ),
            (0.0..1.0, any::<usize>(), inner.clone()).prop_map(|(t, idx, next)| {
                Perturbation::Subdivision {
                    t,
                    idx,
                    next: Box::new(next),
                }
            }),
            (inner.clone(), inner.clone()).prop_map(|(left, right)| {
                Perturbation::Superimposition {
                    left: Box::new(left),
                    right: Box::new(right),
                }
            })
        ]
    })
}

fn index<T>(arr: &[T], idx: usize) -> &T {
    &arr[idx % arr.len()]
}

fn index_mut<T>(arr: &mut [T], idx: usize) -> &mut T {
    &mut arr[idx % arr.len()]
}

pub fn realize_perturbation(
    base_cases: &[Vec<Point<Float>>],
    pert: &Perturbation,
) -> Vec<Point<Float>> {
    match pert {
        Perturbation::Base { idx } => index(base_cases, *idx).to_owned(),
        Perturbation::Point {
            perturbation,
            idx,
            next,
        } => {
            let mut next = realize_perturbation(base_cases, next);
            let p = index_mut(&mut next, *idx);
            *p = perturbation.apply(p.clone());
            next
        }
        Perturbation::Subdivision { t, idx, next } => {
            let mut next = realize_perturbation(base_cases, next);
            let idx = *idx % next.len();
            let p0 = index(&next, idx).clone();
            let p1 = index(&next, idx + 1).clone();
            next.insert(idx + 1, p0.affine(&p1, &Float::new(*t).unwrap()));
            next
        }
        Perturbation::Superimposition { left, right } => {
            let mut next = realize_perturbation(base_cases, left);
            next.extend(realize_perturbation(base_cases, right));
            next
        }
    }
}
