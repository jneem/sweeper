use malachite::{num::conversion::traits::RoundingFrom, rounding_modes::RoundingMode, Rational};
use ordered_float::NotNan;
use proptest::{arbitrary::any, prop_oneof, strategy::Strategy};

use crate::{geom::Point, num::Float};

#[derive(Clone, Copy, Debug)]
pub enum F64Perturbation {
    /// Perturb by between -128 and 127 ulps.
    Ulp(i8),
    /// Perturb by a bounded additive amount.
    Eps(f64),
}

#[derive(Clone, Copy, Debug)]
pub enum F32Perturbation {
    /// Perturb by between -128 and 127 ulps.
    Ulp(i8),
    /// Perturb by a bounded additive amount.
    Eps(f32),
}

#[derive(Clone, Debug)]
pub struct RationalPerturbation {
    /// Perturb by an additive amount.
    eps: Rational,
}

// The Debug bound is because some of the proptest strategy builders want it. Having it here is
// easier than copying it everywhere.
pub trait FloatPerturbation: std::fmt::Debug {
    type Float: crate::num::Float;

    fn apply(&self, f: &Self::Float) -> Self::Float;
}

impl FloatPerturbation for F64Perturbation {
    type Float = NotNan<f64>;

    fn apply(&self, f: &NotNan<f64>) -> NotNan<f64> {
        match self {
            F64Perturbation::Ulp(n) => {
                let same_sign = (*n > 0) == (f.into_inner() > 0.0);
                let sign_bit = 1 << 63;
                match f.classify() {
                    std::num::FpCategory::Nan => unreachable!(),
                    std::num::FpCategory::Infinite => *f,
                    std::num::FpCategory::Zero => {
                        let mut bits = n.unsigned_abs().into();
                        if *n < 0 {
                            bits |= sign_bit;
                        }
                        NotNan::new(f64::from_bits(bits)).unwrap()
                    }
                    std::num::FpCategory::Subnormal => {
                        let bits = f.abs().to_bits();
                        let bits = if same_sign {
                            bits + u64::from(n.unsigned_abs())
                        } else {
                            bits.abs_diff(u64::from(n.unsigned_abs()))
                        };
                        NotNan::new(f.signum() * f64::from_bits(bits)).unwrap()
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
                        NotNan::new(f.signum() * x).unwrap()
                    }
                }
            }
            F64Perturbation::Eps(x) => f + x,
        }
    }
}

// Can we do better than copy-pasting the f64 version?
impl FloatPerturbation for F32Perturbation {
    type Float = NotNan<f32>;

    fn apply(&self, f: &NotNan<f32>) -> NotNan<f32> {
        match self {
            F32Perturbation::Ulp(n) => {
                let same_sign = (*n > 0) == (f.into_inner() > 0.0);
                let sign_bit = 1 << 31;
                match f.classify() {
                    std::num::FpCategory::Nan => unreachable!(),
                    std::num::FpCategory::Infinite => *f,
                    std::num::FpCategory::Zero => {
                        let mut bits = n.unsigned_abs().into();
                        if *n < 0 {
                            bits |= sign_bit;
                        }
                        NotNan::new(f32::from_bits(bits)).unwrap()
                    }
                    std::num::FpCategory::Subnormal => {
                        let bits = f.abs().to_bits();
                        let bits = if same_sign {
                            bits + u32::from(n.unsigned_abs())
                        } else {
                            bits.abs_diff(u32::from(n.unsigned_abs()))
                        };
                        NotNan::new(f.signum() * f32::from_bits(bits)).unwrap()
                    }
                    std::num::FpCategory::Normal => {
                        let delta = if same_sign {
                            (*n as i32).abs()
                        } else {
                            -(*n as i32).abs()
                        };
                        // Taking the absolute value sets the sign bit to zero, so the
                        // addition should never overflow.
                        let bits = f.abs().to_bits().checked_add_signed(delta).unwrap();
                        let x = if bits & sign_bit != 0 {
                            f32::INFINITY
                        } else {
                            f32::from_bits(bits)
                        };
                        NotNan::new(f.signum() * x).unwrap()
                    }
                }
            }
            F32Perturbation::Eps(x) => f + x,
        }
    }
}

impl FloatPerturbation for RationalPerturbation {
    type Float = Rational;

    fn apply(&self, f: &Rational) -> Rational {
        f.clone() + &self.eps
    }
}

#[derive(Clone, Copy, Debug)]
pub struct PointPerturbation<P: FloatPerturbation> {
    pub x: P,
    pub y: P,
}

impl<P: FloatPerturbation> PointPerturbation<P> {
    pub fn apply(&self, p: Point<P::Float>) -> Point<P::Float> {
        Point {
            x: self.x.apply(&p.x),
            y: self.y.apply(&p.y),
        }
    }
}

#[derive(Clone, Debug)]
pub enum Perturbation<P: FloatPerturbation> {
    Base {
        idx: usize,
    },
    Point {
        perturbation: PointPerturbation<P>,
        idx: usize,
        next: Box<Perturbation<P>>,
    },
    Subdivision {
        // Between 0.0 and 1.0
        t: P::Float,
        idx: usize,
        next: Box<Perturbation<P>>,
    },
    Superimposition {
        left: Box<Perturbation<P>>,
        right: Box<Perturbation<P>>,
    },
}

pub fn f64_perturbation(eps: f64) -> impl Strategy<Value = F64Perturbation> + Clone {
    prop_oneof![
        any::<i8>().prop_map(F64Perturbation::Ulp),
        (-eps..=eps).prop_map(F64Perturbation::Eps)
    ]
}

pub fn f32_perturbation(eps: f32) -> impl Strategy<Value = F32Perturbation> + Clone {
    prop_oneof![
        any::<i8>().prop_map(F32Perturbation::Ulp),
        (-eps..=eps).prop_map(F32Perturbation::Eps)
    ]
}

pub fn rational_perturbation(eps: Rational) -> impl Strategy<Value = RationalPerturbation> + Clone {
    // Neither malachite nor proptest implements ranges for rationals, so we convert to float and then convert back.
    let eps: f64 = RoundingFrom::rounding_from(&eps, RoundingMode::Nearest).0;
    (-eps..=eps).prop_map(|x| RationalPerturbation {
        eps: x.try_into().unwrap(),
    })
}

pub fn point_perturbation<P: FloatPerturbation>(
    fp: impl Strategy<Value = P> + Clone,
) -> impl Strategy<Value = PointPerturbation<P>> {
    (fp.clone(), fp).prop_map(|(x, y)| PointPerturbation { x, y })
}

pub fn perturbation<P: FloatPerturbation + 'static>(
    fp: impl Strategy<Value = P> + Clone + 'static,
) -> impl Strategy<Value = Perturbation<P>> {
    let leaf = any::<usize>().prop_map(|idx| Perturbation::Base { idx });
    leaf.prop_recursive(3, 16, 8, move |inner| {
        prop_oneof![
            (
                point_perturbation(fp.clone()),
                any::<usize>(),
                inner.clone()
            )
                .prop_map(|(perturbation, idx, next)| {
                    Perturbation::Point {
                        perturbation,
                        idx,
                        next: Box::new(next),
                    }
                }),
            (0.0f32..1.0, any::<usize>(), inner.clone()).prop_map(|(t, idx, next)| {
                Perturbation::Subdivision {
                    t: Float::from_f32(t),
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

pub fn realize_perturbation<P: FloatPerturbation>(
    base_cases: &[Vec<Point<P::Float>>],
    pert: &Perturbation<P>,
) -> Vec<Point<P::Float>> {
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
            next.insert(idx + 1, p0.affine(&p1, t));
            next
        }
        Perturbation::Superimposition { left, right } => {
            let mut next = realize_perturbation(base_cases, left);
            next.extend(realize_perturbation(base_cases, right));
            next
        }
    }
}
