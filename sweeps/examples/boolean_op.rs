use std::{path::PathBuf, str::FromStr};

use clap::Parser;
use kurbo::DEFAULT_ACCURACY;
use ordered_float::NotNan;
use sweeps::{geom::Point, sweep::Segments, topology::Topology};

type Float = NotNan<f64>;

#[derive(Copy, Clone, Debug)]
enum Op {
    Union,
    Intersection,
    Xor,
}

impl FromStr for Op {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "union" => Ok(Op::Union),
            "intersection" => Ok(Op::Intersection),
            "xor" => Ok(Op::Xor),
            _ => Err(format!("unknown op {s}")),
        }
    }
}

#[derive(Parser)]
struct Args {
    input: PathBuf,
    output: PathBuf,

    #[arg(long)]
    op: Op,

    #[arg(long)]
    non_zero: bool,

    #[arg(long)]
    epsilon: Option<f64>,
}

fn svg_to_segments(tree: &usvg::Tree) -> Segments<NotNan<f64>> {
    let mut ret = Segments::default();

    fn pt(p: usvg::tiny_skia_path::Point) -> kurbo::Point {
        kurbo::Point::new(p.x as f64, p.y as f64)
    }

    fn add_group(group: &usvg::Group, ret: &mut Segments<NotNan<f64>>) {
        for child in group.children() {
            match child {
                usvg::Node::Group(group) => add_group(group, ret),
                usvg::Node::Path(path) => {
                    let kurbo_els = path.data().segments().map(|seg| match seg {
                        usvg::tiny_skia_path::PathSegment::MoveTo(p) => {
                            kurbo::PathEl::MoveTo(pt(p))
                        }
                        usvg::tiny_skia_path::PathSegment::LineTo(p) => {
                            kurbo::PathEl::LineTo(pt(p))
                        }
                        usvg::tiny_skia_path::PathSegment::QuadTo(p0, p1) => {
                            kurbo::PathEl::QuadTo(pt(p0), pt(p1))
                        }
                        usvg::tiny_skia_path::PathSegment::CubicTo(p0, p1, p2) => {
                            kurbo::PathEl::CurveTo(pt(p0), pt(p1), pt(p2))
                        }
                        usvg::tiny_skia_path::PathSegment::Close => kurbo::PathEl::ClosePath,
                    });

                    let mut points = Vec::<Point<Float>>::new();
                    kurbo::flatten(kurbo_els, DEFAULT_ACCURACY, |el| match el {
                        kurbo::PathEl::MoveTo(p) => {
                            ret.add_points(points.drain(..), false);
                            points
                                .push(Point::new(p.x.try_into().unwrap(), p.y.try_into().unwrap()));
                        }
                        kurbo::PathEl::LineTo(p) => {
                            points
                                .push(Point::new(p.x.try_into().unwrap(), p.y.try_into().unwrap()));
                        }
                        kurbo::PathEl::ClosePath => {
                            let p = points.first().cloned();
                            ret.add_points(points.drain(..), true);
                            if let Some(p) = p {
                                points.push(p);
                            }
                        }
                        kurbo::PathEl::QuadTo(..) | kurbo::PathEl::CurveTo(..) => unreachable!(),
                    });

                    if points.len() > 1 {
                        ret.add_points(points.drain(..), false);
                    }
                }
                _ => {}
            }
        }
    }

    add_group(tree.root(), &mut ret);
    ret
}

pub fn main() -> anyhow::Result<()> {
    let args = Args::parse();

    let input = std::fs::read_to_string(&args.input)?;
    let tree = usvg::Tree::from_str(&input, &usvg::Options::default())?;
    let segments = svg_to_segments(&tree);

    let eps = args.epsilon.unwrap_or(0.1).try_into().unwrap();
    let weak_lines = sweeps::algorithms::weak::sweep(&segments, &eps);
    let top = Topology::build(&weak_lines, &segments, &eps);

    // I tried using `tree.root().abs_bounding_box()`, but I don't understand the output.
    let ys: Vec<_> = segments
        .segments()
        .flat_map(|s| [s.start.y, s.end.y])
        .collect();
    let xs: Vec<_> = segments
        .segments()
        .flat_map(|s| [s.start.x, s.end.x])
        .collect();
    let min_x = xs.iter().min().unwrap().into_inner();
    let max_x = xs.iter().max().unwrap().into_inner();
    let min_y = ys.iter().min().unwrap().into_inner();
    let max_y = ys.iter().max().unwrap().into_inner();
    let pad = 1.0 + eps.into_inner();
    let mut document = svg::Document::new().set(
        "viewBox",
        (
            min_x - pad,
            min_y - pad,
            max_x - min_x + 2.0 * pad,
            max_y - min_y + 2.0 * pad,
        ),
    );

    let contours = top.contours(|w| {
        let inside = |winding| {
            if args.non_zero {
                winding != 0
            } else {
                winding % 2 != 0
            }
        };

        match args.op {
            Op::Union => inside(w.shape_a) || inside(w.shape_b),
            Op::Intersection => inside(w.shape_a) && inside(w.shape_b),
            Op::Xor => inside(w.shape_a) != inside(w.shape_b),
        }
    });

    for contour in contours {
        let mut data = svg::node::element::path::Data::new();
        let mut contour = contour.into_iter();
        let Some(p) = contour.next() else {
            continue;
        };

        let (x, y) = (p.x.into_inner(), p.y.into_inner());
        data = data.move_to((x, y));
        for p in contour {
            let (x, y) = (p.x.into_inner(), p.y.into_inner());
            data = data.line_to((x, y));
        }
        data = data.close();
        let path = svg::node::element::Path::new()
            .set("d", data)
            .set("fill", "black");
        document = document.add(path);
    }

    svg::save(&args.output, &document)?;

    Ok(())
}
