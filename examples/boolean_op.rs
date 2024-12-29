use std::{collections::HashSet, path::PathBuf, str::FromStr};

use clap::Parser;
use ordered_float::NotNan;
use svg::Document;

use linesweeper::{Point, Segments, Topology};

type Float = NotNan<f64>;

#[derive(Copy, Clone, Debug)]
enum Op {
    Union,
    Intersection,
    Xor,
    Difference,
    ReverseDifference,
}

impl FromStr for Op {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "union" => Ok(Op::Union),
            "intersection" => Ok(Op::Intersection),
            "xor" => Ok(Op::Xor),
            "difference" => Ok(Op::Difference),
            "reverse_difference" => Ok(Op::ReverseDifference),
            _ => Err(format!("unknown op {s}")),
        }
    }
}

#[derive(Parser)]
struct Args {
    input: PathBuf,
    output: PathBuf,

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
                    let data = path.data().clone().transform(path.abs_transform()).unwrap();
                    let kurbo_els = data.segments().map(|seg| match seg {
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
                    kurbo::flatten(kurbo_els, 1e-6, |el| match el {
                        kurbo::PathEl::MoveTo(p) => {
                            ret.add_points(points.drain(..));
                            points
                                .push(Point::new(p.x.try_into().unwrap(), p.y.try_into().unwrap()));
                        }
                        kurbo::PathEl::LineTo(p) => {
                            points
                                .push(Point::new(p.x.try_into().unwrap(), p.y.try_into().unwrap()));
                        }
                        kurbo::PathEl::ClosePath => {
                            let p = points.first().cloned();
                            ret.add_cycle(points.drain(..));
                            if let Some(p) = p {
                                points.push(p);
                            }
                        }
                        kurbo::PathEl::QuadTo(..) | kurbo::PathEl::CurveTo(..) => unreachable!(),
                    });

                    if points.len() > 1 {
                        ret.add_points(points.drain(..));
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
    eprintln!("{} segments", segments.len());

    let eps = args.epsilon.unwrap_or(0.1).try_into().unwrap();
    let top = Topology::new(&segments, &eps);

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
    let one_width = max_x - min_x + 2.0 * pad;
    let one_height = max_y - min_y + 2.0 * pad;
    let stroke_width = (max_y - min_y).max(max_x - max_y) / 512.0;
    let mut document = svg::Document::new().set(
        "viewBox",
        (min_x - pad, min_y - pad, one_width * 3.0, one_height * 2.0),
    );

    // Draw the original document.
    let mut visited = HashSet::new();
    for mut seg_idx in segments.indices() {
        if !visited.insert(seg_idx) {
            continue;
        }

        let mut data = svg::node::element::path::Data::new();
        let start_idx = seg_idx;
        let p = segments.oriented_start(seg_idx);
        data = data.move_to((p.x.into_inner(), p.y.into_inner()));

        while let Some(idx) = segments.contour_next(seg_idx) {
            seg_idx = idx;
            visited.insert(seg_idx);
            if seg_idx == start_idx {
                data = data.close();
                break;
            } else {
                let p = segments.oriented_start(seg_idx);
                data = data.line_to((p.x.into_inner(), p.y.into_inner()));
            }
        }

        let path = svg::node::element::Path::new()
            .set("stroke", "black")
            .set("stroke-width", stroke_width)
            .set("stroke-linecap", "round")
            .set("stroke-linejoin", "round")
            .set("opacity", 0.2)
            .set("fill", "none")
            .set("d", data);
        document = document.add(path);
    }

    document = add_op(
        document,
        Op::Union,
        args.non_zero,
        &top,
        one_width,
        0.0,
        stroke_width,
    );
    document = add_op(
        document,
        Op::Intersection,
        args.non_zero,
        &top,
        one_width * 2.0,
        0.0,
        stroke_width,
    );
    document = add_op(
        document,
        Op::Xor,
        args.non_zero,
        &top,
        0.0,
        one_height,
        stroke_width,
    );
    document = add_op(
        document,
        Op::Difference,
        args.non_zero,
        &top,
        one_width,
        one_height,
        stroke_width,
    );
    document = add_op(
        document,
        Op::ReverseDifference,
        args.non_zero,
        &top,
        one_width * 2.0,
        one_height,
        stroke_width,
    );

    svg::save(&args.output, &document)?;

    Ok(())
}

fn add_op(
    mut doc: Document,
    op: Op,
    non_zero: bool,
    top: &Topology<Float>,
    x_off: f64,
    y_off: f64,
    stroke_width: f64,
) -> Document {
    let contours = top.contours(|w| {
        let inside = |winding| {
            if non_zero {
                winding != 0
            } else {
                winding % 2 != 0
            }
        };

        match op {
            Op::Union => inside(w.shape_a) || inside(w.shape_b),
            Op::Intersection => inside(w.shape_a) && inside(w.shape_b),
            Op::Xor => inside(w.shape_a) != inside(w.shape_b),
            Op::Difference => inside(w.shape_a) && !inside(w.shape_b),
            Op::ReverseDifference => inside(w.shape_b) && !inside(w.shape_a),
        }
    });

    let colors = [
        "#005F73", "#0A9396", "#94D2BD", "#E9D8A6", "#EE9B00", "#CA6702", "#BB3E03", "#AE2012",
        "#9B2226",
    ];

    let mut color_idx = 0;
    for group in contours.grouped() {
        let mut data = svg::node::element::path::Data::new();

        for contour_idx in group {
            let mut contour = contours[contour_idx].points.iter().cloned();
            let Some(p) = contour.next() else {
                continue;
            };

            let (x, y) = (p.x.into_inner(), p.y.into_inner());
            data = data.move_to((x + x_off, y + y_off));
            for p in contour {
                let (x, y) = (p.x.into_inner(), p.y.into_inner());
                data = data.line_to((x + x_off, y + y_off));
            }
            data = data.close();
        }
        let path = svg::node::element::Path::new()
            .set("d", data)
            .set("stroke", "black")
            .set("stroke-width", stroke_width)
            .set("stroke-linecap", "round")
            .set("stroke-linejoin", "round")
            .set("fill", colors[color_idx]);
        doc = doc.add(path);
        color_idx = (color_idx + 1) % colors.len();
    }
    doc
}
