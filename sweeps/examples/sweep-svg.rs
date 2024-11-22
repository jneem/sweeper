use std::{collections::HashMap, path::PathBuf};

use clap::Parser;
use kurbo::DEFAULT_ACCURACY;
use ordered_float::NotNan;
use sweeps::{
    geom::Point,
    sweep::{SegIdx, Segments},
};

type Float = NotNan<f64>;

#[derive(Parser)]
struct Args {
    input: PathBuf,
    output: PathBuf,

    #[arg(long)]
    epsilon: Option<f64>,

    #[arg(long)]
    dense: bool,
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
    let sweep_lines = if args.dense {
        sweeps::algorithms::weak::weaks_to_sweeps_dense(&weak_lines, &segments, &eps)
    } else {
        sweeps::algorithms::weak::weaks_to_sweeps_sparse(&weak_lines, &segments, &eps)
    };

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
    let pad = 1.0;
    let stroke_width = (max_y - min_y).max(max_x - max_y) / 1024.0;
    let dot_radius = stroke_width * 1.5;
    let mut document = svg::Document::new().set(
        "viewBox",
        (
            min_x - pad,
            min_y - pad,
            max_x - min_x + 2.0 * pad,
            max_y - min_y + 2.0 * pad,
        ),
    );
    for seg_idx in segments.indices() {
        let seg = segments.get(seg_idx);
        let data = svg::node::element::path::Data::new()
            .move_to((seg.start.x.into_inner(), seg.start.y.into_inner()))
            .line_to((seg.end.x.into_inner(), seg.end.y.into_inner()));
        let path = svg::node::element::Path::new()
            .set("stroke", "black")
            .set("stroke-width", stroke_width)
            .set("d", data);
        document = document.add(path);
    }

    let mut last_exit: HashMap<SegIdx, (f64, f64)> = HashMap::new();
    for line in sweep_lines {
        let y = line.y.into_inner();
        let data = svg::node::element::path::Data::new()
            .move_to((min_x, y))
            .line_to((max_x, y));
        let path = svg::node::element::Path::new()
            .set("stroke", "black")
            .set("stroke-width", stroke_width / 4.0)
            .set("stroke-opacity", "0.1")
            .set("d", data);

        for entry in line.segs {
            match entry.x {
                sweeps::sweep::SweepLineSeg::Single(x) => {
                    let c = svg::node::element::Circle::new()
                        .set("r", dot_radius)
                        .set("cy", y)
                        .set("cx", x.into_inner())
                        .set("opacity", 0.5)
                        .set("fill", "blue");
                    document = document.add(c);

                    if let Some(prev_exit) = last_exit.get(&entry.idx) {
                        let data = svg::node::element::path::Data::new()
                            .move_to(*prev_exit)
                            .line_to((x.into_inner(), y));
                        let path = svg::node::element::Path::new()
                            .set("stroke", "black")
                            .set("stroke-width", stroke_width / 2.0)
                            .set("stroke-opacity", "0.5")
                            .set("d", data);
                        document = document.add(path);
                    }

                    last_exit.insert(entry.idx, (x.into_inner(), y));
                }
                sweeps::sweep::SweepLineSeg::EnterExit(x0, x1) => {
                    // TODO: draw a line from its previous exit to x1
                    let c0 = svg::node::element::Circle::new()
                        .set("r", dot_radius)
                        .set("cy", y)
                        .set("cx", x0.into_inner())
                        .set("opacity", 0.5)
                        .set("fill", "red");
                    let c1 = svg::node::element::Circle::new()
                        .set("r", dot_radius)
                        .set("cy", y)
                        .set("cx", x1.into_inner())
                        .set("opacity", 0.5)
                        .set("fill", "green");
                    document = document.add(c0);
                    document = document.add(c1);

                    // A red line from entrance to exit
                    let data = svg::node::element::path::Data::new()
                        .move_to((x0.into_inner(), y))
                        .line_to((x1.into_inner(), y));
                    let path = svg::node::element::Path::new()
                        .set("stroke", "red")
                        .set("stroke-width", stroke_width / 2.0)
                        .set("stroke-opacity", "0.5")
                        .set("d", data);
                    document = document.add(path);

                    if let Some(prev_exit) = last_exit.get(&entry.idx) {
                        let data = svg::node::element::path::Data::new()
                            .move_to(*prev_exit)
                            .line_to((x0.into_inner(), y));
                        let path = svg::node::element::Path::new()
                            .set("stroke", "black")
                            .set("stroke-width", stroke_width / 2.0)
                            .set("stroke-opacity", "0.5")
                            .set("d", data);
                        document = document.add(path);
                    }

                    last_exit.insert(entry.idx, (x1.into_inner(), y));
                }
            }
        }
        document = document.add(path);
    }

    svg::save(&args.output, &document)?;

    Ok(())
}
