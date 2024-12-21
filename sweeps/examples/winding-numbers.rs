use std::path::PathBuf;

use clap::Parser;
use kurbo::DEFAULT_ACCURACY;
use ordered_float::NotNan;
use sweeps::{geom::Point, sweep::Segments, topology::Topology};

type Float = NotNan<f64>;

#[derive(Parser)]
struct Args {
    input: PathBuf,
    output: PathBuf,

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
    let weak_lines = sweeps::weak_ordering::sweep(&segments, &eps);
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
    let stroke_width = (max_y - min_y).max(max_x - max_y) / 512.0;
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

    let text_size = "1px";

    for seg in top.segment_indices() {
        let p0 = &top.point[seg.first_half()];
        let p1 = &top.point[seg.second_half()];
        let (x0, y0) = (p0.x.into_inner(), p0.y.into_inner());
        let (x1, y1) = (p1.x.into_inner(), p1.y.into_inner());
        let c = svg::node::element::Circle::new()
            .set("r", dot_radius)
            .set("cy", y0)
            .set("cx", x0)
            .set("opacity", 0.5)
            .set("fill", "blue");
        document = document.add(c);

        let c = svg::node::element::Circle::new()
            .set("r", dot_radius)
            .set("cy", y1)
            .set("cx", x1)
            .set("opacity", 0.5)
            .set("fill", "blue");
        document = document.add(c);

        let data = svg::node::element::path::Data::new()
            .move_to((x0, y0))
            .line_to((x1, y1));
        let path = svg::node::element::Path::new()
            .set("stroke", "black")
            .set("stroke-width", stroke_width / 2.0)
            .set("stroke-opacity", "0.5")
            .set("d", data);
        document = document.add(path);

        let nx = y1 - y0;
        let ny = x0 - x1;
        let norm = ((nx * nx) + (ny * ny)).sqrt();

        let nx = nx / norm * 3.0 * dot_radius;
        let ny = ny / norm * 3.0 * dot_radius;

        let text =
            svg::node::element::Text::new(format!("{:?}", top.winding[seg].counter_clockwise))
                .set("font-size", text_size)
                .set("text-anchor", "start")
                .set("x", (x0 + x1) / 2.0 + nx)
                .set("y", (y0 + y1) / 2.0 + ny);
        document = document.add(text);

        let text = svg::node::element::Text::new(format!("{:?}", top.winding[seg].clockwise))
            .set("font-size", text_size)
            .set("text-anchor", "end")
            .set("x", (x0 + x1) / 2.0 - nx)
            .set("y", (y0 + y1) / 2.0 - ny);
        document = document.add(text);
    }

    svg::save(&args.output, &document)?;

    Ok(())
}
