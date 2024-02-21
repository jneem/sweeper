use std::{fs::File, path::PathBuf};

use clap::Parser;
use svg::node::element::{path::Data, Circle};
use sweeps::Point;

#[derive(Parser)]
struct Args {
    path: PathBuf,

    #[arg(long)]
    winding: i32,

    #[arg(long)]
    #[clap(default_value_t = 0.1)]
    epsilon: f64,

    #[arg(long, short)]
    output: PathBuf,
}

fn main() -> anyhow::Result<()> {
    let args = Args::parse();
    let data = std::fs::read(args.path)?;
    let opt = usvg::Options::default();
    let tree = usvg::Tree::from_data(&data, &opt)?;

    let polylines = extract_group(tree.root());
    let mut sweeper = sweeps::Sweeper::new(args.epsilon.try_into().unwrap());
    for p in &polylines {
        sweeper.add_closed_polyline(p);
    }
    sweeper.run();
    let out_polylines = sweeper
        .segments
        .walk_winding(&sweeper.ordered_intersections, args.winding);
    let out = polyline_svg(&out_polylines, args.epsilon);
    let out_file = File::create(args.output)?;
    svg::write(out_file, &out)?;

    Ok(())
}

fn polyline_svg(polylines: &[Vec<Point>], eps: f64) -> svg::Document {
    let mut lines = Vec::new();
    let mut points = Vec::new();
    let mut min_x = f64::INFINITY;
    let mut max_x = f64::NEG_INFINITY;
    let mut min_y = f64::INFINITY;
    let mut max_y = f64::NEG_INFINITY;
    for polyline in polylines {
        points.extend(polyline.iter().map(|p| {
            Circle::new()
                .set("cx", p.x.into_inner())
                .set("cy", p.y.into_inner())
                .set("r", 2.0 * eps)
                .set("fill", "black")
        }));

        let last = polyline.last().unwrap();
        let mut data = Data::new().move_to((last.x.into_inner(), last.y.into_inner()));
        for p in polyline {
            min_x = min_x.min(p.x.into_inner());
            max_x = max_x.max(p.x.into_inner());
            min_y = min_y.min(p.y.into_inner());
            max_y = max_y.max(p.y.into_inner());
            data = data.line_to((p.x.into_inner(), p.y.into_inner()));
        }
        lines.push(
            svg::node::element::Path::new()
                .set("fill", "blue")
                .set("stroke", "green")
                .set("stroke-width", eps)
                .set("d", data),
        );
    }

    let mut document = svg::Document::new().set(
        "viewBox",
        (
            min_x - 2.0 * eps,
            min_y - 2.0 * eps,
            max_x - min_x + 4.0 * eps,
            max_y - min_y + 4.0 * eps,
        ),
    );
    for line in lines {
        document = document.add(line);
    }
    for p in points {
        document = document.add(p);
    }
    document
}

fn extract_group(group: &usvg::Group) -> Vec<Vec<Point>> {
    let mut ret = Vec::new();
    for node in group.children() {
        match node {
            usvg::Node::Group(g) => {
                ret.extend(extract_group(g));
            }
            usvg::Node::Path(p) => {
                let path = p.data().clone().transform(group.abs_transform()).unwrap();
                ret.extend(convert_path(&path));
            }
            _ => {}
        }
    }

    ret
}

fn convert_path(path: &usvg::tiny_skia_path::Path) -> Vec<Vec<Point>> {
    use usvg::tiny_skia_path::PathSegment::*;

    let mut ret = Vec::new();
    let mut cur_path = Vec::new();

    for seg in path.segments() {
        match seg {
            MoveTo(p) => {
                if !cur_path.is_empty() {
                    ret.push(std::mem::take(&mut cur_path));
                }
                let p = Point::new(p.x as f64, p.y as f64);
                cur_path.push(p);
            }
            LineTo(p) => {
                let p = Point::new(p.x as f64, p.y as f64);
                cur_path.push(p);
            }
            Close => {
                ret.push(std::mem::take(&mut cur_path));
            }
            QuadTo(_, _) | CubicTo(_, _, _) => panic!("no curves, sorry"),
        }
    }

    if !cur_path.is_empty() {
        ret.push(cur_path);
    }
    ret
}
