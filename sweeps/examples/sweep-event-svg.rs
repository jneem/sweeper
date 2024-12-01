use std::{collections::HashSet, path::PathBuf};

use clap::Parser;
use kurbo::DEFAULT_ACCURACY;
use ordered_float::NotNan;
use sweeps::{
    algorithms::weak::{Position, PositionKind},
    geom::Point,
    sweep::Segments,
};

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

struct SegmentCollector {
    segs: Vec<Vec<Point<Float>>>,
    backwards: Vec<Vec<Point<Float>>>,
    y: Float,
}

impl SegmentCollector {
    fn advance_y(&mut self, y: Float) {
        for (seg, back) in self.segs.iter_mut().zip(&mut self.backwards) {
            seg.extend(std::mem::take(back).into_iter().rev());
        }
        self.y = y;
    }

    fn handle(&mut self, y: Float, ev: Position<Float>) {
        dbg!(y, &ev);
        let seg_idx = ev.seg_idx.0;
        if y > self.y {
            self.advance_y(y);
        }
        match ev.kind {
            PositionKind::Point(x) => {
                self.segs[seg_idx].push(Point::new(x, y));
            }
            PositionKind::Horizontal(x0, x1) => {
                let (segs, x0, x1) = if x0 < x1 {
                    (&mut self.segs[seg_idx], x0, x1)
                } else {
                    (&mut self.backwards[seg_idx], x1, x0)
                };
                if segs.is_empty() {
                    segs.push(Point::new(x0, y));
                }
                segs.push(Point::new(x1, y));
            }
        };
    }

    fn new(size: usize) -> Self {
        Self {
            segs: vec![Vec::new(); size],
            backwards: vec![Vec::new(); size],
            y: f64::NEG_INFINITY.try_into().unwrap(),
        }
    }

    fn finish(mut self, segs: &Segments<Float>) -> Vec<Vec<Point<Float>>> {
        for (i, seg) in self.segs.iter_mut().enumerate() {
            if !segs.orientation[i] {
                seg.reverse();
            }
        }
        self.segs
    }
}

pub fn main() -> anyhow::Result<()> {
    let args = Args::parse();

    let input = std::fs::read_to_string(&args.input)?;
    let tree = usvg::Tree::from_str(&input, &usvg::Options::default())?;
    let segments = svg_to_segments(&tree);

    let eps = args.epsilon.unwrap_or(0.1).try_into().unwrap();
    let weak_lines = sweeps::algorithms::weak::sweep(&segments, &eps);
    let mut collector = SegmentCollector::new(segments.segs.len());
    sweeps::algorithms::weak::weaks_to_events_sparse(&weak_lines, &segments, &eps, |y, ev| {
        collector.handle(y, ev)
    });

    let segs = collector.finish(&segments);

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

    let mut visited = HashSet::new();
    for mut seg_idx in segments.indices() {
        if !visited.insert(seg_idx) {
            continue;
        }

        let mut data = svg::node::element::path::Data::new();
        let start_idx = seg_idx;
        let seg = segments.get(seg_idx);
        let p = if segments.orientation[seg_idx.0] {
            &seg.start
        } else {
            &seg.end
        };
        data = data.move_to((p.x.into_inner(), p.y.into_inner()));

        while let Some(idx) = segments.contour_next[seg_idx.0] {
            seg_idx = idx;
            visited.insert(seg_idx);
            if seg_idx == start_idx {
                data = data.close();
                break;
            } else {
                let seg = segments.get(seg_idx);
                let p = if segments.orientation[seg_idx.0] {
                    &seg.start
                } else {
                    &seg.end
                };
                data = data.line_to((p.x.into_inner(), p.y.into_inner()));
            }
        }

        let path = svg::node::element::Path::new()
            .set("stroke", "black")
            .set("stroke-width", 2.0 * eps.into_inner())
            .set("stroke-linecap", "round")
            .set("stroke-linejoin", "round")
            .set("opacity", 0.2)
            .set("fill", "none")
            .set("d", data);
        document = document.add(path);
    }

    for seg in segs {
        for ps in seg.windows(2) {
            let (x0, y0) = (ps[0].x.into_inner(), ps[0].y.into_inner());
            let (x1, y1) = (ps[1].x.into_inner(), ps[1].y.into_inner());
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
        }
    }

    svg::save(&args.output, &document)?;

    Ok(())
}
