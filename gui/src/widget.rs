use std::sync::Arc;

use ordered_float::NotNan;
use sweeps::algorithms::strip::{Strip, StripSeg};
use xilem::{
    parley::{self, FontContext, Layout},
    text::render_text,
    vello::{
        kurbo::{Affine, Circle, Line, Point, Rect, Stroke},
        peniko::{Brush, Color, Fill},
    },
    widget::{LifeCycle, Widget},
};

use crate::{SweepState, F};

pub struct Sweep {
    pub state: Arc<SweepState>,
    hot_seg: Option<StripSeg<F>>,
    transform: Affine,
    layout: Option<Layout<Brush>>,
}

impl Sweep {
    pub fn new(state: Arc<SweepState>) -> Self {
        Sweep {
            state,
            transform: Affine::IDENTITY,
            hot_seg: None,
            layout: None,
        }
    }

    pub fn seg_at(&self, p: Point) -> Option<StripSeg<F>> {
        let p = self.transform.inverse() * p;
        if let Some(strip) = self.state.strips.iter().find(|s| s.y1.into_inner() >= p.y) {
            let y0 = strip.y0.into_inner();
            let y1 = strip.y1.into_inner();
            let y_frac = (p.y - y0) / (y1 - y0);

            let seg = strip.segs.iter().min_by_key(|s| {
                let x0 = s.x0.into_inner();
                let x1 = s.x1.into_inner();
                let x = x0 + (x1 - x0) * y_frac;

                NotNan::new((x - p.x).abs()).unwrap()
            });
            // TODO: put a threshold -- make sure it's actually close
            seg.cloned()
        } else {
            None
        }
    }

    fn draw_point(&self, scene: &mut xilem::vello::Scene, p: Point) {
        let circle = Circle::new(p, 0.1);
        scene.fill(
            Fill::NonZero,
            self.transform,
            Color::ROYAL_BLUE.with_alpha_factor(0.25),
            None,
            &circle,
        );
        scene.stroke(
            &Stroke::new(0.0),
            self.transform,
            Color::ROYAL_BLUE.with_alpha_factor(0.25),
            None,
            &circle,
        );
    }

    fn draw_strip(&self, scene: &mut xilem::vello::Scene, strip: &Strip<F>) {
        let y0 = strip.y0.into_inner();
        let y1 = strip.y1.into_inner();
        for seg in &strip.segs {
            let p0 = Point::new(seg.x0.into_inner(), y0);
            let p1 = Point::new(seg.x1.into_inner(), y1);
            self.draw_point(scene, p0);
            self.draw_point(scene, p1);
        }

        for seg in &strip.segs {
            let p0 = Point::new(seg.x0.into_inner(), y0);
            let p1 = Point::new(seg.x1.into_inner(), y1);
            let color = if Some(seg) == self.hot_seg.as_ref() {
                Color::LAWN_GREEN
            } else {
                Color::BLANCHED_ALMOND
            };
            scene.stroke(
                &Stroke::new(0.05),
                self.transform,
                color,
                None,
                &Line::new(p0, p1),
            );
        }
    }

    fn compute_seg_layout(&mut self, fc: &mut FontContext) {
        let Some(hot_seg) = self.hot_seg.as_ref() else {
            self.layout = None;
            return;
        };

        let mut lcx = parley::LayoutContext::new();
        let text = format!(
            "seg {}, {:.3} -- {:.3}",
            hot_seg.idx.0, hot_seg.x0, hot_seg.x1
        );
        let mut layout_builder = lcx.ranged_builder(fc, &text, 1.0);
        layout_builder.push_default(&parley::style::StyleProperty::Brush(Brush::Solid(
            Color::BLACK,
        )));
        layout_builder.push_default(&parley::style::StyleProperty::FontStack(
            parley::style::FontStack::Source("system-ui"),
        ));
        let mut layout = layout_builder.build();
        layout.break_all_lines(None, parley::layout::Alignment::Start);
        self.layout = Some(layout);
    }
}

impl Widget for Sweep {
    fn event(&mut self, cx: &mut xilem::widget::EventCx, event: &xilem::widget::Event) {
        if let xilem::widget::Event::MouseMove(ev) = event {
            let hot_seg = self.seg_at(ev.pos);
            if hot_seg != self.hot_seg {
                self.hot_seg = hot_seg;
                cx.request_layout();
                cx.request_paint();
            }
        }
        //dbg!(event);
    }

    fn lifecycle(&mut self, cx: &mut xilem::widget::LifeCycleCx, event: &xilem::widget::LifeCycle) {
        if matches!(event, LifeCycle::HotChanged(_)) {
            cx.request_paint();
        }
    }

    fn update(&mut self, _cx: &mut xilem::widget::UpdateCx) {}

    fn layout(
        &mut self,
        cx: &mut xilem::widget::LayoutCx,
        bc: &xilem::widget::BoxConstraints,
    ) -> xilem::vello::kurbo::Size {
        self.compute_seg_layout(cx.font_cx());
        bc.constrain((100.0, 100.0))
    }

    fn paint(&mut self, cx: &mut xilem::widget::PaintCx, scene: &mut xilem::vello::Scene) {
        let size = cx.size();
        let center = (size.to_vec2() / 2.0).to_point();

        let bbox = self
            .state
            .strips
            .iter()
            .map(strip_box)
            .reduce(|x, y| x.union(y));
        if let Some(bbox) = bbox {
            let bbox = bbox.inset(0.2);
            let scale = (size.width / bbox.width()).min(size.height / bbox.height());
            let transform = Affine::translate(-bbox.center().to_vec2())
                .then_scale(scale)
                .then_translate(center.to_vec2());
            self.transform = transform;
            for strip in &self.state.strips {
                self.draw_strip(scene, strip);
            }
        }

        if let Some(layout) = self.layout.as_ref() {
            render_text(scene, Affine::IDENTITY, layout);
        }
    }
}

fn strip_box(strip: &Strip<F>) -> Rect {
    if strip.segs.is_empty() {
        return Rect::default();
    }

    let y0 = strip.y0.into_inner();
    let y1 = strip.y1.into_inner();
    let xs = || strip.segs.iter().flat_map(|s| [s.x0, s.x1]);
    let x_max = xs().max().unwrap().into_inner();
    let x_min = xs().min().unwrap().into_inner();
    Rect::new(x_min, y0, x_max, y1)
}
