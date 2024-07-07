use std::sync::Arc;

use accesskit::Role;
use masonry::{
    kurbo::ParamCurveNearest,
    parley::{self, FontContext, Layout, LayoutContext},
    text2::{TextBrush, TextLayout},
    vello::{
        kurbo::{Affine, Circle, Line, Point, Rect, Stroke},
        peniko::{Brush, Color, Fill},
    },
    widget::WidgetRef,
    StatusChange,
};
use masonry::{
    vello::Scene, BoxConstraints, EventCtx, LayoutCtx, LifeCycle, LifeCycleCtx, PaintCtx,
    PointerEvent, Size, Widget,
};
use ordered_float::NotNan;
use smallvec::SmallVec;
use sweeps::{
    algorithms::strip::{Strip, StripSeg},
    sweep::{SweepLine, SweepLineSeg},
};

use crate::{SweepState, F};

pub struct Sweep {
    pub state: Arc<SweepState>,
    hot_seg: Option<StripSeg<F>>,
    transform: Affine,
    layout: Option<TextLayout<String>>,
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

        if let Some((_line, seg)) = self
            .state
            .strips
            .iter()
            .flat_map(|strip| {
                strip.segs.iter().map(|seg| {
                    (
                        Line::new(
                            (seg.x0.into_inner(), strip.y0.into_inner()),
                            (seg.x1.into_inner(), strip.y1.into_inner()),
                        ),
                        seg,
                    )
                })
            })
            .min_by_key(|(line, _seg)| NotNan::new(line.nearest(p, 0.0).distance_sq).unwrap())
        {
            // TODO: put a threshold -- make sure it's actually close
            Some(seg.clone())
        } else {
            None
        }
    }

    fn draw_point(&self, scene: &mut Scene, p: Point) {
        let circle = Circle::new(p, 0.06);
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

    fn draw_strip(&self, scene: &mut Scene, strip: &Strip<F>) {
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

    fn draw_sweep_location(&self, scene: &mut Scene, y: F, bbox: Rect) {
        let y = y.into_inner();
        let color = Color::DIM_GRAY;
        scene.stroke(
            &Stroke::new(0.01).with_dashes(0.0, [0.01, 0.02]),
            self.transform,
            color,
            None,
            &Line::new((bbox.x0, y), (bbox.x1, y)),
        );
    }

    fn draw_sweep(&self, scene: &mut Scene, sweep: &SweepLine<F>) {
        for entry in &sweep.segs {
            if let SweepLineSeg::EnterExit(x0, x1) = entry.x {
                let p0 = Point::new(x0.into_inner(), sweep.y.into_inner());
                let p1 = Point::new(x1.into_inner(), sweep.y.into_inner());

                let color = Color::BLACK;
                scene.stroke(
                    &Stroke::new(0.025),
                    self.transform,
                    color,
                    None,
                    &Line::new(p0, p1),
                );
            }
        }
    }

    fn compute_seg_layout(&mut self, fc: &mut FontContext, lc: &mut LayoutContext<TextBrush>) {
        let Some(hot_seg) = self.hot_seg.as_ref() else {
            self.layout = None;
            return;
        };

        let text = format!(
            "seg {}, {:.3} -- {:.3}",
            hot_seg.idx.0, hot_seg.x0, hot_seg.x1
        );
        let mut layout = TextLayout::new(text, 16.0);
        layout.set_brush(Color::BLACK);
        layout.rebuild(fc, lc);
        self.layout = Some(layout);
    }
}

impl Widget for Sweep {
    fn on_pointer_event(&mut self, ctx: &mut EventCtx, event: &PointerEvent) {
        if let PointerEvent::PointerMove(ev) = event {
            let p = Point::new(ev.position.x, ev.position.y);
            let hot_seg = self.seg_at(p);
            if hot_seg != self.hot_seg {
                self.hot_seg = hot_seg;
                ctx.request_layout();
                ctx.request_paint();
            }
        }
        //dbg!(event);
    }

    fn on_text_event(&mut self, _ctx: &mut EventCtx, _event: &masonry::TextEvent) {
        // If focused on a link and enter pressed, follow it?
        // TODO: This sure looks like each link needs its own widget, although I guess the challenge there is
        // that the bounding boxes can go e.g. across line boundaries?
    }

    fn on_access_event(&mut self, _ctx: &mut EventCtx, _event: &masonry::AccessEvent) {}

    fn on_status_change(&mut self, ctx: &mut LifeCycleCtx, event: &StatusChange) {
        if matches!(event, StatusChange::HotChanged(_)) {
            ctx.request_paint();
        }
    }

    fn lifecycle(&mut self, _ctx: &mut LifeCycleCtx, _event: &LifeCycle) {}

    fn layout(&mut self, ctx: &mut LayoutCtx, bc: &BoxConstraints) -> Size {
        let (fc, lc) = ctx.text_contexts();
        self.compute_seg_layout(fc, lc);
        bc.constrain((500.0, 500.0))
    }

    fn paint(&mut self, ctx: &mut PaintCtx, scene: &mut Scene) {
        let size = ctx.size();
        let center = (size.to_vec2() / 2.0).to_point();
        scene.fill(
            Fill::NonZero,
            Affine::IDENTITY,
            Color::WHITE,
            None,
            &size.to_rect(),
        );

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
            for sweep in &self.state.sweeps {
                self.draw_sweep_location(scene, sweep.y, bbox)
            }
            for strip in &self.state.strips {
                self.draw_strip(scene, strip);
            }
            for sweep in &self.state.sweeps {
                self.draw_sweep(scene, sweep)
            }
        }

        if let Some(layout) = self.layout.as_mut() {
            layout.draw(scene, Point::new(0.0, 0.0));
        }
    }

    fn accessibility_role(&self) -> Role {
        Role::Canvas
    }

    fn accessibility(&mut self, ctx: &mut masonry::AccessCtx) {}

    fn children(&self) -> SmallVec<[WidgetRef<'_, dyn Widget>; 16]> {
        SmallVec::new()
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
