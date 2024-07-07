use std::sync::Arc;

use masonry::widget::MainAxisAlignment;
use ordered_float::NotNan;
use sweeps::{
    algorithms::strip::{strips_to_sweeps, sweep, Strip},
    sweep::{Segments, SweepLine},
};
use xilem::{
    view::{button, flex, label},
    Axis, Color, EventLoop, WidgetView, Xilem,
};

mod view;
mod widget;

type F = NotNan<f64>;

struct AppData {
    eps: F,
    sweep: Arc<SweepState>,
}

#[derive(Debug, Default, Clone)]
struct SweepState {
    segs: Segments<F>,
    strips: Vec<Strip<F>>,
    sweeps: Vec<SweepLine<F>>,
}

fn app_logic(data: &mut AppData) -> impl WidgetView<AppData> {
    let sweep = view::Sweep {
        state: Arc::clone(&data.sweep),
    };
    // TODO: there doesn't seem to currently be a way to stretch children on the main axis?
    // flex((flex(label("Placeholder")).direction(Axis::Vertical), sweep))
    //     .main_axis_alignment(MainAxisAlignment::Start)
    //     .cross_axis_alignment(masonry::widget::CrossAxisAlignment::Fill)
    //     .direction(Axis::Horizontal)
    sweep
}

fn main() {
    let segs = Segments::from_closed_cycle([
        (0.5, -1.0),
        (0.0, 0.0),
        (2.0, 0.3),
        (0.0, 1.0),
        (1.0, 1.2),
        (1.5, 0.1),
    ]);
    let eps = NotNan::try_from(0.1).unwrap();
    let strips = sweep(&segs, &eps);
    let sweeps = strips_to_sweeps(&strips, &segs);
    dbg!(&segs, &strips, &sweeps);
    let data = AppData {
        eps,
        sweep: Arc::new(SweepState {
            segs,
            strips,
            sweeps,
        }),
    };

    let app = Xilem::new(data, app_logic);
    app.run_windowed(EventLoop::with_user_event(), "Sweeper".into())
        .unwrap();
}
