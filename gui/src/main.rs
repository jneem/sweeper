use std::sync::Arc;

use ordered_float::NotNan;
use sweeps::{
    algorithms::strip::{strips_to_sweeps, sweep, Strip},
    sweep::{Segments, SweepLine},
};
use taffy::style::AlignItems;
use xilem::{
    vello::peniko::Color,
    view::{button, div, flex_column, flex_row, grid, Adapt, View},
    App, AppLauncher,
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

fn app_logic(data: &mut AppData) -> impl View<AppData> {
    let sweep = view::Sweep {
        state: Arc::clone(&data.sweep),
    };
    flex_row((
        flex_column(div("Placeholder")),
        grid(Some(sweep))
            .with_background_color(Color::WHITE)
            .with_style(|s| s.flex_grow = 1.0),
    ))
    .with_style(|s| {
        s.align_items = Some(AlignItems::Stretch);
    })
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

    let app = App::new(data, app_logic);
    AppLauncher::new(app).run();
}
