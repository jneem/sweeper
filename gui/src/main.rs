use std::sync::Arc;

use ordered_float::NotNan;
use sweeps::{
    algorithms::strip::{sweep, Strip},
    geom::{Point, Segment},
    sweep::Segments,
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

fn cyclic_pairs<T>(xs: &[T]) -> impl Iterator<Item = (&T, &T)> {
    xs.windows(2)
        .map(|pair| (&pair[0], &pair[1]))
        .chain(xs.last().zip(xs.first()))
}

fn main() {
    let segs = Segments {
        segs: cyclic_pairs(&[
            (0.5, -1.0),
            (0.0, 0.0),
            (2.0, 0.3),
            (0.0, 1.0),
            (1.0, 1.2),
            (1.5, 0.1),
        ])
        .map(|(p, q)| {
            let p = Point::<F>::new(p.0.try_into().unwrap(), p.1.try_into().unwrap());
            let q = Point::<F>::new(q.0.try_into().unwrap(), q.1.try_into().unwrap());
            Segment {
                start: p.clone().min(q.clone()),
                end: p.max(q),
            }
        })
        .collect(),
        contour_prev: vec![],
        contour_next: vec![],
    };
    let eps = NotNan::try_from(0.1).unwrap();
    let strips = sweep(&segs, &eps);
    dbg!(&segs, &strips);
    let data = AppData {
        eps,
        sweep: Arc::new(SweepState { segs, strips }),
    };

    let app = App::new(data, app_logic);
    AppLauncher::new(app).run();
}
