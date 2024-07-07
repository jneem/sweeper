use std::sync::Arc;

use xilem::{Pod, ViewCtx, WidgetView};
use xilem_core::{MessageResult, Mut, View, ViewId};

use crate::{widget, SweepState};

pub struct Sweep {
    pub state: Arc<SweepState>,
}

impl<State, Action> View<State, Action, ViewCtx> for Sweep {
    type ViewState = ();

    type Element = Pod<crate::widget::Sweep>;

    fn build(&self, _ctx: &mut ViewCtx) -> (Self::Element, Self::ViewState) {
        (Pod::new(widget::Sweep::new(Arc::clone(&self.state))), ())
    }

    fn rebuild<'el>(
        &self,
        _prev: &Self,
        _state: &mut Self::ViewState,
        ctx: &mut ViewCtx,
        element: Mut<'el, Self::Element>,
    ) -> Mut<'el, Self::Element> {
        if !Arc::ptr_eq(&self.state, &element.widget.state) {
            element.widget.state = Arc::clone(&self.state);
            ctx.mark_changed();
        }
        element
    }

    fn message(
        &self,
        _state: &mut Self::ViewState,
        _id_path: &[ViewId],
        _message: xilem_core::DynMessage,
        _app_state: &mut State,
    ) -> MessageResult<Action> {
        MessageResult::Nop
    }

    fn teardown(
        &self,
        _view_state: &mut Self::ViewState,
        _ctx: &mut ViewCtx,
        _element: xilem_core::Mut<'_, Self::Element>,
    ) {
    }
}

//impl ViewMarker for Sweep {}
