use std::sync::Arc;

use xilem::{
    view::{Cx, Id, View, ViewMarker},
    widget::ChangeFlags,
    MessageResult,
};

use crate::{widget, SweepState};

pub struct Sweep {
    pub state: Arc<SweepState>,
}

impl<T> View<T> for Sweep {
    type State = ();

    type Element = crate::widget::Sweep;

    fn build(&self, _cx: &mut Cx) -> (Id, Self::State, Self::Element) {
        let id = Id::next();
        let state = Arc::default();
        (id, (), widget::Sweep::new(state))
    }

    fn rebuild(
        &self,
        _cx: &mut Cx,
        _prev: &Self,
        _id: &mut Id,
        _state: &mut Self::State,
        element: &mut Self::Element,
    ) -> ChangeFlags {
        if Arc::ptr_eq(&self.state, &element.state) {
            ChangeFlags::default()
        } else {
            element.state = Arc::clone(&self.state);
            ChangeFlags::PAINT
        }
    }

    fn message(
        &self,
        _id_path: &[Id],
        _state: &mut Self::State,
        _message: Box<dyn std::any::Any>,
        _app_state: &mut T,
    ) -> MessageResult<()> {
        MessageResult::Nop
    }
}

impl ViewMarker for Sweep {}
