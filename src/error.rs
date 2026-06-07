use miette::Diagnostic;
use thiserror::Error;

use crate::arena::Arena;
use crate::level::LevelError;
use crate::term::{Name, TermId};
use crate::value::Value;

#[derive(Debug, Error, Diagnostic)]
pub enum TyError<'scope> {
    #[error("expected type {expected}, found {found}")]
    #[diagnostic(code(spartan::type_mismatch))]
    TypeMismatch {
        term: TermId<'scope>,
        expected: String,
        found: String,
    },

    #[error("cannot infer type for term")]
    #[diagnostic(code(spartan::cannot_infer))]
    CannotInfer { term: TermId<'scope> },

    #[error("unknown constant `{name}`")]
    #[diagnostic(code(spartan::unknown_const))]
    UnknownConst {
        term: TermId<'scope>,
        name: Name,
    },

    #[error("universe level error: {0}")]
    #[diagnostic(code(spartan::level))]
    Level(#[from] LevelError),

    #[error("definitional equality failed")]
    #[diagnostic(code(spartan::def_eq))]
    DefEq {
        term: TermId<'scope>,
        left: String,
        right: String,
    },

    #[error("invalid elimination form")]
    #[diagnostic(code(spartan::elim))]
    InvalidElim { term: TermId<'scope> },
}

pub fn value_display<'scope>(v: &Value<'scope>) -> String {
    format!("{v:?}")
}

pub fn term_display<'scope>(arena: &Arena<'scope>, t: TermId<'scope>) -> String {
    format!("{:?}", arena.get(t))
}
