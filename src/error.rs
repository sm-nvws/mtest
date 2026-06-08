use miette::Diagnostic;
use thiserror::Error;

use crate::arena::Arena;
use crate::level::LevelError;
use crate::term::{Name, TermId};
use crate::value::Value;

#[derive(Debug, Error, Diagnostic)]
pub enum TyError {
    #[error("type mismatch at {term}: expected {expected}, found {found}")]
    #[diagnostic(code(spartan::type_mismatch))]
    TypeMismatch {
        term: String,
        expected: String,
        found: String,
    },

    #[error("cannot infer type for {term}")]
    #[diagnostic(code(spartan::cannot_infer))]
    CannotInfer { term: String },

    #[error("unknown constant `{name}` at {term}")]
    #[diagnostic(code(spartan::unknown_const))]
    UnknownConst { term: String, name: Name },

    #[error("universe level error: {0}")]
    #[diagnostic(code(spartan::level))]
    Level(#[from] LevelError),

    #[error("definitional equality failed at {term}: {left} vs {right}")]
    #[diagnostic(code(spartan::def_eq))]
    DefEq {
        term: String,
        left: String,
        right: String,
    },

    #[error("invalid elimination at {term}")]
    #[diagnostic(code(spartan::elim))]
    InvalidElim { term: String },
}

impl TyError {
    pub fn type_mismatch<'scope>(
        arena: &Arena<'scope>,
        term: TermId<'scope>,
        expected: impl Into<String>,
        found: impl Into<String>,
    ) -> Self {
        Self::TypeMismatch {
            term: term_display(arena, term),
            expected: expected.into(),
            found: found.into(),
        }
    }

    pub fn cannot_infer<'scope>(arena: &Arena<'scope>, term: TermId<'scope>) -> Self {
        Self::CannotInfer {
            term: term_display(arena, term),
        }
    }

    pub fn unknown_const<'scope>(
        arena: &Arena<'scope>,
        term: TermId<'scope>,
        name: Name,
    ) -> Self {
        Self::UnknownConst {
            term: term_display(arena, term),
            name,
        }
    }

    pub fn invalid_elim<'scope>(arena: &Arena<'scope>, term: TermId<'scope>) -> Self {
        Self::InvalidElim {
            term: term_display(arena, term),
        }
    }
}

pub fn value_display<'scope>(v: &Value<'scope>) -> String {
    format!("{v:?}")
}

pub fn term_display<'scope>(arena: &Arena<'scope>, t: TermId<'scope>) -> String {
    format!("{:?}", arena.get(t))
}
