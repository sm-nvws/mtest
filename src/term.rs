use crate::level::LevelVar;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Name(pub String);

impl std::fmt::Display for Name {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}

#[derive(Clone, Debug)]
pub enum TermData<'scope> {
    Var(usize),
    Type(LevelVar),
    Pi(TermId<'scope>, TermId<'scope>),
    Lam(TermId<'scope>, TermId<'scope>),
    App(TermId<'scope>, TermId<'scope>),
    Sigma(TermId<'scope>, TermId<'scope>),
    Pair(TermId<'scope>, TermId<'scope>),
    Fst(TermId<'scope>),
    Snd(TermId<'scope>),
    Nat,
    Zero,
    Succ(TermId<'scope>),
    NatElim {
        motive: TermId<'scope>,
        base: TermId<'scope>,
        step: TermId<'scope>,
        target: TermId<'scope>,
    },
    SigmaElim {
        motive: TermId<'scope>,
        elim: TermId<'scope>,
        target: TermId<'scope>,
    },
    Ann(TermId<'scope>, TermId<'scope>),
    Const(Name),
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct TermId<'scope> {
    index: usize,
    _scope: std::marker::PhantomData<fn(&'scope ()) -> &'scope ()>,
}

impl<'scope> TermId<'scope> {
    pub(crate) fn new(index: usize) -> Self {
        Self {
            index,
            _scope: std::marker::PhantomData,
        }
    }

    pub fn index(self) -> usize {
        self.index
    }
}
