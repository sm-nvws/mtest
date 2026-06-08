use std::cell::RefCell;

use crate::level::LevelVar;
use crate::term::{Name, TermData, TermId};

pub fn with_scope<F, R>(f: F) -> R
where
    F: for<'scope> FnOnce(Arena<'scope>) -> R,
{
    fn inner<'scope, F, R>(f: F) -> R
    where
        F: FnOnce(Arena<'scope>) -> R,
    {
        f(Arena::new())
    }
    inner(f)
}

pub struct Arena<'scope> {
    terms: RefCell<Vec<TermData<'scope>>>,
    _scope: std::marker::PhantomData<fn(&'scope ()) -> &'scope ()>,
}

impl<'scope> Arena<'scope> {
    fn new() -> Self {
        Self {
            terms: RefCell::new(Vec::new()),
            _scope: std::marker::PhantomData,
        }
    }

    fn alloc(&self, data: TermData<'scope>) -> TermId<'scope> {
        let mut terms = self.terms.borrow_mut();
        let index = terms.len();
        if index == terms.capacity() && index > 0 {
            terms.reserve(index);
        }
        terms.push(data);
        TermId::new(index)
    }

    pub fn get(&self, id: TermId<'scope>) -> TermData<'scope> {
        self.terms.borrow()[id.index()].clone()
    }

    pub fn var(&self, index: usize) -> TermId<'scope> {
        self.alloc(TermData::Var(index))
    }

    pub fn typ(&self, level: LevelVar) -> TermId<'scope> {
        self.alloc(TermData::Type(level))
    }

    pub fn pi(&self, dom: TermId<'scope>, cod: TermId<'scope>) -> TermId<'scope> {
        self.alloc(TermData::Pi(dom, cod))
    }

    pub fn lam(&self, param_ty: TermId<'scope>, body: TermId<'scope>) -> TermId<'scope> {
        self.alloc(TermData::Lam(param_ty, body))
    }

    pub fn app(&self, fun: TermId<'scope>, arg: TermId<'scope>) -> TermId<'scope> {
        self.alloc(TermData::App(fun, arg))
    }

    pub fn sigma(&self, fst_ty: TermId<'scope>, snd_ty: TermId<'scope>) -> TermId<'scope> {
        self.alloc(TermData::Sigma(fst_ty, snd_ty))
    }

    pub fn pair(&self, fst: TermId<'scope>, snd: TermId<'scope>) -> TermId<'scope> {
        self.alloc(TermData::Pair(fst, snd))
    }

    pub fn fst(&self, pair: TermId<'scope>) -> TermId<'scope> {
        self.alloc(TermData::Fst(pair))
    }

    pub fn snd(&self, pair: TermId<'scope>) -> TermId<'scope> {
        self.alloc(TermData::Snd(pair))
    }

    pub fn nat(&self) -> TermId<'scope> {
        self.alloc(TermData::Nat)
    }

    pub fn zero(&self) -> TermId<'scope> {
        self.alloc(TermData::Zero)
    }

    pub fn succ(&self, n: TermId<'scope>) -> TermId<'scope> {
        self.alloc(TermData::Succ(n))
    }

    pub fn nat_elim(
        &self,
        motive: TermId<'scope>,
        base: TermId<'scope>,
        step: TermId<'scope>,
        target: TermId<'scope>,
    ) -> TermId<'scope> {
        self.alloc(TermData::NatElim {
            motive,
            base,
            step,
            target,
        })
    }

    pub fn sigma_elim(
        &self,
        motive: TermId<'scope>,
        elim: TermId<'scope>,
        target: TermId<'scope>,
    ) -> TermId<'scope> {
        self.alloc(TermData::SigmaElim {
            motive,
            elim,
            target,
        })
    }

    pub fn ann(&self, term: TermId<'scope>, ty: TermId<'scope>) -> TermId<'scope> {
        self.alloc(TermData::Ann(term, ty))
    }

    pub fn konst(&self, name: Name) -> TermId<'scope> {
        self.alloc(TermData::Const(name))
    }
}
