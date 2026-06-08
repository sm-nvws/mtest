use crate::env::Env;
use crate::level::LevelVar;
use crate::term::{Name, TermId};

#[derive(Clone, Debug)]
pub enum Value<'scope> {
    VPi(TermId<'scope>, Env<'scope>),
    VLam(TermId<'scope>, Env<'scope>),
    VSigma(TermId<'scope>, Env<'scope>),
    VPair(Box<Value<'scope>>, Box<Value<'scope>>),
    VNat,
    VZero,
    VSucc(Box<Value<'scope>>),
    VType(LevelVar),
    VConst(Name, Box<Value<'scope>>),
    VNeutral(Neutral<'scope>),
}

#[derive(Clone, Debug)]
pub enum Neutral<'scope> {
    NVar(usize),
    NApp(Box<Neutral<'scope>>, Box<Value<'scope>>),
    NFst(Box<Neutral<'scope>>),
    NSnd(Box<Neutral<'scope>>),
    NNatElim {
        motive: Box<Value<'scope>>,
        base: Box<Value<'scope>>,
        step: Box<Value<'scope>>,
        target: Box<Neutral<'scope>>,
    },
    NSigmaElim {
        motive: Box<Value<'scope>>,
        elim: Box<Value<'scope>>,
        target: Box<Neutral<'scope>>,
    },
    NConst(Name),
}
