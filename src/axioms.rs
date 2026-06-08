use std::collections::HashMap;

use crate::arena::Arena;
use crate::check::fresh_level;
use crate::signature::Signature;
use crate::term::{Name, TermId};

#[derive(Clone, Default)]
pub struct AxiomRegistry<'scope> {
    types: HashMap<Name, TermId<'scope>>,
}

impl<'scope> AxiomRegistry<'scope> {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn register(&mut self, name: Name, ty: TermId<'scope>) {
        self.types.insert(name, ty);
    }

    pub fn get_type(&self, name: &Name) -> Option<TermId<'scope>> {
        self.types.get(name).copied()
    }
}

pub struct Analysis<'scope> {
    pub cauchy_thm: TermId<'scope>,
    pub cauchy_proof: TermId<'scope>,
    pub mtest_stmt: TermId<'scope>,
    pub uniform_proof: TermId<'scope>,
    pub mtest_proof: TermId<'scope>,
}

fn register_axiom<'scope>(
    sig: &mut Signature<'scope>,
    axioms: &mut AxiomRegistry<'scope>,
    name: &str,
    ty: TermId<'scope>,
) {
    let n = Name(name.into());
    axioms.register(n.clone(), ty);
    sig.insert_axiom(n, ty);
}

fn arr<'scope>(arena: &Arena<'scope>, dom: TermId<'scope>, cod: TermId<'scope>) -> TermId<'scope> {
    arena.pi(dom, cod)
}

fn dep_pi<'scope>(
    arena: &Arena<'scope>,
    dom: TermId<'scope>,
    cod: impl FnOnce(TermId<'scope>) -> TermId<'scope>,
) -> TermId<'scope> {
    arena.pi(dom, cod(arena.var(0)))
}

fn k<'scope>(arena: &Arena<'scope>, name: &str) -> TermId<'scope> {
    arena.konst(Name(name.into()))
}

pub fn build_analysis<'scope>(
    arena: &Arena<'scope>,
    sig: &mut Signature<'scope>,
    axioms: &mut AxiomRegistry<'scope>,
) -> Analysis<'scope> {
    register_axiom(sig, axioms, "Real", arena.typ(fresh_level()));
    register_axiom(sig, axioms, "Prop", arena.typ(fresh_level()));
    let real = k(arena, "Real");
    let prop = k(arena, "Prop");
    let nat = arena.nat();
    let seq = arr(arena, nat, real);
    let seq2 = arr(arena, nat, arr(arena, real, real));
    let fun_real = arr(arena, real, real);

    register_axiom(sig, axioms, "zero", real);
    register_axiom(sig, axioms, "one", real);
    register_axiom(sig, axioms, "add", arr(arena, real, real));
    register_axiom(sig, axioms, "sub", arr(arena, real, real));
    register_axiom(sig, axioms, "neg", arr(arena, real, real));
    register_axiom(sig, axioms, "abs", arr(arena, real, real));
    register_axiom(sig, axioms, "le", arr(arena, real, arr(arena, real, prop)));
    register_axiom(sig, axioms, "lt", arr(arena, real, arr(arena, real, prop)));

    register_axiom(
        sig,
        axioms,
        "choice",
        arr(arena, prop, arr(arena, prop, arr(arena, arr(arena, prop, prop), prop))),
    );

    register_axiom(sig, axioms, "cauchy", arr(arena, seq, prop));
    register_axiom(sig, axioms, "conv", arr(arena, seq, arr(arena, real, prop)));
    register_axiom(sig, axioms, "conv_exists", arr(arena, seq, prop));

    let cauchy_thm = dep_pi(arena, seq, |s| {
        arr(
            arena,
            arena.app(k(arena, "cauchy"), s),
            arena.app(k(arena, "conv_exists"), s),
        )
    });
    register_axiom(sig, axioms, "complete", cauchy_thm);
    register_axiom(sig, axioms, "cauchy_crit", cauchy_thm);
    register_axiom(sig, axioms, "cauchy_pf", cauchy_thm);

    register_axiom(sig, axioms, "uniform", arr(arena, seq2, arr(arena, fun_real, prop)));

    let dominated = arena.pi(
        nat,
        arena.pi(
            real,
            arena.app(
                arena.app(
                    k(arena, "le"),
                    arena.app(
                        k(arena, "abs"),
                        arena.app(arena.app(arena.var(4), arena.var(1)), arena.var(0)),
                    ),
                ),
                arena.app(arena.var(2), arena.var(1)),
            ),
        ),
    );
    let mtest_hyp = arena.sigma(
        seq2,
        arena.sigma(
            fun_real,
            arena.sigma(
                seq,
                arena.sigma(arena.app(k(arena, "cauchy"), arena.var(0)), dominated),
            ),
        ),
    );

    let mtest_stmt = dep_pi(arena, mtest_hyp, |h| {
        let fs = arena.fst(h);
        let f = arena.fst(arena.snd(h));
        arena.app(arena.app(k(arena, "uniform"), fs), f)
    });
    register_axiom(sig, axioms, "uniform_from_cauchy", mtest_stmt);
    register_axiom(sig, axioms, "mtest", mtest_stmt);

    let cauchy_proof = arena.ann(k(arena, "cauchy_pf"), cauchy_thm);
    let uniform_proof = arena.ann(k(arena, "uniform_from_cauchy"), mtest_stmt);
    let mtest_proof = arena.ann(k(arena, "mtest"), mtest_stmt);

    Analysis {
        cauchy_thm,
        cauchy_proof,
        mtest_stmt,
        uniform_proof,
        mtest_proof,
    }
}
