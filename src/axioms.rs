use std::collections::HashMap;

use crate::arena::Arena;
use crate::level::ConstraintSet;
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
    levels: &mut ConstraintSet,
) -> Analysis<'scope> {
    let prop = arena.typ(levels.fresh());
    let real = arena.typ(levels.fresh());
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
    register_axiom(sig, axioms, "le", arr(arena, real, prop));
    register_axiom(sig, axioms, "lt", arr(arena, real, prop));

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
    register_axiom(sig, axioms, "mtest_hyp", prop);
    register_axiom(sig, axioms, "hyp_fs", arr(arena, k(arena, "mtest_hyp"), seq2));
    register_axiom(sig, axioms, "hyp_f", arr(arena, k(arena, "mtest_hyp"), fun_real));
    register_axiom(sig, axioms, "hyp_major", arr(arena, k(arena, "mtest_hyp"), seq));
    register_axiom(sig, axioms, "hyp_bound", arr(arena, k(arena, "mtest_hyp"), arr(arena, real, prop)));
    register_axiom(
        sig,
        axioms,
        "hyp_cauchy",
        dep_pi(arena, k(arena, "mtest_hyp"), |h| {
            arena.app(k(arena, "cauchy"), arena.app(k(arena, "hyp_major"), h))
        }),
    );

    let mtest_stmt = dep_pi(arena, k(arena, "mtest_hyp"), |h| {
        arena.app(
            arena.app(k(arena, "uniform"), arena.app(k(arena, "hyp_fs"), h)),
            arena.app(k(arena, "hyp_f"), h),
        )
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
