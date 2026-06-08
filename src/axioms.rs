use crate::arena::Arena;
use crate::check::fresh_level;
use crate::signature::Signature;
use crate::term::{Name, TermId};

pub struct Analysis<'scope> {
    pub cauchy_thm: TermId<'scope>,
    pub cauchy_proof: TermId<'scope>,
    pub mtest_stmt: TermId<'scope>,
    pub uniform_proof: TermId<'scope>,
    pub mtest_proof: TermId<'scope>,
}

fn register_axiom<'scope>(sig: &mut Signature<'scope>, name: &str, ty: TermId<'scope>) {
    sig.insert_axiom(Name(name.into()), ty);
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

fn uniform_conv<'scope>(
    arena: &Arena<'scope>,
    nat: TermId<'scope>,
    real: TermId<'scope>,
    fs: TermId<'scope>,
    f: TermId<'scope>,
) -> TermId<'scope> {
    let closeness = arena.app(
        arena.app(
            k(arena, "lt"),
            arena.app(
                k(arena, "abs"),
                arena.app(
                    arena.app(k(arena, "sub"), arena.app(arena.app(fs, arena.var(2)), arena.var(0))),
                    arena.app(f, arena.var(0)),
                ),
            ),
        ),
        arena.var(5),
    );
    let forall_x = arena.pi(real, closeness);
    let n_ge = arena.pi(
        arena.app(arena.app(k(arena, "nat_le"), arena.var(1)), arena.var(0)),
        forall_x,
    );
    let forall_n = arena.pi(nat, n_ge);
    let exists_n = arena.sigma(nat, forall_n);
    let eps_pos = arena.pi(
        arena.app(arena.app(k(arena, "lt"), k(arena, "zero")), arena.var(0)),
        exists_n,
    );
    arena.pi(real, eps_pos)
}

pub fn build_analysis<'scope>(
    arena: &Arena<'scope>,
    sig: &mut Signature<'scope>,
) -> Analysis<'scope> {
    register_axiom(sig, "Real", arena.typ(fresh_level()));
    register_axiom(sig, "Prop", arena.typ(fresh_level()));
    let real = k(arena, "Real");
    let prop = k(arena, "Prop");
    let nat = arena.nat();
    let seq = arr(arena, nat, real);
    let seq2 = arr(arena, nat, arr(arena, real, real));
    let fun_real = arr(arena, real, real);

    register_axiom(sig, "zero", real);
    register_axiom(sig, "one", real);
    register_axiom(sig, "add", arr(arena, real, arr(arena, real, real)));
    register_axiom(sig, "sub", arr(arena, real, arr(arena, real, real)));
    register_axiom(sig, "neg", arr(arena, real, real));
    register_axiom(sig, "abs", arr(arena, real, real));
    register_axiom(sig, "le", arr(arena, real, arr(arena, real, prop)));
    register_axiom(sig, "lt", arr(arena, real, arr(arena, real, prop)));
    register_axiom(sig, "nat_le", arr(arena, nat, arr(arena, nat, prop)));

    register_axiom(
        sig,
        "choice",
        arr(arena, prop, arr(arena, prop, arr(arena, arr(arena, prop, prop), prop))),
    );

    register_axiom(sig, "cauchy", arr(arena, seq, prop));
    register_axiom(sig, "conv", arr(arena, seq, arr(arena, real, prop)));
    register_axiom(sig, "conv_exists", arr(arena, seq, prop));

    let cauchy_thm = dep_pi(arena, seq, |s| {
        arr(
            arena,
            arena.app(k(arena, "cauchy"), s),
            arena.app(k(arena, "conv_exists"), s),
        )
    });
    register_axiom(sig, "complete", cauchy_thm);
    register_axiom(sig, "cauchy_crit", cauchy_thm);
    register_axiom(sig, "cauchy_pf", cauchy_thm);

    let uniform_ty = dep_pi(arena, seq2, |fs| {
        dep_pi(arena, fun_real, |f| uniform_conv(arena, nat, real, fs, f))
    });
    register_axiom(sig, "uniform", uniform_ty);

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
    let rest_ty = arena.sigma(
        seq,
        arena.sigma(arena.app(k(arena, "cauchy"), arena.var(0)), dominated),
    );
    let tail_ty = arena.sigma(fun_real, rest_ty);
    let mtest_hyp = arena.sigma(seq2, tail_ty);

    let mtest_stmt = dep_pi(arena, mtest_hyp, |h| {
        let motive = arena.lam(
            mtest_hyp,
            arena.app(
                arena.app(k(arena, "uniform"), arena.fst(arena.var(0))),
                arena.fst(arena.snd(arena.var(0))),
            ),
        );
        let elim = arena.lam(
            seq2,
            arena.lam(
                tail_ty,
                arena.sigma_elim(
                    arena.lam(
                        tail_ty,
                        arena.app(
                            arena.app(k(arena, "uniform"), arena.var(1)),
                            arena.fst(arena.var(0)),
                        ),
                    ),
                    arena.lam(
                        fun_real,
                        arena.lam(
                            rest_ty,
                            arena.app(
                                arena.app(k(arena, "uniform"), arena.var(2)),
                                arena.var(1),
                            ),
                        ),
                    ),
                    arena.var(0),
                ),
            ),
        );
        arena.sigma_elim(motive, elim, h)
    });
    register_axiom(sig, "uniform_from_cauchy", mtest_stmt);
    register_axiom(sig, "mtest", mtest_stmt);

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
