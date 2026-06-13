use spartan_rs::arena::with_scope;
use spartan_rs::axioms::build_analysis;
use spartan_rs::check::{check, reset_levels, solve_levels};
use spartan_rs::context::Context;
use spartan_rs::env::Env;
use spartan_rs::level::{ConstraintSet, Level, LevelError};
use spartan_rs::norm::{eval, normalize};
use spartan_rs::signature::Signature;
use spartan_rs::term::TermData;
use spartan_rs::value::Value;

#[test]
fn analysis_typechecks() {
    reset_levels();
    with_scope(|arena| {
        let mut sig = Signature::new();
        let ctx = Context::new();
        let env = Env::new();
        let analysis = build_analysis(&arena, &mut sig);

        let steps = [
            (analysis.cauchy_proof, analysis.cauchy_thm),
            (analysis.uniform_proof, analysis.mtest_stmt),
            (analysis.mtest_proof, analysis.mtest_stmt),
        ];
        for (proof, stmt) in steps {
            let stmt_val = eval(&arena, &sig, stmt, &env);
            check(&arena, &sig, &ctx, &env, proof, stmt_val).expect("proof should type-check");
        }
        solve_levels().expect("levels should be consistent");
    });
}

#[test]
fn eval_and_normalize_nat() {
    with_scope(|arena| {
        let sig = Signature::new();
        let env = Env::new();

        let two = arena.succ(arena.succ(arena.zero()));
        match eval(&arena, &sig, two, &env) {
            Value::VSucc(inner) => match *inner {
                Value::VSucc(innermost) => assert!(matches!(*innermost, Value::VZero)),
                other => panic!("expected VSucc(VZero), got {other:?}"),
            },
            other => panic!("expected VSucc, got {other:?}"),
        }

        // Normalizing a closed numeral is the identity on its structure.
        let normalized = normalize(&arena, &sig, &env, two);
        assert!(matches!(arena.get(normalized), TermData::Succ(_)));
    });
}

#[test]
fn solver_accepts_consistent_constraints() {
    let mut cs = ConstraintSet::new();
    let a = cs.fresh();
    let b = cs.fresh();
    cs.subtype(Level::var(a), Level::var(b));
    cs.subtype(Level::var(b), Level::var(a).succ());
    assert!(cs.solve().is_ok());
}

#[test]
fn solver_rejects_zero_equals_succ() {
    let mut cs = ConstraintSet::new();
    cs.equate(Level::Zero, Level::Zero.succ());
    assert!(matches!(cs.solve(), Err(LevelError::Inconsistent)));
}

#[test]
fn solver_terminates_on_variable_cycle() {
    let mut cs = ConstraintSet::new();
    let a = cs.fresh();
    let b = cs.fresh();
    cs.equate(Level::var(a), Level::var(b));
    cs.equate(Level::var(b), Level::var(a));
    assert!(cs.solve().is_ok());
}
