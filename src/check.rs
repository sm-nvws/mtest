use std::cell::RefCell;

use crate::arena::Arena;
use crate::axioms::AxiomRegistry;
use crate::context::Context;
use crate::env::Env;
use crate::error::{term_display, value_display, TyError};
use crate::level::{ConstraintSet, Level, LevelVar};
use crate::norm::{def_eq, eval};
use crate::signature::{Entry, Signature};
use crate::term::TermData;
use crate::term::TermId;
use crate::value::{Neutral, Value};

thread_local! {
    static LEVELS: RefCell<ConstraintSet> = RefCell::new(ConstraintSet::new());
}

pub fn solve_levels() -> Result<(), crate::level::LevelError> {
    LEVELS.with(|cell| cell.borrow_mut().solve())
}

pub fn reset_levels() {
    LEVELS.with(|cell| *cell.borrow_mut() = ConstraintSet::new());
}

pub fn fresh_level() -> LevelVar {
    levels_mut(|levels| levels.fresh())
}

fn levels_mut<F, R>(f: F) -> R
where
    F: FnOnce(&mut ConstraintSet) -> R,
{
    LEVELS.with(|cell| f(&mut cell.borrow_mut()))
}

pub fn check<'scope>(
    arena: &Arena<'scope>,
    sig: &Signature<'scope>,
    axioms: &AxiomRegistry<'scope>,
    ctx: &Context<'scope>,
    env: &Env<'scope>,
    term: TermId<'scope>,
    ty: Value<'scope>,
) -> Result<(), TyError<'scope>> {
    levels_mut(|levels| check_inner(arena, sig, axioms, ctx, env, levels, term, ty))
}

fn check_inner<'scope>(
    arena: &Arena<'scope>,
    sig: &Signature<'scope>,
    axioms: &AxiomRegistry<'scope>,
    ctx: &Context<'scope>,
    env: &Env<'scope>,
    levels: &mut ConstraintSet,
    term: TermId<'scope>,
    ty: Value<'scope>,
) -> Result<(), TyError<'scope>> {
    match arena.get(term) {
        TermData::Ann(t, ty_term) => {
            let expected = eval(arena, sig, ty_term, env);
            if !def_eq(arena, sig, env, levels, &expected, &ty) {
                return Err(TyError::TypeMismatch {
                    term,
                    expected: value_display(&ty),
                    found: value_display(&expected),
                });
            }
            check_inner(arena, sig, axioms, ctx, env, levels, t, ty)
        }
        TermData::Lam(param_ty, body) => match &ty {
            Value::VPi(pi_id, pi_env) => {
                let (dom, cod) = pi_parts(arena, *pi_id)?;
                let dom_val = eval(arena, sig, dom, env);
                let param_ty_val = eval(arena, sig, param_ty, env);
                if !def_eq(arena, sig, env, levels, &param_ty_val, &dom_val) {
                    return Err(TyError::TypeMismatch {
                        term,
                        expected: value_display(&dom_val),
                        found: term_display(arena, param_ty),
                    });
                }
                let new_ctx = ctx.extend(dom_val);
                let new_env = env.extend(Value::VNeutral(Neutral::NVar(env.len())));
                let cod_env = if pi_env.len() > 0 && pi_env.len() == env.len() {
                    pi_env
                } else {
                    &pi_env.extend(Value::VNeutral(Neutral::NVar(pi_env.len())))
                };
                let cod_val = eval(arena, sig, cod, cod_env);
                check_inner(arena, sig, axioms, &new_ctx, &new_env, levels, body, cod_val)
            }
            _ => Err(TyError::TypeMismatch {
                term,
                expected: "Π-type".into(),
                found: value_display(&ty),
            }),
        },
        TermData::Pair(fst, snd) => match &ty {
            Value::VSigma(sig_id, env_sig) => {
                let (a, b) = sigma_parts(arena, *sig_id)?;
                let fst_ty = eval(arena, sig, a, env_sig);
                check_inner(arena, sig, axioms, ctx, env, levels, fst, fst_ty)?;
                let fst_val = eval(arena, sig, fst, env);
                let snd_ty = eval(arena, sig, b, &env_sig.extend(fst_val));
                check_inner(arena, sig, axioms, ctx, env, levels, snd, snd_ty)
            }
            _ => Err(TyError::TypeMismatch {
                term,
                expected: "Σ-type".into(),
                found: value_display(&ty),
            }),
        },
        TermData::Zero => {
            if !def_eq(arena, sig, env, levels, &ty, &Value::VNat) {
                return Err(TyError::TypeMismatch {
                    term,
                    expected: value_display(&ty),
                    found: "Nat".into(),
                });
            }
            Ok(())
        }
        TermData::Succ(n) => {
            if !def_eq(arena, sig, env, levels, &ty, &Value::VNat) {
                return Err(TyError::TypeMismatch {
                    term,
                    expected: value_display(&ty),
                    found: "Nat".into(),
                });
            }
            check_inner(arena, sig, axioms, ctx, env, levels, n, Value::VNat)
        }
        TermData::NatElim {
            motive,
            base,
            step,
            target,
        } => check_nat_elim(
            arena, sig, axioms, ctx, env, levels, term, ty, motive, base, step, target,
        ),
        _ => {
            let inferred = infer_inner(arena, sig, axioms, ctx, env, levels, term)?;
            if !def_eq(arena, sig, env, levels, &inferred, &ty) {
                return Err(TyError::TypeMismatch {
                    term,
                    expected: value_display(&ty),
                    found: value_display(&inferred),
                });
            }
            Ok(())
        }
    }
}

pub fn infer<'scope>(
    arena: &Arena<'scope>,
    sig: &Signature<'scope>,
    axioms: &AxiomRegistry<'scope>,
    ctx: &Context<'scope>,
    env: &Env<'scope>,
    term: TermId<'scope>,
) -> Result<Value<'scope>, TyError<'scope>> {
    levels_mut(|levels| infer_inner(arena, sig, axioms, ctx, env, levels, term))
}

fn infer_inner<'scope>(
    arena: &Arena<'scope>,
    sig: &Signature<'scope>,
    axioms: &AxiomRegistry<'scope>,
    ctx: &Context<'scope>,
    env: &Env<'scope>,
    levels: &mut ConstraintSet,
    term: TermId<'scope>,
) -> Result<Value<'scope>, TyError<'scope>> {
    match arena.get(term) {
        TermData::Var(i) => Ok(ctx.lookup(i).clone()),
        TermData::Type(l) => {
            let lift = levels.fresh();
            levels.subtype(Level::var(l), Level::var(lift).succ());
            Ok(Value::VType(lift))
        }
        TermData::Pi(a, b) => {
            let a_ty = infer_inner(arena, sig, axioms, ctx, env, levels, a)?;
            match a_ty {
                Value::VType(l_dom) => {
                    let new_ctx = ctx.extend(Value::VType(l_dom));
                    let new_env = env.extend(Value::VNeutral(Neutral::NVar(env.len())));
                    let b_ty = infer_inner(arena, sig, axioms, &new_ctx, &new_env, levels, b)?;
                    match b_ty {
                        Value::VType(l_cod) => {
                            let lvl = levels.fresh();
                            levels.subtype(Level::var(l_cod), Level::var(lvl));
                            Ok(Value::VType(lvl))
                        }
                        _ => Err(TyError::TypeMismatch {
                            term,
                            expected: "universe".into(),
                            found: value_display(&b_ty),
                        }),
                    }
                }
                _ => {
                    let new_ctx = ctx.extend(a_ty.clone());
                    let new_env = env.extend(Value::VNeutral(Neutral::NVar(env.len())));
                    let _cod = infer_inner(arena, sig, axioms, &new_ctx, &new_env, levels, b)?;
                    let pi_id = arena.pi(a, b);
                    Ok(Value::VPi(pi_id, env.clone()))
                }
            }
        }
        TermData::Lam(param_ty, body) => {
            let dom = eval(arena, sig, param_ty, env);
            let new_ctx = ctx.extend(dom.clone());
            let new_env = env.extend(Value::VNeutral(Neutral::NVar(env.len())));
            let _cod = infer_inner(arena, sig, axioms, &new_ctx, &new_env, levels, body)?;
            let pi_id = arena.pi(param_ty, body);
            Ok(Value::VPi(pi_id, env.clone()))
        }
        TermData::App(f, x) => {
            let fun_ty = infer_inner(arena, sig, axioms, ctx, env, levels, f)?;
            app_infer(arena, sig, axioms, ctx, env, levels, term, f, x, fun_ty)
        }
        TermData::Sigma(a, b) => {
            let a_ty = infer_inner(arena, sig, axioms, ctx, env, levels, a)?;
            match a_ty {
                Value::VType(l1) => {
                    let new_ctx = ctx.extend(Value::VType(l1));
                    let new_env = env.extend(Value::VNeutral(Neutral::NVar(env.len())));
                    let b_ty = infer_inner(arena, sig, axioms, &new_ctx, &new_env, levels, b)?;
                    match b_ty {
                        Value::VType(l2) => {
                            levels.subtype(Level::var(l1), Level::var(l2));
                            Ok(Value::VType(l2))
                        }
                        _ => Err(TyError::TypeMismatch {
                            term,
                            expected: "universe".into(),
                            found: value_display(&b_ty),
                        }),
                    }
                }
                _ => Err(TyError::TypeMismatch {
                    term,
                    expected: "universe".into(),
                    found: "Σ-type".into(),
                }),
            }
        }
        TermData::Pair(_, _) => Err(TyError::CannotInfer { term }),
        TermData::Fst(p) => {
            let pair_ty = infer_inner(arena, sig, axioms, ctx, env, levels, p)?;
            match pair_ty {
                Value::VSigma(sig_id, env_sig) => {
                    let (a, _) = sigma_parts(arena, sig_id)?;
                    Ok(eval(arena, sig, a, &env_sig))
                }
                _ => Err(TyError::TypeMismatch {
                    term,
                    expected: "Σ-type".into(),
                    found: value_display(&pair_ty),
                }),
            }
        }
        TermData::Snd(p) => {
            let pair_ty = infer_inner(arena, sig, axioms, ctx, env, levels, p)?;
            match pair_ty {
                Value::VSigma(sig_id, env_sig) => {
                    let (_a, b) = sigma_parts(arena, sig_id)?;
                    let pair_val = eval(arena, sig, p, env);
                    let fst_val = match pair_val {
                        Value::VPair(f, _) => *f,
                        _ => return Err(TyError::CannotInfer { term }),
                    };
                    Ok(eval(arena, sig, b, &env_sig.extend(fst_val)))
                }
                _ => Err(TyError::TypeMismatch {
                    term,
                    expected: "Σ-type".into(),
                    found: value_display(&pair_ty),
                }),
            }
        }
        TermData::Nat => Ok(Value::VType(levels.fresh())),
        TermData::Zero => Ok(Value::VNat),
        TermData::Succ(n) => {
            check_inner(arena, sig, axioms, ctx, env, levels, n, Value::VNat)?;
            Ok(Value::VNat)
        }
        TermData::NatElim { .. } => Err(TyError::CannotInfer { term }),
        TermData::Ann(t, ty) => {
            let expected = eval(arena, sig, ty, env);
            check_inner(arena, sig, axioms, ctx, env, levels, t, expected.clone())?;
            Ok(expected)
        }
        TermData::Const(name) => lookup_const(arena, sig, axioms, term, &name),
    }
}

fn app_infer<'scope>(
    arena: &Arena<'scope>,
    sig: &Signature<'scope>,
    axioms: &AxiomRegistry<'scope>,
    ctx: &Context<'scope>,
    env: &Env<'scope>,
    levels: &mut ConstraintSet,
    term: TermId<'scope>,
    _f: TermId<'scope>,
    x: TermId<'scope>,
    fun_ty: Value<'scope>,
) -> Result<Value<'scope>, TyError<'scope>> {
    let pi = match fun_ty {
        Value::VPi(pi_id, _) => Some(pi_id),
        Value::VConst(_, ref ty) => match ty.as_ref() {
            Value::VPi(pi_id, _) => Some(*pi_id),
            _ => None,
        },
        _ => None,
    };
    let Some(pi_id) = pi else {
        return Err(TyError::TypeMismatch {
            term,
            expected: "Π-type".into(),
            found: value_display(&fun_ty),
        });
    };
    let (dom, cod) = pi_parts(arena, pi_id)?;
    let dom_val = eval(arena, sig, dom, env);
    let arg_val = eval(arena, sig, x, env);
    check_inner(arena, sig, axioms, ctx, env, levels, x, dom_val)?;
    Ok(eval(arena, sig, cod, &env.extend(arg_val)))
}

fn lookup_const<'scope>(
    arena: &Arena<'scope>,
    sig: &Signature<'scope>,
    axioms: &AxiomRegistry<'scope>,
    term: TermId<'scope>,
    name: &crate::term::Name,
) -> Result<Value<'scope>, TyError<'scope>> {
    let ty = if let Some(entry) = sig.get(name) {
        match entry {
            Entry::Def { ty, .. } | Entry::Axiom { ty } => *ty,
        }
    } else if let Some(ty) = axioms.get_type(name) {
        ty
    } else {
        return Err(TyError::UnknownConst {
            term,
            name: name.clone(),
        });
    };
    let vty = eval(arena, sig, ty, &Env::new());
    match sig.get(name) {
        Some(Entry::Def { .. }) => Ok(vty),
        Some(Entry::Axiom { .. }) => Ok(Value::VConst(name.clone(), Box::new(vty))),
        None => Ok(Value::VConst(name.clone(), Box::new(vty))),
    }
}

fn pi_parts<'scope>(
    arena: &Arena<'scope>,
    pi_id: TermId<'scope>,
) -> Result<(TermId<'scope>, TermId<'scope>), TyError<'scope>> {
    match arena.get(pi_id) {
        TermData::Pi(a, b) => Ok((a, b)),
        _ => Err(TyError::InvalidElim { term: pi_id }),
    }
}

fn sigma_parts<'scope>(
    arena: &Arena<'scope>,
    sig_id: TermId<'scope>,
) -> Result<(TermId<'scope>, TermId<'scope>), TyError<'scope>> {
    match arena.get(sig_id) {
        TermData::Sigma(a, b) => Ok((a, b)),
        _ => Err(TyError::InvalidElim { term: sig_id }),
    }
}

fn check_nat_elim<'scope>(
    arena: &Arena<'scope>,
    sig: &Signature<'scope>,
    axioms: &AxiomRegistry<'scope>,
    ctx: &Context<'scope>,
    env: &Env<'scope>,
    levels: &mut ConstraintSet,
    term: TermId<'scope>,
    ty: Value<'scope>,
    motive: TermId<'scope>,
    base: TermId<'scope>,
    step: TermId<'scope>,
    target: TermId<'scope>,
) -> Result<(), TyError<'scope>> {
    let motive_pi = arena.pi(arena.nat(), arena.typ(levels.fresh()));
    check_inner(
        arena,
        sig,
        axioms,
        ctx,
        env,
        levels,
        motive,
        Value::VPi(motive_pi, env.clone()),
    )?;
    let base_ty = eval(arena, sig, arena.app(motive, arena.zero()), env);
    check_inner(arena, sig, axioms, ctx, env, levels, base, base_ty)?;
    let step_ty = arena.pi(
        arena.nat(),
        arena.pi(
            arena.app(motive, arena.var(0)),
            arena.app(motive, arena.succ(arena.var(1))),
        ),
    );
    check_inner(
        arena,
        sig,
        axioms,
        ctx,
        env,
        levels,
        step,
        eval(arena, sig, step_ty, env),
    )?;
    check_inner(arena, sig, axioms, ctx, env, levels, target, Value::VNat)?;
    let expected = eval(arena, sig, arena.app(motive, target), env);
    if !def_eq(arena, sig, env, levels, &expected, &ty) {
        return Err(TyError::TypeMismatch {
            term,
            expected: value_display(&ty),
            found: value_display(&expected),
        });
    }
    Ok(())
}
