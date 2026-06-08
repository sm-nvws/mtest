use std::cell::RefCell;

use crate::arena::Arena;
use crate::context::Context;
use crate::env::Env;
use crate::error::{value_display, TyError};
use crate::level::{ConstraintSet, Level, LevelVar};
use crate::norm::{def_eq, eval, quote};
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
    ctx: &Context<'scope>,
    env: &Env<'scope>,
    term: TermId<'scope>,
    ty: Value<'scope>,
) -> Result<(), TyError> {
    levels_mut(|levels| check_inner(arena, sig, ctx, env, levels, term, ty))
}

fn check_inner<'scope>(
    arena: &Arena<'scope>,
    sig: &Signature<'scope>,
    ctx: &Context<'scope>,
    env: &Env<'scope>,
    levels: &mut ConstraintSet,
    term: TermId<'scope>,
    ty: Value<'scope>,
) -> Result<(), TyError> {
    match arena.get(term) {
        TermData::Ann(t, ty_term) => {
            let expected = eval(arena, sig, ty_term, env);
            if !def_eq(arena, sig, env, levels, &expected, &ty) {
                return Err(TyError::type_mismatch(
                    arena,
                    term,
                    value_display(&ty),
                    value_display(&expected),
                ));
            }
            check_inner(arena, sig, ctx, env, levels, t, ty)
        }
        TermData::Lam(param_ty, body) => match &ty {
            Value::VPi(pi_id, pi_env) => {
                let (dom, cod) = pi_parts(arena, *pi_id)?;
                let dom_val = eval(arena, sig, dom, pi_env);
                let param_ty_val = eval(arena, sig, param_ty, env);
                if !def_eq(arena, sig, env, levels, &param_ty_val, &dom_val) {
                    return Err(TyError::type_mismatch(
                        arena,
                        term,
                        value_display(&dom_val),
                        format!("{:?}", arena.get(param_ty)),
                    ));
                }
                let new_ctx = ctx.extend(dom_val);
                let new_env = env.extend(Value::VNeutral(Neutral::NVar(env.len())));
                let cod_env = pi_env.extend(Value::VNeutral(Neutral::NVar(pi_env.len())));
                let cod_val = eval(arena, sig, cod, &cod_env);
                check_inner(arena, sig, &new_ctx, &new_env, levels, body, cod_val)
            }
            _ => Err(TyError::type_mismatch(
                arena,
                term,
                "Π-type",
                value_display(&ty),
            )),
        },
        TermData::Pair(fst, snd) => match &ty {
            Value::VSigma(sig_id, env_sig) => {
                let (a, b) = sigma_parts(arena, *sig_id)?;
                let fst_ty = eval(arena, sig, a, env_sig);
                check_inner(arena, sig, ctx, env, levels, fst, fst_ty)?;
                let fst_val = eval(arena, sig, fst, env);
                let snd_ty = eval(arena, sig, b, &env_sig.extend(fst_val));
                check_inner(arena, sig, ctx, env, levels, snd, snd_ty)
            }
            _ => Err(TyError::type_mismatch(
                arena,
                term,
                "Σ-type",
                value_display(&ty),
            )),
        },
        TermData::Zero => {
            if !def_eq(arena, sig, env, levels, &ty, &Value::VNat) {
                return Err(TyError::type_mismatch(arena, term, value_display(&ty), "Nat"));
            }
            Ok(())
        }
        TermData::Succ(n) => {
            if !def_eq(arena, sig, env, levels, &ty, &Value::VNat) {
                return Err(TyError::type_mismatch(arena, term, value_display(&ty), "Nat"));
            }
            check_inner(arena, sig, ctx, env, levels, n, Value::VNat)
        }
        TermData::NatElim {
            motive,
            base,
            step,
            target,
        } => check_nat_elim(
            arena, sig, ctx, env, levels, term, ty, motive, base, step, target,
        ),
        TermData::SigmaElim {
            motive,
            elim,
            target,
        } => check_sigma_elim(
            arena, sig, ctx, env, levels, term, ty, motive, elim, target,
        ),
        _ => {
            let inferred = infer_inner(arena, sig, ctx, env, levels, term)?;
            if !def_eq(arena, sig, env, levels, &inferred, &ty) {
                return Err(TyError::type_mismatch(
                    arena,
                    term,
                    value_display(&ty),
                    value_display(&inferred),
                ));
            }
            Ok(())
        }
    }
}

pub fn infer<'scope>(
    arena: &Arena<'scope>,
    sig: &Signature<'scope>,
    ctx: &Context<'scope>,
    env: &Env<'scope>,
    term: TermId<'scope>,
) -> Result<Value<'scope>, TyError> {
    levels_mut(|levels| infer_inner(arena, sig, ctx, env, levels, term))
}

fn infer_inner<'scope>(
    arena: &Arena<'scope>,
    sig: &Signature<'scope>,
    ctx: &Context<'scope>,
    env: &Env<'scope>,
    levels: &mut ConstraintSet,
    term: TermId<'scope>,
) -> Result<Value<'scope>, TyError> {
    match arena.get(term) {
        TermData::Var(i) => Ok(ctx.lookup(i).clone()),
        TermData::Type(l) => {
            let lift = levels.fresh();
            levels.subtype(Level::var(l), Level::var(lift).succ());
            Ok(Value::VType(lift))
        }
        TermData::Pi(a, b) => {
            let a_ty = infer_inner(arena, sig, ctx, env, levels, a)?;
            match a_ty {
                Value::VType(l_dom) => {
                    let new_ctx = ctx.extend(Value::VType(l_dom));
                    let new_env = env.extend(Value::VNeutral(Neutral::NVar(env.len())));
                    let b_ty = infer_inner(arena, sig, &new_ctx, &new_env, levels, b)?;
                    match b_ty {
                        Value::VType(l_cod) => {
                            let lvl = levels.fresh();
                            levels.subtype(Level::var(l_cod), Level::var(lvl));
                            Ok(Value::VType(lvl))
                        }
                        _ => Err(TyError::type_mismatch(
                            arena,
                            term,
                            "universe",
                            value_display(&b_ty),
                        )),
                    }
                }
                _ => {
                    let new_ctx = ctx.extend(a_ty.clone());
                    let new_env = env.extend(Value::VNeutral(Neutral::NVar(env.len())));
                    let _cod = infer_inner(arena, sig, &new_ctx, &new_env, levels, b)?;
                    let pi_id = arena.pi(a, b);
                    Ok(Value::VPi(pi_id, env.clone()))
                }
            }
        }
        TermData::Lam(param_ty, body) => {
            let dom = eval(arena, sig, param_ty, env);
            let new_ctx = ctx.extend(dom.clone());
            let new_env = env.extend(Value::VNeutral(Neutral::NVar(env.len())));
            let cod_val = infer_inner(arena, sig, &new_ctx, &new_env, levels, body)?;
            let cod_term = quote(arena, sig, &cod_val, new_env.len());
            let pi_id = arena.pi(param_ty, cod_term);
            Ok(Value::VPi(pi_id, env.clone()))
        }
        TermData::App(f, x) => {
            let fun_ty = infer_inner(arena, sig, ctx, env, levels, f)?;
            app_infer(arena, sig, ctx, env, levels, term, f, x, fun_ty)
        }
        TermData::Sigma(a, b) => {
            let a_ty = infer_inner(arena, sig, ctx, env, levels, a)?;
            match a_ty {
                Value::VType(l1) => {
                    let new_ctx = ctx.extend(Value::VType(l1));
                    let new_env = env.extend(Value::VNeutral(Neutral::NVar(env.len())));
                    let b_ty = infer_inner(arena, sig, &new_ctx, &new_env, levels, b)?;
                    match b_ty {
                        Value::VType(l2) => {
                            levels.subtype(Level::var(l1), Level::var(l2));
                            Ok(Value::VType(l2))
                        }
                        _ => Err(TyError::type_mismatch(
                            arena,
                            term,
                            "universe",
                            value_display(&b_ty),
                        )),
                    }
                }
                _ => Err(TyError::type_mismatch(arena, term, "universe", "Σ-type")),
            }
        }
        TermData::Pair(_, _) => Err(TyError::cannot_infer(arena, term)),
        TermData::Fst(p) => {
            let pair_ty = infer_inner(arena, sig, ctx, env, levels, p)?;
            match pair_ty {
                Value::VSigma(sig_id, env_sig) => {
                    let (a, _) = sigma_parts(arena, sig_id)?;
                    Ok(eval(arena, sig, a, &env_sig))
                }
                _ => Err(TyError::type_mismatch(
                    arena,
                    term,
                    "Σ-type",
                    value_display(&pair_ty),
                )),
            }
        }
        TermData::Snd(p) => {
            let pair_ty = infer_inner(arena, sig, ctx, env, levels, p)?;
            match pair_ty {
                Value::VSigma(sig_id, env_sig) => {
                    let (_a, b) = sigma_parts(arena, sig_id)?;
                    let pair_val = eval(arena, sig, p, env);
                    let fst_val = match pair_val {
                        Value::VPair(f, _) => *f,
                        _ => return Err(TyError::cannot_infer(arena, term)),
                    };
                    Ok(eval(arena, sig, b, &env_sig.extend(fst_val)))
                }
                _ => Err(TyError::type_mismatch(
                    arena,
                    term,
                    "Σ-type",
                    value_display(&pair_ty),
                )),
            }
        }
        TermData::Nat => Ok(Value::VType(levels.fresh())),
        TermData::Zero => Ok(Value::VNat),
        TermData::Succ(n) => {
            check_inner(arena, sig, ctx, env, levels, n, Value::VNat)?;
            Ok(Value::VNat)
        }
        TermData::NatElim { .. } | TermData::SigmaElim { .. } => {
            Err(TyError::cannot_infer(arena, term))
        }
        TermData::Ann(t, ty) => {
            let expected = eval(arena, sig, ty, env);
            check_inner(arena, sig, ctx, env, levels, t, expected.clone())?;
            Ok(expected)
        }
        TermData::Const(name) => lookup_const(arena, sig, term, &name),
    }
}

fn app_infer<'scope>(
    arena: &Arena<'scope>,
    sig: &Signature<'scope>,
    ctx: &Context<'scope>,
    env: &Env<'scope>,
    levels: &mut ConstraintSet,
    term: TermId<'scope>,
    _f: TermId<'scope>,
    x: TermId<'scope>,
    fun_ty: Value<'scope>,
) -> Result<Value<'scope>, TyError> {
    let (pi_id, pi_env) = match fun_ty {
        Value::VPi(pi_id, pi_env) => (pi_id, pi_env),
        Value::VConst(_, ref ty) => match ty.as_ref() {
            Value::VPi(pi_id, pi_env) => (*pi_id, pi_env.clone()),
            _ => {
                return Err(TyError::type_mismatch(
                    arena,
                    term,
                    "Π-type",
                    value_display(&fun_ty),
                ));
            }
        },
        _ => {
            return Err(TyError::type_mismatch(
                arena,
                term,
                "Π-type",
                value_display(&fun_ty),
            ));
        }
    };
    let (dom, cod) = pi_parts(arena, pi_id)?;
    let dom_val = eval(arena, sig, dom, &pi_env);
    let arg_val = eval(arena, sig, x, env);
    check_inner(arena, sig, ctx, env, levels, x, dom_val)?;
    Ok(eval(arena, sig, cod, &pi_env.extend(arg_val)))
}

fn lookup_const<'scope>(
    arena: &Arena<'scope>,
    sig: &Signature<'scope>,
    term: TermId<'scope>,
    name: &crate::term::Name,
) -> Result<Value<'scope>, TyError> {
    let Some(entry) = sig.get(name) else {
        return Err(TyError::unknown_const(arena, term, name.clone()));
    };
    let ty = match entry {
        Entry::Def { ty, .. } | Entry::Axiom { ty } => *ty,
    };
    let vty = eval(arena, sig, ty, &Env::new());
    match entry {
        Entry::Def { .. } => Ok(vty),
        Entry::Axiom { .. } => Ok(Value::VConst(name.clone(), Box::new(vty))),
    }
}

fn pi_parts<'scope>(
    arena: &Arena<'scope>,
    pi_id: TermId<'scope>,
) -> Result<(TermId<'scope>, TermId<'scope>), TyError> {
    match arena.get(pi_id) {
        TermData::Pi(a, b) => Ok((a, b)),
        _ => Err(TyError::invalid_elim(arena, pi_id)),
    }
}

fn sigma_parts<'scope>(
    arena: &Arena<'scope>,
    sig_id: TermId<'scope>,
) -> Result<(TermId<'scope>, TermId<'scope>), TyError> {
    match arena.get(sig_id) {
        TermData::Sigma(a, b) => Ok((a, b)),
        _ => Err(TyError::invalid_elim(arena, sig_id)),
    }
}

fn check_sigma_elim<'scope>(
    arena: &Arena<'scope>,
    sig: &Signature<'scope>,
    ctx: &Context<'scope>,
    env: &Env<'scope>,
    levels: &mut ConstraintSet,
    term: TermId<'scope>,
    ty: Value<'scope>,
    motive: TermId<'scope>,
    elim: TermId<'scope>,
    target: TermId<'scope>,
) -> Result<(), TyError> {
    let target_ty = infer_inner(arena, sig, ctx, env, levels, target)?;
    let (sig_id, _env_sig) = match target_ty {
        Value::VSigma(sig_id, env_sig) => (sig_id, env_sig),
        _ => {
            return Err(TyError::type_mismatch(
                arena,
                target,
                "Σ-type",
                value_display(&target_ty),
            ));
        }
    };
    let (a_ty, b_ty) = sigma_parts(arena, sig_id)?;
    let motive_pi = arena.pi(sig_id, arena.typ(levels.fresh()));
    check_inner(
        arena,
        sig,
        ctx,
        env,
        levels,
        motive,
        Value::VPi(motive_pi, env.clone()),
    )?;
    let elim_ty = arena.pi(
        a_ty,
        arena.pi(
            b_ty,
            arena.app(motive, arena.pair(arena.var(1), arena.var(0))),
        ),
    );
    check_inner(
        arena,
        sig,
        ctx,
        env,
        levels,
        elim,
        eval(arena, sig, elim_ty, env),
    )?;
    let expected = eval(arena, sig, arena.app(motive, target), env);
    if !def_eq(arena, sig, env, levels, &expected, &ty) {
        return Err(TyError::type_mismatch(
            arena,
            term,
            value_display(&ty),
            value_display(&expected),
        ));
    }
    Ok(())
}

fn check_nat_elim<'scope>(
    arena: &Arena<'scope>,
    sig: &Signature<'scope>,
    ctx: &Context<'scope>,
    env: &Env<'scope>,
    levels: &mut ConstraintSet,
    term: TermId<'scope>,
    ty: Value<'scope>,
    motive: TermId<'scope>,
    base: TermId<'scope>,
    step: TermId<'scope>,
    target: TermId<'scope>,
) -> Result<(), TyError> {
    let motive_pi = arena.pi(arena.nat(), arena.typ(levels.fresh()));
    check_inner(
        arena,
        sig,
        ctx,
        env,
        levels,
        motive,
        Value::VPi(motive_pi, env.clone()),
    )?;
    let base_ty = eval(arena, sig, arena.app(motive, arena.zero()), env);
    check_inner(arena, sig, ctx, env, levels, base, base_ty)?;
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
        ctx,
        env,
        levels,
        step,
        eval(arena, sig, step_ty, env),
    )?;
    check_inner(arena, sig, ctx, env, levels, target, Value::VNat)?;
    let expected = eval(arena, sig, arena.app(motive, target), env);
    if !def_eq(arena, sig, env, levels, &expected, &ty) {
        return Err(TyError::type_mismatch(
            arena,
            term,
            value_display(&ty),
            value_display(&expected),
        ));
    }
    Ok(())
}
