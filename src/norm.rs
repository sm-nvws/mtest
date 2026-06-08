use crate::arena::Arena;
use crate::env::Env;
use crate::level::{ConstraintSet, Level};
use crate::signature::{Entry, Signature};
use crate::term::{TermData, TermId};
use crate::value::{Neutral, Value};

pub fn eval<'scope>(
    arena: &Arena<'scope>,
    sig: &Signature<'scope>,
    term: TermId<'scope>,
    env: &Env<'scope>,
) -> Value<'scope> {
    match arena.get(term) {
        TermData::Var(i) => env.lookup(i).clone(),
        TermData::Type(l) => Value::VType(l),
        TermData::Pi(_, _) => Value::VPi(term, env.clone()),
        TermData::Lam(t, b) => Value::VLam(b, env.extend(eval(arena, sig, t, env))),
        TermData::App(f, x) => {
            let vf = eval(arena, sig, f, env);
            let vx = eval(arena, sig, x, env);
            apply(arena, sig, vf, vx)
        }
        TermData::Sigma(_, _) => Value::VSigma(term, env.clone()),
        TermData::Pair(x, y) => Value::VPair(
            Box::new(eval(arena, sig, x, env)),
            Box::new(eval(arena, sig, y, env)),
        ),
        TermData::Fst(p) => elim_fst(eval(arena, sig, p, env)),
        TermData::Snd(p) => elim_snd(eval(arena, sig, p, env)),
        TermData::Nat => Value::VNat,
        TermData::Zero => Value::VZero,
        TermData::Succ(n) => Value::VSucc(Box::new(eval(arena, sig, n, env))),
        TermData::NatElim {
            motive,
            base,
            step,
            target,
        } => elim_nat(arena, sig, env, motive, base, step, eval(arena, sig, target, env)),
        TermData::SigmaElim {
            motive,
            elim,
            target,
        } => elim_sigma(arena, sig, env, motive, elim, eval(arena, sig, target, env)),
        TermData::Ann(t, _) => eval(arena, sig, t, env),
        TermData::Const(name) => eval_const(arena, sig, &name, env),
    }
}

fn eval_const<'scope>(
    arena: &Arena<'scope>,
    sig: &Signature<'scope>,
    name: &crate::term::Name,
    env: &Env<'scope>,
) -> Value<'scope> {
    match sig.get(name) {
        Some(Entry::Def { body, .. }) => eval(arena, sig, *body, env),
        Some(Entry::Axiom { ty }) => {
            let vty = eval(arena, sig, *ty, env);
            Value::VConst(name.clone(), Box::new(vty))
        }
        None => Value::VNeutral(Neutral::NConst(name.clone())),
    }
}

fn apply<'scope>(
    arena: &Arena<'scope>,
    sig: &Signature<'scope>,
    fun: Value<'scope>,
    arg: Value<'scope>,
) -> Value<'scope> {
    match fun {
        Value::VLam(body, env) => eval(arena, sig, body, &env.extend(arg)),
        Value::VNeutral(n) => Value::VNeutral(Neutral::NApp(Box::new(n), Box::new(arg))),
        Value::VConst(name, _) => Value::VNeutral(Neutral::NApp(
            Box::new(Neutral::NConst(name)),
            Box::new(arg),
        )),
        other => Value::VNeutral(Neutral::NApp(
            Box::new(neutral_from_value(other)),
            Box::new(arg),
        )),
    }
}

fn neutral_from_value<'scope>(v: Value<'scope>) -> Neutral<'scope> {
    match v {
        Value::VNeutral(n) => n,
        Value::VConst(name, _) => Neutral::NConst(name),
        _ => Neutral::NVar(0),
    }
}

fn elim_fst<'scope>(pair: Value<'scope>) -> Value<'scope> {
    match pair {
        Value::VPair(a, _) => *a,
        Value::VNeutral(n) => Value::VNeutral(Neutral::NFst(Box::new(n))),
        other => Value::VNeutral(Neutral::NFst(Box::new(neutral_from_value(other)))),
    }
}

fn elim_snd<'scope>(pair: Value<'scope>) -> Value<'scope> {
    match pair {
        Value::VPair(_, b) => *b,
        Value::VNeutral(n) => Value::VNeutral(Neutral::NSnd(Box::new(n))),
        other => Value::VNeutral(Neutral::NSnd(Box::new(neutral_from_value(other)))),
    }
}

fn elim_sigma<'scope>(
    arena: &Arena<'scope>,
    sig: &Signature<'scope>,
    env: &Env<'scope>,
    motive: TermId<'scope>,
    elim: TermId<'scope>,
    target: Value<'scope>,
) -> Value<'scope> {
    let vm = eval(arena, sig, motive, env);
    let ve = eval(arena, sig, elim, env);
    match target {
        Value::VPair(fst, snd) => apply(arena, sig, apply(arena, sig, ve, *fst), *snd),
        Value::VNeutral(n) => Value::VNeutral(Neutral::NSigmaElim {
            motive: Box::new(vm),
            elim: Box::new(ve),
            target: Box::new(n),
        }),
        other => Value::VNeutral(Neutral::NSigmaElim {
            motive: Box::new(vm),
            elim: Box::new(ve),
            target: Box::new(neutral_from_value(other)),
        }),
    }
}

fn elim_nat<'scope>(
    arena: &Arena<'scope>,
    sig: &Signature<'scope>,
    env: &Env<'scope>,
    motive: TermId<'scope>,
    base: TermId<'scope>,
    step: TermId<'scope>,
    target: Value<'scope>,
) -> Value<'scope> {
    let vm = eval(arena, sig, motive, env);
    let vb = eval(arena, sig, base, env);
    let vs = eval(arena, sig, step, env);
    match target {
        Value::VZero => vb,
        Value::VSucc(n) => {
            let pred = *n;
            let ih = elim_nat(arena, sig, env, motive, base, step, pred.clone());
            apply(arena, sig, apply(arena, sig, vs, pred), ih)
        }
        Value::VNeutral(n) => Value::VNeutral(Neutral::NNatElim {
            motive: Box::new(vm),
            base: Box::new(vb),
            step: Box::new(vs),
            target: Box::new(n),
        }),
        other => Value::VNeutral(Neutral::NNatElim {
            motive: Box::new(vm),
            base: Box::new(vb),
            step: Box::new(vs),
            target: Box::new(neutral_from_value(other)),
        }),
    }
}

pub fn quote<'scope>(
    arena: &Arena<'scope>,
    sig: &Signature<'scope>,
    val: &Value<'scope>,
    level: usize,
) -> TermId<'scope> {
    match val {
        Value::VType(l) => arena.typ(*l),
        Value::VPi(pi_id, env) => quote_pi(arena, sig, *pi_id, env, level),
        Value::VLam(body, env) => {
            let param_ty = quote_lam_param(arena, sig, *body, env, level);
            let body_env = env.extend(Value::VNeutral(Neutral::NVar(level)));
            let body_val = eval(arena, sig, *body, &body_env);
            let b = quote(arena, sig, &body_val, level + 1);
            let p = param_ty;
            arena.lam(p, b)
        }
        Value::VSigma(sig_id, env) => quote_sigma(arena, sig, *sig_id, env, level),
        Value::VPair(x, y) => {
            let a = quote(arena, sig, x, level);
            let b = quote(arena, sig, y, level);
            arena.pair(a, b)
        }
        Value::VNat => arena.nat(),
        Value::VZero => arena.zero(),
        Value::VSucc(n) => {
            let inner = quote(arena, sig, n, level);
            arena.succ(inner)
        }
        Value::VConst(name, ty) => {
            let t = quote(arena, sig, ty, level);
            let k = arena.konst(name.clone());
            arena.ann(k, t)
        }
        Value::VNeutral(n) => quote_neutral(arena, sig, n, level),
    }
}

fn quote_pi<'scope>(
    arena: &Arena<'scope>,
    sig: &Signature<'scope>,
    pi_id: TermId<'scope>,
    env: &Env<'scope>,
    level: usize,
) -> TermId<'scope> {
    let (a, b) = match arena.get(pi_id) {
        TermData::Pi(a, b) => (a, b),
        _ => return pi_id,
    };
    let dom = quote(arena, sig, &eval(arena, sig, a, env), level);
    let body_env = env.extend(Value::VNeutral(Neutral::NVar(level)));
    let cod = quote(arena, sig, &eval(arena, sig, b, &body_env), level + 1);
    arena.pi(dom, cod)
}

fn quote_sigma<'scope>(
    arena: &Arena<'scope>,
    sig: &Signature<'scope>,
    sig_id: TermId<'scope>,
    env: &Env<'scope>,
    level: usize,
) -> TermId<'scope> {
    let (a, b) = match arena.get(sig_id) {
        TermData::Sigma(a, b) => (a, b),
        _ => return sig_id,
    };
    let fst = quote(arena, sig, &eval(arena, sig, a, env), level);
    let body_env = env.extend(Value::VNeutral(Neutral::NVar(level)));
    let snd = quote(arena, sig, &eval(arena, sig, b, &body_env), level + 1);
    arena.sigma(fst, snd)
}

fn quote_lam_param<'scope>(
    arena: &Arena<'scope>,
    sig: &Signature<'scope>,
    body: TermId<'scope>,
    env: &Env<'scope>,
    level: usize,
) -> TermId<'scope> {
    match arena.get(body) {
        TermData::Lam(t, _) => quote(arena, sig, &eval(arena, sig, t, env), level),
        _ => arena.var(level),
    }
}

fn quote_neutral<'scope>(
    arena: &Arena<'scope>,
    sig: &Signature<'scope>,
    n: &Neutral<'scope>,
    level: usize,
) -> TermId<'scope> {
    match n {
        Neutral::NVar(l) => {
            assert!(level > *l, "variable out of scope in quote");
            arena.var(level - 1 - l)
        }
        Neutral::NApp(h, a) => {
            let f = quote_neutral(arena, sig, h, level);
            let x = quote(arena, sig, a, level);
            arena.app(f, x)
        }
        Neutral::NFst(p) => {
            let pair = quote_neutral(arena, sig, p, level);
            arena.fst(pair)
        }
        Neutral::NSnd(p) => {
            let pair = quote_neutral(arena, sig, p, level);
            arena.snd(pair)
        }
        Neutral::NNatElim {
            motive,
            base,
            step,
            target,
        } => {
            let m = quote(arena, sig, motive, level);
            let b = quote(arena, sig, base, level);
            let s = quote(arena, sig, step, level);
            let t = quote_neutral(arena, sig, target, level);
            arena.nat_elim(m, b, s, t)
        }
        Neutral::NSigmaElim {
            motive,
            elim,
            target,
        } => {
            let m = quote(arena, sig, motive, level);
            let e = quote(arena, sig, elim, level);
            let t = quote_neutral(arena, sig, target, level);
            arena.sigma_elim(m, e, t)
        }
        Neutral::NConst(name) => arena.konst(name.clone()),
    }
}

pub fn normalize<'scope>(
    arena: &Arena<'scope>,
    sig: &Signature<'scope>,
    env: &Env<'scope>,
    term: TermId<'scope>,
) -> TermId<'scope> {
    match arena.get(term) {
        TermData::Ann(t, ty) => {
            let nt = normalize(arena, sig, env, t);
            let nty = normalize(arena, sig, env, ty);
            arena.ann(nt, nty)
        }
        _ => {
            let v = eval(arena, sig, term, env);
            quote(arena, sig, &v, env.len())
        }
    }
}

pub fn def_eq<'scope>(
    arena: &Arena<'scope>,
    sig: &Signature<'scope>,
    env: &Env<'scope>,
    levels: &mut ConstraintSet,
    a: &Value<'scope>,
    b: &Value<'scope>,
) -> bool {
    def_eq_values(arena, sig, env, levels, a, b)
}

fn def_eq_values<'scope>(
    arena: &Arena<'scope>,
    sig: &Signature<'scope>,
    env: &Env<'scope>,
    levels: &mut ConstraintSet,
    a: &Value<'scope>,
    b: &Value<'scope>,
) -> bool {
    if let Value::VConst(name, _) = a {
        if let Some(Entry::Def { body, .. }) = sig.get(name) {
            let unfolded = eval(arena, sig, *body, env);
            return def_eq_values(arena, sig, env, levels, &unfolded, b);
        }
    }
    if let Value::VConst(name, _) = b {
        if let Some(Entry::Def { body, .. }) = sig.get(name) {
            let unfolded = eval(arena, sig, *body, env);
            return def_eq_values(arena, sig, env, levels, a, &unfolded);
        }
    }

    match (a, b) {
        (Value::VType(l1), Value::VType(l2)) => {
            levels.equate(Level::var(*l1), Level::var(*l2));
            true
        }
        (Value::VNat, Value::VNat) => true,
        (Value::VZero, Value::VZero) => true,
        (Value::VSucc(a1), Value::VSucc(b1)) => {
            def_eq_values(arena, sig, env, levels, a1, b1)
        }
        (Value::VPair(x1, y1), Value::VPair(x2, y2)) => {
            def_eq_values(arena, sig, env, levels, x1, x2)
                && def_eq_values(arena, sig, env, levels, y1, y2)
        }
        (Value::VPi(id1, env1), Value::VPi(id2, env2)) => {
            def_eq_pi(arena, sig, env, levels, *id1, env1, *id2, env2)
        }
        (Value::VSigma(id1, env1), Value::VSigma(id2, env2)) => {
            def_eq_sigma(arena, sig, env, levels, *id1, env1, *id2, env2)
        }
        (Value::VLam(body1, env1), Value::VLam(body2, env2)) => {
            def_eq_lam(arena, sig, env, levels, *body1, env1, *body2, env2)
        }
        (Value::VConst(n1, _), Value::VConst(n2, _)) => n1 == n2,
        (Value::VConst(_, ty1), other) => def_eq_values(arena, sig, env, levels, ty1, other),
        (other, Value::VConst(_, ty2)) => def_eq_values(arena, sig, env, levels, other, ty2),
        (Value::VNeutral(n1), Value::VNeutral(n2)) => {
            def_eq_neutral(arena, sig, env, levels, n1, n2)
        }
        _ => {
            let na = quote(arena, sig, a, env.len());
            let nb = quote(arena, sig, b, env.len());
            structural_eq(arena, na, nb)
        }
    }
}

fn def_eq_pi<'scope>(
    arena: &Arena<'scope>,
    sig: &Signature<'scope>,
    env: &Env<'scope>,
    levels: &mut ConstraintSet,
    id1: TermId<'scope>,
    env1: &Env<'scope>,
    id2: TermId<'scope>,
    env2: &Env<'scope>,
) -> bool {
    let (a1, b1) = match arena.get(id1) {
        TermData::Pi(a, b) => (a, b),
        _ => return false,
    };
    let (a2, b2) = match arena.get(id2) {
        TermData::Pi(a, b) => (a, b),
        _ => return false,
    };
    let dom1 = eval(arena, sig, a1, env1);
    let dom2 = eval(arena, sig, a2, env2);
    if !def_eq_values(arena, sig, env, levels, &dom1, &dom2) {
        return false;
    }
    let env1_ext = env1.extend(Value::VNeutral(Neutral::NVar(env1.len())));
    let env2_ext = env2.extend(Value::VNeutral(Neutral::NVar(env2.len())));
    let cod1 = eval(arena, sig, b1, &env1_ext);
    let cod2 = eval(arena, sig, b2, &env2_ext);
    def_eq_values(arena, sig, env, levels, &cod1, &cod2)
}

fn def_eq_sigma<'scope>(
    arena: &Arena<'scope>,
    sig: &Signature<'scope>,
    env: &Env<'scope>,
    levels: &mut ConstraintSet,
    id1: TermId<'scope>,
    env1: &Env<'scope>,
    id2: TermId<'scope>,
    env2: &Env<'scope>,
) -> bool {
    let (a1, b1) = match arena.get(id1) {
        TermData::Sigma(a, b) => (a, b),
        _ => return false,
    };
    let (a2, b2) = match arena.get(id2) {
        TermData::Sigma(a, b) => (a, b),
        _ => return false,
    };
    let fst1 = eval(arena, sig, a1, env1);
    let fst2 = eval(arena, sig, a2, env2);
    if !def_eq_values(arena, sig, env, levels, &fst1, &fst2) {
        return false;
    }
    let env1_ext = env1.extend(Value::VNeutral(Neutral::NVar(env1.len())));
    let env2_ext = env2.extend(Value::VNeutral(Neutral::NVar(env2.len())));
    let snd1 = eval(arena, sig, b1, &env1_ext);
    let snd2 = eval(arena, sig, b2, &env2_ext);
    def_eq_values(arena, sig, env, levels, &snd1, &snd2)
}

fn def_eq_lam<'scope>(
    arena: &Arena<'scope>,
    sig: &Signature<'scope>,
    env: &Env<'scope>,
    levels: &mut ConstraintSet,
    body1: TermId<'scope>,
    env1: &Env<'scope>,
    body2: TermId<'scope>,
    env2: &Env<'scope>,
) -> bool {
    let arg = Value::VNeutral(Neutral::NVar(env.len()));
    let v1 = eval(arena, sig, body1, &env1.extend(arg.clone()));
    let v2 = eval(arena, sig, body2, &env2.extend(arg));
    def_eq_values(arena, sig, env, levels, &v1, &v2)
}

fn def_eq_neutral<'scope>(
    arena: &Arena<'scope>,
    sig: &Signature<'scope>,
    env: &Env<'scope>,
    levels: &mut ConstraintSet,
    a: &Neutral<'scope>,
    b: &Neutral<'scope>,
) -> bool {
    match (a, b) {
        (Neutral::NVar(i), Neutral::NVar(j)) => i == j,
        (Neutral::NConst(n1), Neutral::NConst(n2)) => n1 == n2,
        (Neutral::NApp(f1, x1), Neutral::NApp(f2, x2)) => {
            def_eq_neutral(arena, sig, env, levels, f1, f2)
                && def_eq_values(arena, sig, env, levels, x1, x2)
        }
        (Neutral::NFst(p1), Neutral::NFst(p2)) => def_eq_neutral(arena, sig, env, levels, p1, p2),
        (Neutral::NSnd(p1), Neutral::NSnd(p2)) => def_eq_neutral(arena, sig, env, levels, p1, p2),
        (
            Neutral::NNatElim {
                motive: m1,
                base: b1,
                step: s1,
                target: t1,
            },
            Neutral::NNatElim {
                motive: m2,
                base: b2,
                step: s2,
                target: t2,
            },
        ) => {
            def_eq_values(arena, sig, env, levels, m1, m2)
                && def_eq_values(arena, sig, env, levels, b1, b2)
                && def_eq_values(arena, sig, env, levels, s1, s2)
                && def_eq_neutral(arena, sig, env, levels, t1, t2)
        }
        (
            Neutral::NSigmaElim {
                motive: m1,
                elim: e1,
                target: t1,
            },
            Neutral::NSigmaElim {
                motive: m2,
                elim: e2,
                target: t2,
            },
        ) => {
            def_eq_values(arena, sig, env, levels, m1, m2)
                && def_eq_values(arena, sig, env, levels, e1, e2)
                && def_eq_neutral(arena, sig, env, levels, t1, t2)
        }
        _ => {
            let t1 = quote_neutral(arena, sig, a, env.len());
            let t2 = quote_neutral(arena, sig, b, env.len());
            structural_eq(arena, t1, t2)
        }
    }
}

fn structural_eq<'scope>(arena: &Arena<'scope>, a: TermId<'scope>, b: TermId<'scope>) -> bool {
    match (arena.get(a), arena.get(b)) {
        (TermData::Var(i), TermData::Var(j)) => i == j,
        (TermData::Type(l1), TermData::Type(l2)) => l1 == l2,
        (TermData::Pi(a1, b1), TermData::Pi(a2, b2)) => {
            structural_eq(arena, a1, a2) && structural_eq(arena, b1, b2)
        }
        (TermData::Lam(t1, b1), TermData::Lam(t2, b2)) => {
            structural_eq(arena, t1, t2) && structural_eq(arena, b1, b2)
        }
        (TermData::App(f1, x1), TermData::App(f2, x2)) => {
            structural_eq(arena, f1, f2) && structural_eq(arena, x1, x2)
        }
        (TermData::Sigma(a1, b1), TermData::Sigma(a2, b2)) => {
            structural_eq(arena, a1, a2) && structural_eq(arena, b1, b2)
        }
        (TermData::Pair(x1, y1), TermData::Pair(x2, y2)) => {
            structural_eq(arena, x1, x2) && structural_eq(arena, y1, y2)
        }
        (TermData::Fst(p1), TermData::Fst(p2)) => structural_eq(arena, p1, p2),
        (TermData::Snd(p1), TermData::Snd(p2)) => structural_eq(arena, p1, p2),
        (TermData::Nat, TermData::Nat) => true,
        (TermData::Zero, TermData::Zero) => true,
        (TermData::Succ(n1), TermData::Succ(n2)) => structural_eq(arena, n1, n2),
        (
            TermData::NatElim {
                motive: m1,
                base: b1,
                step: s1,
                target: t1,
            },
            TermData::NatElim {
                motive: m2,
                base: b2,
                step: s2,
                target: t2,
            },
        ) => {
            structural_eq(arena, m1, m2)
                && structural_eq(arena, b1, b2)
                && structural_eq(arena, s1, s2)
                && structural_eq(arena, t1, t2)
        }
        (
            TermData::SigmaElim {
                motive: m1,
                elim: e1,
                target: t1,
            },
            TermData::SigmaElim {
                motive: m2,
                elim: e2,
                target: t2,
            },
        ) => {
            structural_eq(arena, m1, m2)
                && structural_eq(arena, e1, e2)
                && structural_eq(arena, t1, t2)
        }
        (TermData::Ann(t1, ty1), TermData::Ann(t2, ty2)) => {
            structural_eq(arena, t1, t2) && structural_eq(arena, ty1, ty2)
        }
        (TermData::Const(n1), TermData::Const(n2)) => n1 == n2,
        _ => false,
    }
}
