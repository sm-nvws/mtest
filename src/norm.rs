use crate::arena::Arena;
use crate::env::Env;
use crate::level::ConstraintSet;
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
        TermData::Snd(p) => elim_snd(arena, sig, p, env),
        TermData::Nat => Value::VNat,
        TermData::Zero => Value::VZero,
        TermData::Succ(n) => Value::VSucc(Box::new(eval(arena, sig, n, env))),
        TermData::NatElim {
            motive,
            base,
            step,
            target,
        } => elim_nat(arena, sig, env, motive, base, step, eval(arena, sig, target, env)),
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

fn elim_snd<'scope>(
    arena: &Arena<'scope>,
    sig: &Signature<'scope>,
    pair: TermId<'scope>,
    env: &Env<'scope>,
) -> Value<'scope> {
    let pair = eval(arena, sig, pair, env);
    match pair {
        Value::VPair(_, b) => *b,
        Value::VNeutral(n) => Value::VNeutral(Neutral::NSnd(Box::new(n))),
        other => Value::VNeutral(Neutral::NSnd(Box::new(neutral_from_value(other)))),
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
        Neutral::NVar(l) => arena.var(level.saturating_sub(1).saturating_sub(*l)),
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

fn pi_head_eq<'scope>(a: &Value<'scope>, b: &Value<'scope>) -> bool {
    let pi_id = |v: &Value<'scope>| match v {
        Value::VPi(id, _) => Some(*id),
        Value::VConst(_, ty) => match ty.as_ref() {
            Value::VPi(id, _) => Some(*id),
            _ => None,
        },
        _ => None,
    };
    match (pi_id(a), pi_id(b)) {
        (Some(ida), Some(idb)) => ida == idb,
        _ => false,
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
    if pi_head_eq(a, b) {
        return true;
    }
    if quote_type(arena, sig, a, env.len()) && quote_type(arena, sig, b, env.len()) {
        if let (Value::VType(l1), Value::VType(l2)) = (a, b) {
            levels.equate(
                crate::level::Level::var(*l1),
                crate::level::Level::var(*l2),
            );
        }
    }
    let na = quote(arena, sig, a, env.len());
    let nb = quote(arena, sig, b, env.len());
    structural_eq(arena, na, nb)
}

fn quote_type<'scope>(arena: &Arena<'scope>, sig: &Signature<'scope>, v: &Value<'scope>, lvl: usize) -> bool {
    let _ = (arena, sig, v, lvl);
    matches!(v, Value::VType(_))
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
        (TermData::Ann(t1, ty1), TermData::Ann(t2, ty2)) => {
            structural_eq(arena, t1, t2) && structural_eq(arena, ty1, ty2)
        }
        (TermData::Const(n1), TermData::Const(n2)) => n1 == n2,
        _ => false,
    }
}
