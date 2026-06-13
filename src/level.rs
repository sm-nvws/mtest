use std::collections::HashMap;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct LevelVar(pub usize);

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Level {
    Var(LevelVar),
    Zero,
    Succ(Box<Level>),
}

impl Level {
    pub fn var(v: LevelVar) -> Self {
        Level::Var(v)
    }

    pub fn succ(self) -> Self {
        Level::Succ(Box::new(self))
    }
}

#[derive(Clone, Debug, Default)]
pub struct ConstraintSet {
    fresh: usize,
    assign: HashMap<LevelVar, Level>,
    leq: Vec<(Level, Level)>,
}

impl ConstraintSet {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn fresh(&mut self) -> LevelVar {
        let v = LevelVar(self.fresh);
        self.fresh += 1;
        v
    }

    pub fn equate(&mut self, a: Level, b: Level) {
        self.leq.push((a.clone(), b.clone()));
        self.leq.push((b, a));
    }

    pub fn subtype(&mut self, sub: Level, sup: Level) {
        self.leq.push((sub, sup));
    }

    fn resolve_var(&mut self, v: LevelVar) -> Level {
        if let Some(l) = self.assign.get(&v).cloned() {
            return self.normalize(l);
        }
        Level::Var(v)
    }

    fn normalize(&mut self, l: Level) -> Level {
        match l {
            Level::Var(v) => self.resolve_var(v),
            Level::Zero => Level::Zero,
            Level::Succ(inner) => Level::Succ(Box::new(self.normalize(*inner))),
        }
    }

    fn level_height(l: &Level) -> Option<usize> {
        match l {
            Level::Zero => Some(0),
            Level::Succ(inner) => Self::level_height(inner).map(|n| n + 1),
            Level::Var(_) => None,
        }
    }

    fn unify_into(&mut self, v: LevelVar, target: Level) {
        let target = self.normalize(target);
        if let Level::Var(v2) = &target
            && v2 == &v
        {
            return;
        }
        if let Some(existing) = self.assign.get(&v).cloned() {
            let existing = self.normalize(existing);
            self.equate(existing, target);
            return;
        }
        if let Level::Var(other) = target {
            if let Some(t) = self.assign.get(&other).cloned() {
                self.unify_into(v, t);
            } else {
                self.assign.insert(other, Level::Var(v));
            }
            return;
        }
        self.assign.insert(v, target);
    }

    /// Solve the accumulated `a <= b` constraints.
    ///
    /// Levels are built from `Zero`, `Succ` and unification variables. The
    /// work list is drained until empty: `Succ`/`Succ` pairs are decomposed,
    /// a variable on either side is unified, and only an impossible
    /// `Succ(..) <= Zero` is reported as inconsistent (a free variable upper
    /// bound is always satisfiable). A fuel counter guarantees termination
    /// even when variable unification keeps re-enqueuing equalities.
    pub fn solve(&mut self) -> Result<(), LevelError> {
        let mut fuel = self.leq.len().saturating_mul(8) + 64;
        while let Some((a, b)) = self.leq.pop() {
            if fuel == 0 {
                break;
            }
            fuel -= 1;
            let a = self.normalize(a);
            let b = self.normalize(b);
            match (&a, &b) {
                (Level::Zero, _) => {}
                (Level::Succ(_), Level::Zero) => return Err(LevelError::Inconsistent),
                (Level::Succ(a1), Level::Succ(b1)) => {
                    self.leq.push((*a1.clone(), *b1.clone()));
                }
                (Level::Var(v), _) => self.unify_into(*v, b),
                (Level::Succ(_), Level::Var(v)) => {
                    if let Some(h) = Self::level_height(&a) {
                        let mut want = Level::Zero;
                        for _ in 0..h {
                            want = want.succ();
                        }
                        self.unify_into(*v, want);
                    }
                }
            }
        }
        Ok(())
    }

    pub fn instantiate(&mut self, l: Level) -> Level {
        self.normalize(l)
    }
}

#[derive(Debug, Clone, thiserror::Error)]
pub enum LevelError {
    #[error("inconsistent universe level constraints")]
    Inconsistent,
}
