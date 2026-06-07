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
        if let Level::Var(v2) = &target {
            if v2 == &v {
                return;
            }
        }
        if let Some(existing) = self.assign.get(&v).cloned() {
            let existing = self.normalize(existing);
            self.equate(existing, target);
            return;
        }
        if let Level::Var(other) = target {
            if self.assign.contains_key(&other) {
                let t = self.assign.get(&other).cloned().unwrap();
                self.unify_into(v, t);
                return;
            }
            self.assign.insert(other, Level::Var(v));
            return;
        }
        self.assign.insert(v, target);
    }

    fn unify_pair(&mut self, a: Level, b: Level) {
        let a = self.normalize(a);
        let b = self.normalize(b);
        match (&a, &b) {
            (Level::Zero, Level::Zero) => {}
            (Level::Succ(a1), Level::Succ(b1)) => self.unify_pair(*a1.clone(), *b1.clone()),
            (Level::Var(va), _) => self.unify_into(*va, b),
            (_, Level::Var(vb)) => self.unify_into(*vb, a),
            _ => self.leq.push((a, b)),
        }
    }

    pub fn solve(&mut self) -> Result<(), LevelError> {
        let leq: Vec<_> = self.leq.drain(..).collect();
        for (a, b) in leq {
            let a = self.normalize(a);
            let b = self.normalize(b);
            match (&a, &b) {
                (Level::Var(v), _) => self.unify_into(*v, b),
                (_, Level::Var(v)) => self.unify_into(*v, a),
                (Level::Zero, Level::Zero) => {}
                (Level::Succ(a1), Level::Succ(b1)) => self.unify_pair(*a1.clone(), *b1.clone()),
                (Level::Zero, Level::Succ(_)) | (Level::Succ(_), Level::Zero) => {
                    return Err(LevelError::Inconsistent);
                }
                (Level::Succ(_), Level::Succ(_)) => {}
            }
        }

        let mut pending: Vec<(Level, Level)> = self.leq.clone();
        while !pending.is_empty() {
            let mut next = Vec::new();
            for (sub, sup) in &pending {
                let sub = self.normalize(sub.clone());
                let sup = self.normalize(sup.clone());
                match (&sub, &sup) {
                    (Level::Var(v), _) => self.unify_into(*v, sup),
                    (_, Level::Var(v)) => {
                        if let Some(h) = Self::level_height(&sub) {
                            let mut want = Level::Zero;
                            for _ in 0..h {
                                want = want.succ();
                            }
                            self.unify_into(*v, want);
                        } else {
                            next.push((sub, sup));
                        }
                    }
                    (Level::Zero, Level::Zero) => {}
                    (Level::Succ(s1), Level::Succ(s2)) => next.push((*s1.clone(), *s2.clone())),
                    (Level::Zero, Level::Succ(_)) => return Err(LevelError::Inconsistent),
                    _ => next.push((sub, sup)),
                }
            }
            if next.len() == self.leq.len() && next == self.leq {
                break;
            }
            pending = next;
        }
        self.leq = pending;
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
