use std::collections::HashMap;

use crate::term::{Name, TermId};

#[derive(Clone, Debug)]
pub enum Entry<'scope> {
    Def {
        ty: TermId<'scope>,
        body: TermId<'scope>,
    },
    Axiom {
        ty: TermId<'scope>,
    },
}

#[derive(Clone, Default)]
pub struct Signature<'scope> {
    entries: HashMap<Name, Entry<'scope>>,
}

impl<'scope> Signature<'scope> {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn insert_def(&mut self, name: Name, ty: TermId<'scope>, body: TermId<'scope>) {
        self.entries
            .insert(name, Entry::Def { ty, body });
    }

    pub fn insert_axiom(&mut self, name: Name, ty: TermId<'scope>) {
        self.entries.insert(name, Entry::Axiom { ty });
    }

    pub fn get(&self, name: &Name) -> Option<&Entry<'scope>> {
        self.entries.get(name)
    }
}
