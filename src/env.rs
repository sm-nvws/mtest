use crate::value::Value;

#[derive(Clone, Debug, Default)]
pub struct Env<'scope> {
    bindings: Vec<Value<'scope>>,
}

impl<'scope> Env<'scope> {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn lookup(&self, index: usize) -> &Value<'scope> {
        &self.bindings[self.bindings.len() - 1 - index]
    }

    pub fn extend(&self, value: Value<'scope>) -> Self {
        let mut env = self.clone();
        env.bindings.push(value);
        env
    }

    pub fn len(&self) -> usize {
        self.bindings.len()
    }
}
