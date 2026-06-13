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
        let len = self.bindings.len();
        match len.checked_sub(1).and_then(|top| top.checked_sub(index)) {
            Some(pos) => &self.bindings[pos],
            None => panic!("de Bruijn index {index} out of range (env len {len})"),
        }
    }

    pub fn extend(&self, value: Value<'scope>) -> Self {
        let mut env = self.clone();
        env.bindings.push(value);
        env
    }

    pub fn len(&self) -> usize {
        self.bindings.len()
    }

    pub fn is_empty(&self) -> bool {
        self.bindings.is_empty()
    }
}
