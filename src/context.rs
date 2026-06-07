use crate::value::Value;

#[derive(Clone, Default)]
pub struct Context<'scope> {
    types: Vec<Value<'scope>>,
}

impl<'scope> Context<'scope> {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn lookup(&self, index: usize) -> &Value<'scope> {
        &self.types[self.types.len() - 1 - index]
    }

    pub fn extend(&self, ty: Value<'scope>) -> Self {
        let mut ctx = self.clone();
        ctx.types.push(ty);
        ctx
    }

    pub fn len(&self) -> usize {
        self.types.len()
    }
}
