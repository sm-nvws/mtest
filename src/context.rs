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
        let len = self.types.len();
        match len.checked_sub(1).and_then(|top| top.checked_sub(index)) {
            Some(pos) => &self.types[pos],
            None => panic!("de Bruijn index {index} out of range (context len {len})"),
        }
    }

    pub fn extend(&self, ty: Value<'scope>) -> Self {
        let mut ctx = self.clone();
        ctx.types.push(ty);
        ctx
    }

    pub fn len(&self) -> usize {
        self.types.len()
    }

    pub fn is_empty(&self) -> bool {
        self.types.is_empty()
    }
}
