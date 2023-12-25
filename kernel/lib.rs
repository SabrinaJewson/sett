#![allow(
    clippy::short_circuit_statement,
    clippy::diverging_sub_expression,
    const_item_mutation,
    clippy::single_match,
    clippy::new_without_default
)]

pub struct Kernel(parse::State);

impl Kernel {
    pub fn new() -> Self {
        Self(parse::State::new())
    }
    pub fn add(&mut self, s: &str) -> Result<(), String> {
        self.0.parse(s)
    }
}

mod stack;

mod expr;

mod kernel;

mod parse;

#[cfg(test)]
mod tests;
