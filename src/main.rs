#![allow(
    clippy::short_circuit_statement,
    clippy::diverging_sub_expression,
    const_item_mutation
)]

fn main() {
    eval::State::new();
}

mod stack;

mod expr;

mod kernel;

mod parse;

mod eval;

#[cfg(test)]
mod tests;
