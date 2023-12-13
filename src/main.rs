#![allow(clippy::short_circuit_statement, clippy::diverging_sub_expression)]

fn main() {
    eval::new_state();
}

mod eval;
mod expr;
mod kernel;
mod parse;
mod stack;

#[cfg(test)]
mod tests;
