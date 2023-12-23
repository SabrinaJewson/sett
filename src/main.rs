#![allow(
    clippy::short_circuit_statement,
    clippy::diverging_sub_expression,
    const_item_mutation
)]

fn main() {
    kernel::State::new();
}

mod stack;

mod expr;

mod kernel;

mod eval;

//mod parse;

//#[cfg(test)]
//mod tests;
