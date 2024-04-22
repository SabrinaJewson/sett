#[derive(Default, Clone)]
pub(crate) struct Module {
    pub submodules: Namespace<Module>,
    pub commands: Namespace<Term>,
    pub prefix_terms: Namespace<Term>,
    pub postfix_terms: Namespace<Term>,
    pub children: type_id::Map<Rc<dyn Any>>,
}

#[derive(Clone)]
pub(crate) struct Term {
    left_punctuation: bool,
    right_punctuation: bool,
    // TODO: Params for type inference… that’s hard ;(
    run: Rc<dyn Fn(&SourceFile, usize, usize, &[Module])>,
}

use crate::type_id;
use crate::Namespace;
use crate::SourceFile;
use std::any::Any;
use std::rc::Rc;
