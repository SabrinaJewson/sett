mod type_id;
use type_id::TypeId;

mod elab;
use elab::Module;
use elab::Term;

mod command;

mod trie;
use trie::Trie;

mod lexer;

mod core;
use core::ident;
use core::Ident;
use core::Namespace;
use core::Visibility;

mod diagnostic;
use diagnostic::Diagnostic;
use diagnostic::SourceFile;

//#[salsa::jar(db = Db)]
//pub(crate) struct Jar(
//    expand::Context,
//    expand::File,
//    expand::parse,
//    expand::Ident,
//    expand::Module,
//);
//
//pub(crate) trait Db: salsa::DbWithJar<Jar> {
//    fn read_file(&mut self, path: &str) -> Result<String, BoxError>;
//}
//
//#[derive(Default)]
//#[salsa::db(Jar)]
//pub(crate) struct DbImpl {
//    storage: salsa::Storage<Self>,
//}
//
//impl Db for DbImpl {
//    fn read_file(&mut self, path: &str) -> Result<String, BoxError> {
//        todo!()
//    }
//}
//
//impl salsa::Database for DbImpl {}
//
//pub type BoxError = Box<dyn Send + Sync + Error>;
//
//mod core;
////mod elab;
////mod commands;
//mod expand;
//
//use std::error::Error;
