#[derive(Default)]
pub(crate) struct ModuleCommands {
    pub submodules: Namespace<ModuleCommands>,
    pub commands: Namespace<Command>,
    pub children: type_id::Map<Rc<dyn Any>>,
}

pub(crate) struct Command {
    right_punctuation: bool,
    parser: Parser,
}

// TODO: Commands can take doc comments as parameters
pub(crate) type Parser = Rc<
    dyn Fn(
        &SourceFile,
        usize,
        usize,
        &[ModuleCommands],
        &mut Vec<Diagnostic>,
    ) -> (usize, CommandExpansion),
>;

pub(crate) type CommandExpansion =
    Box<dyn FnOnce(&mut ModuleCommands, &mut Vec<Diagnostic>) -> Expansion>;

pub(crate) type Expansion =
    Box<dyn FnOnce(&mut Vec<ModuleCommands>, &mut Module, &mut Vec<Diagnostic>) -> Verifier>;

pub(crate) type Verifier = Box<dyn FnOnce(&[Module], &mut Vec<Diagnostic>)>;

pub(crate) fn run(
    source: SourceFile,
    offset: usize,
    end: usize,
    // TODO: Intern these
    ancestors: &mut Vec<ModuleCommands>,
) -> (Module, Vec<Verifier>, Vec<Diagnostic>) {
    let (command_expansions, mut diagnostics) = parse(source, offset, end, ancestors);

    let mut module_commands = ModuleCommands::default();
    let expansions = command_expansions
        .into_iter()
        .map(|expansion| expansion(&mut module_commands, &mut diagnostics))
        .collect::<Vec<_>>();

    let old_len = ancestors.len();
    ancestors.push(module_commands);
    let mut module = Module::default();
    let verifiers = expansions
        .into_iter()
        .map(|expansion| {
            let verifier = expansion(ancestors, &mut module, &mut diagnostics);
            assert_eq!(ancestors.len(), old_len + 1);
            verifier
        })
        .collect::<Vec<_>>();
    ancestors.pop();

    (module, verifiers, diagnostics)
}

/// The initial pass serves to compile all dependencies declared in this module.
///
/// The returned `Module` does not contain all the items in this module:
/// it only contains items from dependencies,
/// and most notably commands from dependencies,
/// which are useable in submodules
/// (this module is added to the `ancestors` array).
fn parse(
    source: SourceFile,
    mut offset: usize,
    end: usize,
    ancestors: &[ModuleCommands],
) -> (Vec<CommandExpansion>, Vec<Diagnostic>) {
    let mut expansions = Vec::new();
    let mut diagnostics = Vec::new();
    'outer: loop {
        let mut path_start = usize::MAX;
        let mut scopes = ancestors;
        let mut first_segment = true;

        let (vis, command) = loop {
            let old_offset = offset;
            lexer::consume_whitespace(&source, &mut offset, &mut diagnostics);
            if !first_segment && old_offset != offset {
                diagnostics
                    .push(source.error(old_offset..offset, "whitespace cannot appear in paths"));
            }
            if offset == end {
                break 'outer;
            }

            let ident_start = offset;
            if first_segment {
                path_start = ident_start;
            }
            let remaining = &source.data[offset..end];

            let tuple = scopes.iter().rev().find_map(|scope| {
                scope
                    .commands
                    .get_prefix(remaining)
                    .filter(|(_, _, c)| c.right_punctuation)
            });
            if let Some((ident, vis, command)) = tuple {
                offset += ident.len();
                break (vis, command);
            }

            let ident_len = ident::parse_longest(remaining, |_| false);
            assert_ne!(ident_len, 0);
            let (ident, remaining) = remaining.split_at(ident_len);
            offset += ident_len;
            if !remaining.starts_with(':') {
                let command = scopes
                    .iter()
                    .rev()
                    .find_map(|scope| scope.commands.get_exact(ident));
                let Some((vis, command)) = command else {
                    diagnostics.push(source.error(ident_start..offset, "no command found"));
                    break 'outer;
                };
                assert!(!command.right_punctuation);
                break (vis, command);
            }
            offset += b":".len();
            // TODO: `super` support
            // Note that the ancestry *doesn’t* include the current module, unlike usual.
            let submodule = scopes
                .iter()
                .rev()
                .find_map(|scope| scope.submodules.get_exact(ident));
            let Some((vis, submodule)) = submodule else {
                diagnostics.push(source.error(ident_start..offset, "no module found"));
                break 'outer;
            };
            if !first_segment && vis == Visibility::Private {
                diagnostics.push(source.error(ident_start..offset, "module is private"));
            }
            scopes = slice::from_ref(submodule);
            first_segment = false;
        };
        if !first_segment && vis == Visibility::Private {
            diagnostics.push(source.error(path_start..offset, "command is private"));
        }
        let (new_offset, expansion) =
            (command.parser)(&source, offset, end, ancestors, &mut diagnostics);
        if end < new_offset {
            let msg = "command attempted to read more text than it was given";
            diagnostics.push(source.error(path_start..end, msg));
        } else {
            loop {
                match new_offset.cmp(&offset) {
                    cmp::Ordering::Less => {
                        let msg = "command left trailing tokens";
                        diagnostics.push(source.error(new_offset..offset, msg));
                        break;
                    }
                    cmp::Ordering::Equal => break,
                    cmp::Ordering::Greater => {
                        // TODO: Void the errors, somehow
                        lexer::next_token(&source, &mut offset, &mut diagnostics);
                    }
                }
            }
        }
        expansions.push(expansion);
    }
    (expansions, diagnostics)
}

use crate::ident;
use crate::lexer;
use crate::type_id;
use crate::Diagnostic;
use crate::Module;
use crate::Namespace;
use crate::SourceFile;
use crate::Visibility;
use std::any::Any;
use std::cmp;
use std::rc::Rc;
use std::slice;
