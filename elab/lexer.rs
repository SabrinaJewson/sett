pub(crate) enum Token {
    /// Whitespace, including control characters, and comments.
    Trivia,
    /// A non-whitespace, non-control, non-quote character.
    Char,
    /// A string literal, normal or raw.
    StringLit,
    /// Something enclosed in balanced brackets.
    Bracketed(Bracket),
}

/// The different kinds of bracket that must be balanced.
#[derive(Clone, Copy)]
pub(crate) enum Bracket {
    Round,
    Square,
    Curly,
    WhiteRound,
    WhiteSquare,
    WhiteCurly,
    Angle,
    DoubleAngle,
}

const BRACKETS: &[(char, char, Bracket)] = &[
    ('(', ')', Bracket::Round),
    ('[', ']', Bracket::Square),
    ('{', '}', Bracket::Curly),
    ('⦅', '⦆', Bracket::WhiteRound),
    ('⟦', '⟧', Bracket::WhiteSquare),
    ('⦃', '⦄', Bracket::WhiteCurly),
    ('⟨', '⟩', Bracket::Angle),
    ('⟪', '⟫', Bracket::DoubleAngle),
];

pub(crate) fn next_token(
    source: &SourceFile,
    offset: &mut usize,
    diagnostics: &mut Vec<Diagnostic>,
) -> Option<Token> {
    let remaining = &source.data[*offset..];
    Some(if remaining.starts_with("//") {
        line_comment(source, offset);
        Token::Trivia
    } else if remaining.starts_with("/*") {
        block_comment(source, offset, diagnostics);
        Token::Trivia
    } else if try_whitespace(source, offset, diagnostics) {
        Token::Trivia
    } else if remaining.starts_with("r\"") || remaining.starts_with("r#") {
        raw_string(source, offset, diagnostics)?;
        Token::StringLit
    } else if remaining.starts_with('"') {
        string(source, offset, diagnostics)?;
        Token::StringLit
    } else if let Some(&(start, end, bracket)) = BRACKETS
        .iter()
        .find(|&&(start, _, _)| remaining.starts_with(start))
    {
        let open_bracket = *offset;
        *offset += start.len_utf8();
        while next_token(source, offset, diagnostics).is_some() {}
        if source.data[*offset..].starts_with(end) {
            *offset += end.len_utf8();
        } else {
            diagnostics.push(source.error(open_bracket..*offset, "unclosed bracket"));
        }
        Token::Bracketed(bracket)
    } else if BRACKETS
        .iter()
        .any(|&(_, end, _)| remaining.starts_with(end))
    {
        return None;
    } else if let Some(c) = remaining.chars().next() {
        *offset += c.len_utf8();
        Token::Char
    } else {
        return None;
    })
}

/// After calling this function, the remaining text, if nonempty,
/// starts with an identifier or `super`.
pub(crate) fn consume_whitespace(
    source: &SourceFile,
    offset: &mut usize,
    diagnostics: &mut Vec<Diagnostic>,
) {
    loop {
        while try_whitespace(source, offset, diagnostics) {}
        if source.data[*offset..].starts_with("//") {
            line_comment(source, offset);
        } else if source.data[*offset..].starts_with("/*") {
            block_comment(source, offset, diagnostics);
        } else {
            break;
        }
    }
}

fn try_whitespace(
    source: &SourceFile,
    offset: &mut usize,
    diagnostics: &mut Vec<Diagnostic>,
) -> bool {
    let c = source.data[*offset..].chars().next();
    let Some(c) = c.filter(|c| c.is_whitespace() || c.is_control()) else {
        return false;
    };
    if !c.is_ascii_whitespace() {
        diagnostics.push(source.error(*offset..*offset + c.len_utf8(), "non-ASCII whitespace"));
    }
    *offset += c.len_utf8();
    true
}

fn line_comment(source: &SourceFile, offset: &mut usize) {
    match source.data[*offset..].find('\n') {
        Some(i) => *offset += i,
        None => *offset = source.data.len(),
    }
}

fn block_comment(source: &SourceFile, offset: &mut usize, diagnostics: &mut Vec<Diagnostic>) {
    let start = *offset;
    *offset += "/*".len();
    let mut remaining = &source.data[*offset..];

    let mut depth = 1;
    while depth != 0 {
        let Some(star) = remaining.find('*') else {
            diagnostics.push(source.error(start.., "unclosed comment"));
            *offset = source.data.len();
            break;
        };
        let mut skip = "*".len();
        if star != 0 && remaining.as_bytes()[star - 1] == b'/' {
            depth += 1;
        } else if remaining.as_bytes().get(star + 1) == Some(&b'/') {
            skip = "*/".len();
            depth -= 1;
        }
        *offset += star + skip;
        remaining = &remaining[star + skip..];
    }
}

fn raw_string(
    source: &SourceFile,
    offset: &mut usize,
    diagnostics: &mut Vec<Diagnostic>,
) -> Option<()> {
    let start = *offset;
    *offset += 1;
    let remaining = &source.data[*offset..];
    let hashes = remaining.trim_start_matches('#').len() - remaining.len();
    *offset += hashes;
    if 256 <= hashes {
        let msg = "raw string literals may have at most 256 hashes";
        diagnostics.push(source.error(start..*offset, msg));
        *offset = source.data.len();
        return None;
    }
    let remaining = match remaining.strip_prefix('"') {
        Some(remaining) => {
            *offset += 1;
            remaining
        }
        None => {
            diagnostics.push(source.error(start..*offset, "raw string literal requires quote"));
            remaining
        }
    };

    const ENDING_BYTES: [u8; 256] = {
        let mut array = [b'#'; 256];
        array[0] = b'"';
        array
    };
    const ENDING: &str = match str::from_utf8(&ENDING_BYTES) {
        Ok(s) => s,
        Err(_) => unreachable!(),
    };
    let Some(raw_string_len) = remaining.find(&ENDING[..hashes + 1]) else {
        diagnostics.push(source.error(start.., "unterminated raw string literal"));
        return None;
    };
    *offset += raw_string_len + 1 + hashes;

    Some(())
}

fn string(
    source: &SourceFile,
    offset: &mut usize,
    diagnostics: &mut Vec<Diagnostic>,
) -> Option<()> {
    let start = *offset;
    *offset += 1;
    let content_start = *offset;
    let mut chars = source.data[*offset..].char_indices();
    *offset += loop {
        match chars.next() {
            Some((i, '"')) => break i + '"'.len_utf8(),
            Some((escape_index, '\\')) => match chars.next() {
                Some((_, 'x' | 'u' | 'n' | 'r' | 't' | 'e' | '0' | '\\')) | None => {}
                Some((_, c)) => {
                    let escape_start = content_start + escape_index;
                    let range = escape_start..escape_start + '\\'.len_utf8() + c.len_utf8();
                    diagnostics.push(source.error(range, "invalid escape sequence"));
                }
            },
            Some((_, _)) => {}
            None => {
                diagnostics.push(source.error(start.., "unterminated string literal"));
                break source.data[*offset..].len();
            }
        }
    };
    Some(())
}

use crate::diagnostic::Diagnostic;
use crate::SourceFile;
use std::str;
