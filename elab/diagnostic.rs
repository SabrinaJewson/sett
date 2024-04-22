pub(crate) struct SourceFile {
    pub path: String,
    pub data: String,
}

impl SourceFile {
    pub fn warn(&self, loc: impl IntoRange, msg: impl Display) -> Diagnostic {
        self.diagnostic(Level::Warn, loc, msg)
    }
    pub fn error(&self, loc: impl IntoRange, msg: impl Display) -> Diagnostic {
        self.diagnostic(Level::Error, loc, msg)
    }
    pub fn diagnostic(&self, level: Level, loc: impl IntoRange, msg: impl Display) -> Diagnostic {
        let Range { start, end } = loc.into_range(&self.data);
        Diagnostic(if start == end {
            format!("{}:{start}: {level}: {msg}", self.path)
        } else {
            format!("{}:{start}..{end}: {level}: {msg}", self.path)
        })
    }
}

pub(crate) trait IntoRange {
    fn into_range(self, source: &str) -> Range<usize>;
}

impl IntoRange for Range<usize> {
    fn into_range(self, _source: &str) -> Range<usize> {
        self
    }
}

impl IntoRange for RangeFrom<usize> {
    fn into_range(self, source: &str) -> Range<usize> {
        self.start..source.len()
    }
}

impl IntoRange for usize {
    fn into_range(self, _source: &str) -> Range<usize> {
        self..self
    }
}

pub(crate) enum Level {
    Warn,
    Error,
}

impl Display for Level {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Self::Warn => f.write_str("warn"),
            Self::Error => f.write_str("error"),
        }
    }
}

pub(crate) struct Diagnostic(String);

use std::fmt;
use std::fmt::Display;
use std::fmt::Formatter;
use std::ops::Range;
use std::ops::RangeFrom;
