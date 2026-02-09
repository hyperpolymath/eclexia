// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Source span tracking for error reporting.

/// A span in the source code, representing a range of bytes.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Span {
    /// Start byte offset (inclusive)
    pub start: u32,
    /// End byte offset (exclusive)
    pub end: u32,
}

impl Span {
    /// Create a new span from start and end offsets.
    pub const fn new(start: u32, end: u32) -> Self {
        Self { start, end }
    }

    /// Create an empty span at a position.
    pub const fn empty(pos: u32) -> Self {
        Self { start: pos, end: pos }
    }

    /// Create a dummy span for synthesized nodes.
    pub const fn dummy() -> Self {
        Self { start: 0, end: 0 }
    }

    /// Check if this span is empty.
    pub const fn is_empty(&self) -> bool {
        self.start == self.end
    }

    /// Get the length of this span in bytes.
    pub const fn len(&self) -> u32 {
        self.end - self.start
    }

    /// Merge two spans into one that covers both.
    pub fn merge(self, other: Self) -> Self {
        Self {
            start: self.start.min(other.start),
            end: self.end.max(other.end),
        }
    }

    /// Check if this span contains a byte offset.
    pub const fn contains(&self, offset: u32) -> bool {
        offset >= self.start && offset < self.end
    }

    /// Check if this span overlaps with another.
    pub const fn overlaps(&self, other: &Self) -> bool {
        self.start < other.end && other.start < self.end
    }

    /// Convert to a range for slicing.
    pub fn as_range(&self) -> std::ops::Range<usize> {
        self.start as usize..self.end as usize
    }
}

impl From<std::ops::Range<usize>> for Span {
    fn from(range: std::ops::Range<usize>) -> Self {
        Self {
            start: range.start as u32,
            end: range.end as u32,
        }
    }
}

impl From<std::ops::Range<u32>> for Span {
    fn from(range: std::ops::Range<u32>) -> Self {
        Self {
            start: range.start,
            end: range.end,
        }
    }
}

/// Line and column position in source code (1-indexed).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LineCol {
    /// Line number (1-indexed)
    pub line: u32,
    /// Column number (1-indexed)
    pub col: u32,
}

impl LineCol {
    /// Create a new line:column position.
    pub const fn new(line: u32, col: u32) -> Self {
        Self { line, col }
    }
}

impl std::fmt::Display for LineCol {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}:{}", self.line, self.col)
    }
}

impl Span {
    /// Convert a byte offset to line:column position.
    ///
    /// Returns (1,1) for position 0, and properly handles newlines.
    pub fn offset_to_linecol(source: &str, offset: u32) -> LineCol {
        let offset = offset as usize;
        let mut line = 1u32;
        let mut col = 1u32;
        let mut pos = 0;

        for ch in source.chars() {
            if pos >= offset {
                break;
            }
            if ch == '\n' {
                line += 1;
                col = 1;
            } else {
                col += 1;
            }
            pos += ch.len_utf8();
        }

        LineCol::new(line, col)
    }

    /// Get the line:column of the start of this span.
    pub fn start_linecol(&self, source: &str) -> LineCol {
        Self::offset_to_linecol(source, self.start)
    }

    /// Get the line:column of the end of this span.
    pub fn end_linecol(&self, source: &str) -> LineCol {
        Self::offset_to_linecol(source, self.end)
    }

    /// Format this span as "line:col" for the start position.
    pub fn format_location(&self, source: &str) -> String {
        let lc = self.start_linecol(source);
        format!("{}:{}", lc.line, lc.col)
    }
}

/// A value with an associated source span.
#[derive(Debug, Clone, Copy)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Spanned<T> {
    /// Source location of the spanned value
    pub span: Span,
    /// The wrapped value
    pub value: T,
}

impl<T> Spanned<T> {
    /// Create a new spanned value.
    pub const fn new(span: Span, value: T) -> Self {
        Self { span, value }
    }

    /// Map the inner value while preserving the span.
    pub fn map<U, F: FnOnce(T) -> U>(self, f: F) -> Spanned<U> {
        Spanned {
            span: self.span,
            value: f(self.value),
        }
    }
}

impl<T> std::ops::Deref for Spanned<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.value
    }
}

impl<T> std::ops::DerefMut for Spanned<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.value
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_span_merge() {
        let a = Span::new(10, 20);
        let b = Span::new(15, 30);
        let merged = a.merge(b);
        assert_eq!(merged.start, 10);
        assert_eq!(merged.end, 30);
    }

    #[test]
    fn test_span_contains() {
        let span = Span::new(10, 20);
        assert!(span.contains(10));
        assert!(span.contains(15));
        assert!(!span.contains(20)); // exclusive end
        assert!(!span.contains(5));
    }
}
