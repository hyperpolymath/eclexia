// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Interactive debugger for Eclexia programs.

pub mod breakpoint;
pub mod inspection;
pub mod session;

pub use session::{DebugSession, ContinueResult};
