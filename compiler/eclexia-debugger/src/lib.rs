// SPDX-License-Identifier: MPL-2.0
// Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Interactive debugger for Eclexia programs.

#![forbid(unsafe_code)]
pub mod breakpoint;
pub mod inspection;
pub mod session;

pub use session::{ContinueResult, DebugSession};
