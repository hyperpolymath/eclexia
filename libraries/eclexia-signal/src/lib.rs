// SPDX-License-Identifier: PMPL-1.0-or-later

//! OS signal mapping and parsing utilities.

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Signal {
    Hup,
    Int,
    Quit,
    Term,
    Kill,
    Usr1,
    Usr2,
}

pub fn name(sig: Signal) -> &'static str {
    match sig {
        Signal::Hup => "SIGHUP",
        Signal::Int => "SIGINT",
        Signal::Quit => "SIGQUIT",
        Signal::Term => "SIGTERM",
        Signal::Kill => "SIGKILL",
        Signal::Usr1 => "SIGUSR1",
        Signal::Usr2 => "SIGUSR2",
    }
}

pub fn number(sig: Signal) -> i32 {
    match sig {
        Signal::Hup => 1,
        Signal::Int => 2,
        Signal::Quit => 3,
        Signal::Kill => 9,
        Signal::Usr1 => 10,
        Signal::Term => 15,
        Signal::Usr2 => 12,
    }
}

pub fn from_name(name_in: &str) -> Option<Signal> {
    match name_in.trim().to_ascii_uppercase().as_str() {
        "SIGHUP" | "HUP" => Some(Signal::Hup),
        "SIGINT" | "INT" => Some(Signal::Int),
        "SIGQUIT" | "QUIT" => Some(Signal::Quit),
        "SIGTERM" | "TERM" => Some(Signal::Term),
        "SIGKILL" | "KILL" => Some(Signal::Kill),
        "SIGUSR1" | "USR1" => Some(Signal::Usr1),
        "SIGUSR2" | "USR2" => Some(Signal::Usr2),
        _ => None,
    }
}

pub fn from_number(signal_number: i32) -> Option<Signal> {
    match signal_number {
        1 => Some(Signal::Hup),
        2 => Some(Signal::Int),
        3 => Some(Signal::Quit),
        9 => Some(Signal::Kill),
        10 => Some(Signal::Usr1),
        12 => Some(Signal::Usr2),
        15 => Some(Signal::Term),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_mappings() {
        assert_eq!(name(Signal::Int), "SIGINT");
        assert_eq!(number(Signal::Term), 15);
        assert_eq!(from_name("INT"), Some(Signal::Int));
        assert_eq!(from_number(9), Some(Signal::Kill));
    }
}
