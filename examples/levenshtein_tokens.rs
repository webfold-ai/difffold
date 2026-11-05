//! Prints the unit-cost Levenshtein distance of two token files.
//!
//! Each file holds whitespace-separated `u32` token ids. Without `--limit` the exact distance is
//! printed. With `--limit K` the bounded search is used, which prints `exceeds K` when the distance is
//! larger than `K`.
//!
//! usage: levenshtein_tokens <a.txt> <b.txt> [--limit K]

use std::process::ExitCode;

use difffold::levenshtein::{levenshtein, levenshtein_within_u32};

fn read_tokens(path: &str) -> Result<Vec<u32>, String> {
    let text = std::fs::read_to_string(path).map_err(|e| format!("reading {path}: {e}"))?;
    text.split_whitespace()
        .map(|t| {
            t.parse::<u32>()
                .map_err(|e| format!("{path}: token {t:?}: {e}"))
        })
        .collect()
}

fn run(args: &[String]) -> Result<String, String> {
    let usage = "usage: levenshtein_tokens <a.txt> <b.txt> [--limit K]";
    let (a_path, b_path) = match args {
        [a, b, ..] => (a.as_str(), b.as_str()),
        _ => return Err(usage.to_owned()),
    };
    let limit = match &args[2..] {
        [] => None,
        [flag, k] if flag == "--limit" => Some(
            k.parse::<u32>()
                .map_err(|e| format!("--limit {k:?}: {e}"))?,
        ),
        _ => return Err(usage.to_owned()),
    };
    let a = read_tokens(a_path)?;
    let b = read_tokens(b_path)?;
    Ok(match limit {
        None => levenshtein(&a, &b).to_string(),
        Some(k) => match levenshtein_within_u32(&a, &b, k) {
            Some(d) => d.to_string(),
            None => format!("exceeds {k}"),
        },
    })
}

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    match run(&args) {
        Ok(line) => {
            println!("{line}");
            ExitCode::SUCCESS
        }
        Err(msg) => {
            eprintln!("{msg}");
            ExitCode::FAILURE
        }
    }
}
