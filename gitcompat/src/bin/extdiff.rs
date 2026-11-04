//! `difffold-extdiff`: git external diff helper. Always exits 0 (git reads other codes as failure).
//!
//! Flags before the positional arguments: `--json`, `--json-sidecar FILE`, `--no-unified`.

use gitcompat::extdiff::{run, Opts};
use std::ffi::OsString;
use std::io::Write;

fn main() {
	let mut opts = Opts::from_env();
	let mut pos: Vec<OsString> = Vec::new();
	let mut it = std::env::args_os().skip(1);
	let mut flags_done = false;
	while let Some(a) = it.next() {
		if !flags_done {
			match a.to_str() {
				Some("--json") => {
					opts.json = true;
					continue;
				}
				Some("--no-unified") => {
					opts.show_unified = false;
					continue;
				}
				Some("--json-sidecar") => {
					opts.json_sidecar = it.next().map(Into::into);
					continue;
				}
				Some("--") => {
					flags_done = true;
					continue;
				}
				_ => flags_done = true,
			}
		}
		pos.push(a);
	}
	let out = run(&pos, &opts);
	let stdout = std::io::stdout();
	let mut h = stdout.lock();
	let _ = h.write_all(&out);
	let _ = h.flush();
}
