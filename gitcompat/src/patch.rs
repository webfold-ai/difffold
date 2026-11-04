//! Apply-compatible unified patches (byte certificate producer).
//!
//! Lines are split on `\n` only and keep their terminator, so a CR stays inside the line (CRLF is
//! preserved) and "last line without final newline" is a different line from the same text with a
//! newline. That identity rule is what makes `\ No newline at end of file` come out right.
//!
//! Binary data (any NUL byte on either side) never gets a text patch: it is delegated to
//! `git diff --binary --no-index` or refused, per [`BinaryMode`].

use crate::myers;
use std::collections::HashMap;
use std::io::Write;
use std::path::PathBuf;
use std::process::Command;
use std::sync::atomic::{AtomicU64, Ordering};

/// File names, modes and context for one file's patch. A `None` mode means the side does not exist
/// (`/dev/null`).
#[derive(Debug, Clone)]
pub struct PatchSpec {
	pub old_path: Vec<u8>,
	pub new_path: Vec<u8>,
	pub old_mode: Option<u32>,
	pub new_mode: Option<u32>,
	pub context: usize,
	pub myers_budget: u64,
}

impl PatchSpec {
	/// A modification of `path`, mode 100644 on both sides.
	#[must_use]
	pub fn modify(path: &str) -> Self {
		PatchSpec {
			old_path: path.as_bytes().to_vec(),
			new_path: path.as_bytes().to_vec(),
			old_mode: Some(0o100_644),
			new_mode: Some(0o100_644),
			context: 3,
			myers_budget: myers::DEFAULT_BUDGET,
		}
	}
}

/// What to do with binary input.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinaryMode {
	/// Delegate to `git diff --binary --no-index`.
	Git,
	/// Return [`Outcome::Refused`].
	Refuse,
}

/// Counters over a patch.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct PatchStats {
	pub hunks: usize,
	pub added: usize,
	pub removed: usize,
	pub bytes: usize,
	/// Myers ran out of budget somewhere and emitted a replace.
	pub capped: bool,
}

/// Result of [`make_patch`].
#[derive(Debug)]
pub enum Outcome {
	/// Same bytes, same mode, same path. There is nothing to apply and the patch is empty.
	Identical,
	/// Text patch from the in-crate Myers.
	Text { patch: Vec<u8>, stats: PatchStats },
	/// Binary patch produced by git itself.
	GitBinary { patch: Vec<u8> },
	/// No patch was produced, and the reason says why.
	Refused(String),
}

/// True when the data would be treated as binary: any NUL byte.
#[must_use]
pub fn is_binary(data: &[u8]) -> bool {
	data.contains(&0)
}

/// Split into lines that keep their terminating `\n`.
#[must_use]
pub fn split_lines(data: &[u8]) -> Vec<&[u8]> {
	let mut out = Vec::new();
	let mut start = 0;
	for (i, &c) in data.iter().enumerate() {
		if c == b'\n' {
			out.push(&data[start..=i]);
			start = i + 1;
		}
	}
	if start < data.len() {
		out.push(&data[start..]);
	}
	out
}

fn quote_name(prefix: &str, path: &[u8]) -> Vec<u8> {
	let mut full = prefix.as_bytes().to_vec();
	full.extend_from_slice(path);
	let needs = full.iter().any(|&c| c < 0x20 || c == 0x7f || c >= 0x80 || c == b'"' || c == b'\\');
	if !needs {
		return full;
	}
	let mut out = vec![b'"'];
	for &c in &full {
		match c {
			b'"' => out.extend_from_slice(b"\\\""),
			b'\\' => out.extend_from_slice(b"\\\\"),
			b'\t' => out.extend_from_slice(b"\\t"),
			b'\n' => out.extend_from_slice(b"\\n"),
			b'\r' => out.extend_from_slice(b"\\r"),
			0x07 => out.extend_from_slice(b"\\a"),
			0x08 => out.extend_from_slice(b"\\b"),
			0x0c => out.extend_from_slice(b"\\f"),
			0x0b => out.extend_from_slice(b"\\v"),
			c if c < 0x20 || c == 0x7f || c >= 0x80 => out.extend_from_slice(format!("\\{c:03o}").as_bytes()),
			c => out.push(c),
		}
	}
	out.push(b'"');
	out
}

/// `--- name` or `+++ name` line body; names with a space get a trailing tab like git does.
fn marker_name(prefix: &str, path: &[u8]) -> Vec<u8> {
	let mut n = quote_name(prefix, path);
	if n.first() != Some(&b'"') && path.contains(&b' ') {
		n.push(b'\t');
	}
	n
}

fn header(spec: &PatchSpec, similarity: Option<u32>, has_hunks: bool) -> Vec<u8> {
	let mut h = Vec::new();
	let (a_path, b_path) = match (spec.old_mode, spec.new_mode) {
		(None, _) => (&spec.new_path, &spec.new_path),
		(_, None) => (&spec.old_path, &spec.old_path),
		_ => (&spec.old_path, &spec.new_path),
	};
	h.extend_from_slice(b"diff --git ");
	h.extend_from_slice(&quote_name("a/", a_path));
	h.push(b' ');
	h.extend_from_slice(&quote_name("b/", b_path));
	h.push(b'\n');
	match (spec.old_mode, spec.new_mode) {
		(None, Some(m)) => h.extend_from_slice(format!("new file mode {m:o}\n").as_bytes()),
		(Some(m), None) => h.extend_from_slice(format!("deleted file mode {m:o}\n").as_bytes()),
		(Some(o), Some(n)) => {
			if o != n {
				h.extend_from_slice(format!("old mode {o:o}\nnew mode {n:o}\n").as_bytes());
			}
			if spec.old_path != spec.new_path {
				h.extend_from_slice(format!("similarity index {}%\nrename from ", similarity.unwrap_or(0)).as_bytes());
				h.extend_from_slice(&quote_name("", &spec.old_path));
				h.extend_from_slice(b"\nrename to ");
				h.extend_from_slice(&quote_name("", &spec.new_path));
				h.push(b'\n');
			}
		}
		(None, None) => {}
	}
	if has_hunks {
		h.extend_from_slice(b"--- ");
		if spec.old_mode.is_some() {
			h.extend_from_slice(&marker_name("a/", &spec.old_path));
		} else {
			h.extend_from_slice(b"/dev/null");
		}
		h.extend_from_slice(b"\n+++ ");
		if spec.new_mode.is_some() {
			h.extend_from_slice(&marker_name("b/", &spec.new_path));
		} else {
			h.extend_from_slice(b"/dev/null");
		}
		h.push(b'\n');
	}
	h
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Kind {
	Eq,
	Del,
	Ins,
}

fn range_text(start: usize, count: usize) -> String {
	let s = if count == 0 { start } else { start + 1 };
	if count == 1 { format!("{s}") } else { format!("{s},{count}") }
}

fn push_line(out: &mut Vec<u8>, tag: u8, line: &[u8]) {
	out.push(tag);
	out.extend_from_slice(line);
	if line.last() != Some(&b'\n') {
		out.extend_from_slice(b"\n\\ No newline at end of file\n");
	}
}

/// Build the text patch for two non-binary byte strings.
fn text_patch(spec: &PatchSpec, before: &[u8], after: &[u8]) -> (Vec<u8>, PatchStats) {
	let al = split_lines(before);
	let bl = split_lines(after);
	let mut ids: HashMap<&[u8], u32> = HashMap::new();
	let mut ai: Vec<u32> = Vec::with_capacity(al.len());
	for l in &al {
		let n = ids.len() as u32;
		ai.push(*ids.entry(l).or_insert(n));
	}
	let mut bi: Vec<u32> = Vec::with_capacity(bl.len());
	for l in &bl {
		let n = ids.len() as u32;
		bi.push(*ids.entry(l).or_insert(n));
	}
	let r = myers::diff_with_budget(&ai, &bi, spec.myers_budget);

	// Ops with the a/b index consumed before each op.
	let mut ops: Vec<(Kind, usize, usize)> = Vec::new();
	let (mut i, mut j) = (0, 0);
	while i < al.len() || j < bl.len() {
		if i < al.len() && r.del[i] {
			ops.push((Kind::Del, i, j));
			i += 1;
		} else if j < bl.len() && r.ins[j] {
			ops.push((Kind::Ins, i, j));
			j += 1;
		} else {
			ops.push((Kind::Eq, i, j));
			i += 1;
			j += 1;
		}
	}
	let changes: Vec<usize> = ops.iter().enumerate().filter(|(_, o)| o.0 != Kind::Eq).map(|(k, _)| k).collect();
	let mut matched_bytes = 0usize;
	for (k, o) in ops.iter().enumerate() {
		let _ = k;
		if o.0 == Kind::Eq {
			matched_bytes += al[o.1].len();
		}
	}
	let mut stats = PatchStats { capped: r.capped, ..PatchStats::default() };
	let mut body = Vec::new();
	let ctx = spec.context;
	let mut g = 0;
	while g < changes.len() {
		let mut e = g;
		while e + 1 < changes.len() && changes[e + 1] - changes[e] - 1 <= 2 * ctx {
			e += 1;
		}
		let lo = changes[g].saturating_sub(ctx);
		let hi = (changes[e] + ctx + 1).min(ops.len());
		let slice = &ops[lo..hi];
		let oc = slice.iter().filter(|o| o.0 != Kind::Ins).count();
		let nc = slice.iter().filter(|o| o.0 != Kind::Del).count();
		let (as_, bs) = (slice[0].1, slice[0].2);
		body.extend_from_slice(format!("@@ -{} +{} @@\n", range_text(as_, oc), range_text(bs, nc)).as_bytes());
		for o in slice {
			match o.0 {
				Kind::Eq => push_line(&mut body, b' ', al[o.1]),
				Kind::Del => {
					stats.removed += 1;
					push_line(&mut body, b'-', al[o.1]);
				}
				Kind::Ins => {
					stats.added += 1;
					push_line(&mut body, b'+', bl[o.2]);
				}
			}
		}
		stats.hunks += 1;
		g = e + 1;
	}
	let denom = before.len().max(after.len()).max(1);
	let sim = if before == after { 100 } else { ((matched_bytes * 100) / denom).min(99) as u32 };
	let mut out = header(spec, Some(sim), !body.is_empty());
	out.extend_from_slice(&body);
	stats.bytes = out.len();
	(out, stats)
}

/// Make a patch that `git apply` accepts and that turns `before` into `after` exactly.
#[must_use]
pub fn make_patch(spec: &PatchSpec, before: &[u8], after: &[u8], binary: BinaryMode) -> Outcome {
	let same_meta = spec.old_mode == spec.new_mode && spec.old_path == spec.new_path;
	if before == after && same_meta && spec.old_mode.is_some() {
		return Outcome::Identical;
	}
	if is_binary(before) || is_binary(after) {
		if before == after {
			// Mode or rename only: no bytes to carry.
			let out = header(spec, Some(100), false);
			let stats = PatchStats { bytes: out.len(), ..PatchStats::default() };
			return Outcome::Text { patch: out, stats };
		}
		return match binary {
			BinaryMode::Refuse => Outcome::Refused("binary input (NUL byte) and binary mode is refuse".into()),
			BinaryMode::Git => git_binary_patch(spec, before, after),
		};
	}
	let (patch, stats) = text_patch(spec, before, after);
	Outcome::Text { patch, stats }
}

static COUNTER: AtomicU64 = AtomicU64::new(0);

/// A fresh scratch directory under the system temp dir.
///
/// # Panics
/// Panics when the directory cannot be created.
#[must_use]
pub fn scratch_dir(tag: &str) -> PathBuf {
	let n = COUNTER.fetch_add(1, Ordering::Relaxed);
	let d = std::env::temp_dir().join(format!("gitcompat-{tag}-{}-{n}", std::process::id()));
	std::fs::create_dir_all(&d).expect("create scratch dir");
	d
}

fn git_binary_patch(spec: &PatchSpec, before: &[u8], after: &[u8]) -> Outcome {
	if spec.old_mode.is_some() && spec.new_mode.is_some() && spec.old_path != spec.new_path {
		return Outcome::Refused("binary rename with content change is not supported".into());
	}
	let dir = scratch_dir("bin");
	let result = (|| -> Result<Vec<u8>, String> {
		let (a_name, b_name) = (String::from_utf8_lossy(&spec.old_path).into_owned(), String::from_utf8_lossy(&spec.new_path).into_owned());
		let name = if spec.old_mode.is_some() { a_name } else { b_name.clone() };
		let name_b = if spec.new_mode.is_some() { b_name } else { name.clone() };
		let write = |side: &str, rel: &str, data: &[u8], mode: u32| -> Result<String, String> {
			let p = dir.join(side).join(rel);
			std::fs::create_dir_all(p.parent().unwrap()).map_err(|e| e.to_string())?;
			std::fs::write(&p, data).map_err(|e| e.to_string())?;
			#[cfg(unix)]
			{
				use std::os::unix::fs::PermissionsExt;
				std::fs::set_permissions(&p, std::fs::Permissions::from_mode(mode & 0o777)).map_err(|e| e.to_string())?;
			}
			Ok(format!("{side}/{rel}"))
		};
		let a_arg = match spec.old_mode {
			Some(m) => write("a", &name, before, m)?,
			None => "/dev/null".to_string(),
		};
		let b_arg = match spec.new_mode {
			Some(m) => write("b", &name_b, after, m)?,
			None => "/dev/null".to_string(),
		};
		let out = Command::new("git")
			.current_dir(&dir)
			.env("GIT_CONFIG_GLOBAL", "/dev/null")
			.env("GIT_CONFIG_SYSTEM", "/dev/null")
			.args(["diff", "--no-index", "--binary", "--full-index", "--no-prefix", "--no-ext-diff", "--"])
			.arg(&a_arg)
			.arg(&b_arg)
			.output()
			.map_err(|e| format!("cannot run git: {e}"))?;
		if out.status.code() != Some(1) && out.status.code() != Some(0) {
			return Err(format!("git diff failed: {}", String::from_utf8_lossy(&out.stderr)));
		}
		Ok(out.stdout)
	})();
	let _ = std::fs::remove_dir_all(&dir);
	match result {
		Ok(p) if p.windows(16).any(|w| w == b"GIT binary patch") => Outcome::GitBinary { patch: p },
		Ok(_) => Outcome::Refused("git did not produce a binary patch".into()),
		Err(e) => Outcome::Refused(e),
	}
}

/// Count hunk lines of a unified patch (headers excluded).
#[must_use]
pub fn patch_stats(patch: &[u8]) -> PatchStats {
	let lines = split_lines(patch);
	let mut st = PatchStats { bytes: patch.len(), ..PatchStats::default() };
	let mut k = 0;
	while k < lines.len() {
		if let Some((oc, nc)) = parse_hunk_header(lines[k]) {
			st.hunks += 1;
			k += 1;
			let (mut o, mut n) = (0, 0);
			while (o < oc || n < nc) && k < lines.len() {
				match lines[k].first() {
					Some(b' ') => {
						o += 1;
						n += 1;
					}
					Some(b'-') => {
						o += 1;
						st.removed += 1;
					}
					Some(b'+') => {
						n += 1;
						st.added += 1;
					}
					_ => {}
				}
				k += 1;
			}
		} else {
			k += 1;
		}
	}
	st
}

/// Returns `(old_start, old_count, new_start, new_count)` of a hunk header line.
fn parse_hunk_full(line: &[u8]) -> Option<(usize, usize, usize, usize)> {
	let s = std::str::from_utf8(line).ok()?.strip_prefix("@@ -")?;
	let (old, rest) = s.split_once(" +")?;
	let (new, _) = rest.split_once(" @@")?;
	let pr = |t: &str| -> Option<(usize, usize)> {
		match t.split_once(',') {
			Some((a, b)) => Some((a.parse().ok()?, b.parse().ok()?)),
			None => Some((t.parse().ok()?, 1)),
		}
	};
	let (os, oc) = pr(old)?;
	let (ns, nc) = pr(new)?;
	Some((os, oc, ns, nc))
}

fn parse_hunk_header(line: &[u8]) -> Option<(usize, usize)> {
	parse_hunk_full(line).map(|(_, oc, _, nc)| (oc, nc))
}

/// Apply a single-file text patch made by [`make_patch`] to `before`, in process. This is the
/// helper's own byte-certificate check; it is independent of the diff code but is not `git apply`.
///
/// # Errors
/// Returns a description when the patch does not apply or is malformed.
pub fn apply_patch(before: &[u8], patch: &[u8]) -> Result<Vec<u8>, String> {
	let bl = split_lines(before);
	let pl = split_lines(patch);
	let mut out = Vec::with_capacity(before.len());
	let mut cur = 0usize;
	let mut k = 0usize;
	while k < pl.len() && parse_hunk_full(pl[k]).is_none() {
		k += 1;
	}
	while k < pl.len() {
		let Some((os, oc, _, nc)) = parse_hunk_full(pl[k]) else {
			if pl[k].starts_with(b"diff --git") {
				return Err("multi-file patch".into());
			}
			return Err(format!("unexpected line in patch at {k}"));
		};
		k += 1;
		let idx = if oc == 0 { os } else { os - 1 };
		if idx < cur || idx > bl.len() {
			return Err("hunk out of order or out of range".into());
		}
		for l in &bl[cur..idx] {
			out.extend_from_slice(l);
		}
		cur = idx;
		let (mut o, mut n) = (0, 0);
		while o < oc || n < nc {
			let Some(line) = pl.get(k) else { return Err("truncated hunk".into()) };
			k += 1;
			let tag = line[0];
			let mut content: &[u8] = &line[1..];
			if pl.get(k).is_some_and(|l| l.first() == Some(&b'\\')) {
				content = content.strip_suffix(b"\n").unwrap_or(content);
				k += 1;
			}
			match tag {
				b' ' | b'-' => {
					if bl.get(cur).copied() != Some(content) {
						return Err(format!("context mismatch at before line {}", cur + 1));
					}
					cur += 1;
					o += 1;
					if tag == b' ' {
						out.extend_from_slice(content);
						n += 1;
					}
				}
				b'+' => {
					out.extend_from_slice(content);
					n += 1;
				}
				_ => return Err("bad hunk line tag".into()),
			}
		}
	}
	for l in &bl[cur..] {
		out.extend_from_slice(l);
	}
	Ok(out)
}

/// Write helper used by the binaries.
///
/// # Errors
/// Propagates the write error.
pub fn write_all(mut w: impl Write, data: &[u8]) -> std::io::Result<()> {
	w.write_all(data)?;
	w.flush()
}
