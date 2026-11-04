//! Independent check of a patch with the real `git apply`, in throwaway directories.
//!
//! Three checks per patch: `git apply --check`, `git apply` in a plain directory, and
//! `git apply --index` in a fresh repository. After the last two the resulting file bytes must
//! equal the after-bytes exactly, the mode must match, and for `--index` the staged blob id must
//! equal `git hash-object` of the after-bytes.

use crate::patch::{scratch_dir, PatchSpec};
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

/// Result of the git checks for one patch.
#[derive(Debug, Clone, Default)]
pub struct CheckResult {
	pub check_ok: bool,
	pub apply_ok: bool,
	pub index_ok: bool,
	/// First failure, if any.
	pub detail: String,
}

impl CheckResult {
	#[must_use]
	pub fn all_ok(&self) -> bool {
		self.check_ok && self.apply_ok && self.index_ok
	}
}

/// A `git` command with a deterministic environment.
#[must_use]
pub fn git(dir: &Path) -> Command {
	let mut c = Command::new("git");
	c.current_dir(dir)
		.env("GIT_CONFIG_GLOBAL", "/dev/null")
		.env("GIT_CONFIG_SYSTEM", "/dev/null")
		.env("GIT_CONFIG_NOSYSTEM", "1")
		.env("GIT_TERMINAL_PROMPT", "0");
	c
}

fn run(mut c: Command) -> Result<Output, String> {
	c.output().map_err(|e| format!("spawn git: {e}"))
}

fn setup(dir: &Path, spec: &PatchSpec, before: &[u8]) -> Result<(), String> {
	if let Some(m) = spec.old_mode {
		let p = dir.join(path_str(&spec.old_path));
		if let Some(par) = p.parent() {
			std::fs::create_dir_all(par).map_err(|e| e.to_string())?;
		}
		std::fs::write(&p, before).map_err(|e| e.to_string())?;
		set_mode(&p, m)?;
	}
	Ok(())
}

fn path_str(p: &[u8]) -> PathBuf {
	use std::os::unix::ffi::OsStrExt;
	PathBuf::from(std::ffi::OsStr::from_bytes(p))
}

fn set_mode(p: &Path, mode: u32) -> Result<(), String> {
	use std::os::unix::fs::PermissionsExt;
	std::fs::set_permissions(p, std::fs::Permissions::from_mode(mode & 0o777)).map_err(|e| e.to_string())
}

fn verify_tree(dir: &Path, spec: &PatchSpec, after: &[u8]) -> Result<(), String> {
	use std::os::unix::fs::PermissionsExt;
	match spec.new_mode {
		Some(m) => {
			let p = dir.join(path_str(&spec.new_path));
			let got = std::fs::read(&p).map_err(|e| format!("result file missing: {e}"))?;
			if got != after {
				let first = got.iter().zip(after).position(|(a, b)| a != b).unwrap_or(got.len().min(after.len()));
				return Err(format!("bytes differ: got {} bytes, want {}, first difference at {first}", got.len(), after.len()));
			}
			let exec = std::fs::metadata(&p).map_err(|e| e.to_string())?.permissions().mode() & 0o111 != 0;
			if exec != (m & 0o111 != 0) {
				return Err(format!("executable bit is {exec}, want {}", m & 0o111 != 0));
			}
			if spec.old_mode.is_some() && spec.old_path != spec.new_path && dir.join(path_str(&spec.old_path)).exists() {
				return Err("old path still exists after rename".into());
			}
		}
		None => {
			if dir.join(path_str(&spec.old_path)).exists() {
				return Err("deleted file still exists".into());
			}
		}
	}
	Ok(())
}

/// Apply `patch` with git in a scratch directory (and a scratch repository) and compare.
///
/// # Panics
/// Panics when scratch directories cannot be created.
#[must_use]
pub fn check_with_git(spec: &PatchSpec, before: &[u8], after: &[u8], patch: &[u8]) -> CheckResult {
	let mut r = CheckResult::default();
	let root = scratch_dir("chk");
	let res = (|| -> Result<(), String> {
		let patch_file = root.join("p.patch");
		std::fs::write(&patch_file, patch).map_err(|e| e.to_string())?;
		let plain = root.join("plain");
		std::fs::create_dir_all(&plain).map_err(|e| e.to_string())?;
		setup(&plain, spec, before)?;
		let mut c = git(&plain);
		c.args(["apply", "--check", "--whitespace=nowarn"]).arg(&patch_file);
		let o = run(c)?;
		if !o.status.success() {
			return Err(format!("git apply --check: {}", String::from_utf8_lossy(&o.stderr).trim()));
		}
		r.check_ok = true;
		let mut c = git(&plain);
		c.args(["apply", "--whitespace=nowarn"]).arg(&patch_file);
		let o = run(c)?;
		if !o.status.success() {
			return Err(format!("git apply: {}", String::from_utf8_lossy(&o.stderr).trim()));
		}
		verify_tree(&plain, spec, after).map_err(|e| format!("git apply result: {e}"))?;
		r.apply_ok = true;

		let repo = root.join("repo");
		std::fs::create_dir_all(&repo).map_err(|e| e.to_string())?;
		let mut c = git(&repo);
		c.args(["init", "-q"]);
		let o = run(c)?;
		if !o.status.success() {
			return Err("git init failed".into());
		}
		setup(&repo, spec, before)?;
		if spec.old_mode.is_some() {
			let mut c = git(&repo);
			c.arg("add").arg("--").arg(path_str(&spec.old_path));
			let o = run(c)?;
			if !o.status.success() {
				return Err(format!("git add: {}", String::from_utf8_lossy(&o.stderr).trim()));
			}
		}
		let mut c = git(&repo);
		c.args(["apply", "--index", "--whitespace=nowarn"]).arg(&patch_file);
		let o = run(c)?;
		if !o.status.success() {
			return Err(format!("git apply --index: {}", String::from_utf8_lossy(&o.stderr).trim()));
		}
		verify_tree(&repo, spec, after).map_err(|e| format!("git apply --index result: {e}"))?;
		if spec.new_mode.is_some() {
			let mut c = git(&repo);
			c.args(["ls-files", "-s", "-z", "--"]).arg(path_str(&spec.new_path));
			let o = run(c)?;
			let ls = String::from_utf8_lossy(&o.stdout).into_owned();
			let blob = ls.split_whitespace().nth(1).unwrap_or("").to_string();
			let af = root.join("after.bin");
			std::fs::write(&af, after).map_err(|e| e.to_string())?;
			let mut c = git(&repo);
			c.arg("hash-object").arg(&af);
			let want = String::from_utf8_lossy(&run(c)?.stdout).trim().to_string();
			if blob != want {
				return Err(format!("index blob {blob} != hash-object {want}"));
			}
		} else {
			let mut c = git(&repo);
			c.args(["ls-files", "--"]).arg(path_str(&spec.old_path));
			if !run(c)?.stdout.is_empty() {
				return Err("deleted path still in index".into());
			}
		}
		r.index_ok = true;
		Ok(())
	})();
	if let Err(e) = res {
		r.detail = e;
	}
	let _ = std::fs::remove_dir_all(&root);
	r
}
