//! `GIT_EXTERNAL_DIFF` / `diff.external` protocol and the review rendering.
//!
//! Git calls the helper with 7 arguments `path old-file old-hex old-mode new-file new-hex new-mode`,
//! or 9 for a rename or copy (the extra two are `new-path` and the extended header text), or with
//! 1 argument (`path`) for an unmerged path. A missing side is `/dev/null` with hex
//! `0000000...` and mode `.`. Output goes to stdout and the exit status must be 0.
//!
//! Two certificates are reported and never conflated: `byte` (the unified diff printed here
//! replays on the old bytes to the new bytes) and `structural` (difffold's edit script replay).

use crate::patch::{apply_patch, is_binary, make_patch, BinaryMode, Outcome, PatchSpec};
use crate::structural::{self, StructOpts};
use std::ffi::OsString;
use std::os::unix::ffi::OsStrExt;
use std::path::PathBuf;

/// Options, normally from the environment.
#[derive(Debug, Clone)]
pub struct Opts {
    pub json: bool,
    pub json_sidecar: Option<PathBuf>,
    pub show_unified: bool,
    pub max_text_bytes: usize,
    pub structural: StructOpts,
}

impl Opts {
    /// Defaults overridden by `DIFFFOLD_*` environment variables.
    #[must_use]
    pub fn from_env() -> Self {
        let num = |k: &str| std::env::var(k).ok().and_then(|v| v.parse::<usize>().ok());
        let mut s = StructOpts::default();
        if let Some(v) = num("DIFFFOLD_MAX_STRUCT_BYTES") {
            s.max_bytes = v;
        }
        s.allow_parse_errors = std::env::var_os("DIFFFOLD_ALLOW_PARSE_ERRORS").is_some();
        Opts {
            json: std::env::var_os("DIFFFOLD_JSON").is_some(),
            json_sidecar: std::env::var_os("DIFFFOLD_JSON_SIDECAR").map(PathBuf::from),
            show_unified: std::env::var_os("DIFFFOLD_NO_UNIFIED").is_none(),
            max_text_bytes: num("DIFFFOLD_MAX_TEXT_BYTES").unwrap_or(64 << 20),
            structural: s,
        }
    }
}

/// One side of a git external diff call.
#[derive(Debug, Clone)]
pub struct Side {
    pub file: Option<PathBuf>,
    pub hex: String,
    pub mode: Option<u32>,
}

/// Parsed protocol arguments.
#[derive(Debug, Clone)]
pub enum Request {
    Unmerged {
        path: String,
    },
    Pair {
        path: String,
        new_path: Option<String>,
        old: Side,
        new: Side,
        rename_header: Option<String>,
    },
}

fn side(file: &OsString, hex: &OsString, mode: &OsString) -> Side {
    let f = if file.as_bytes() == b"/dev/null" {
        None
    } else {
        Some(PathBuf::from(file))
    };
    let mode = std::str::from_utf8(mode.as_bytes())
        .ok()
        .and_then(|m| u32::from_str_radix(m, 8).ok());
    Side {
        file: f,
        hex: hex.to_string_lossy().into_owned(),
        mode,
    }
}

/// Parse the positional arguments.
///
/// # Errors
/// Returns a message for an unsupported argument count.
pub fn parse_request(a: &[OsString]) -> Result<Request, String> {
    let s = |o: &OsString| o.to_string_lossy().into_owned();
    match a.len() {
        1 => Ok(Request::Unmerged { path: s(&a[0]) }),
        2 => Ok(Request::Pair {
            path: s(&a[1]),
            new_path: None,
            old: Side {
                file: Some(PathBuf::from(&a[0])),
                hex: String::new(),
                mode: Some(0o100_644),
            },
            new: Side {
                file: Some(PathBuf::from(&a[1])),
                hex: String::new(),
                mode: Some(0o100_644),
            },
            rename_header: None,
        }),
        7 | 9 => Ok(Request::Pair {
            path: s(&a[0]),
            new_path: if a.len() == 9 { Some(s(&a[7])) } else { None },
            old: side(&a[1], &a[2], &a[3]),
            new: side(&a[4], &a[5], &a[6]),
            rename_header: if a.len() == 9 { Some(s(&a[8])) } else { None },
        }),
        n => Err(format!("expected 1, 2, 7 or 9 arguments, got {n}")),
    }
}

fn jstr(s: &str) -> String {
    let mut o = String::from("\"");
    for c in s.chars() {
        match c {
            '"' => o.push_str("\\\""),
            '\\' => o.push_str("\\\\"),
            '\n' => o.push_str("\\n"),
            '\r' => o.push_str("\\r"),
            '\t' => o.push_str("\\t"),
            c if (c as u32) < 0x20 => o.push_str(&format!("\\u{:04x}", c as u32)),
            c => o.push(c),
        }
    }
    o.push('"');
    o
}

/// The outcome of one helper call, before rendering.
#[derive(Debug, Default)]
pub struct Report {
    pub path: String,
    pub old_hex: String,
    pub new_hex: String,
    pub bytes_before: usize,
    pub bytes_after: usize,
    /// `structural+unified`, `unified`, `binary`, `too_large`, `identical`, `unmerged`, `unreadable`.
    pub route: &'static str,
    pub fallback_reasons: Vec<String>,
    /// `verified`, `failed`, `not_applicable`.
    pub byte_status: &'static str,
    pub byte_detail: String,
    /// `replay_verified` or `not_run`.
    pub structural_status: &'static str,
    pub structural_reason: String,
    pub structural: Option<structural::Summary>,
    /// Structure identical (cost 0) while bytes differ.
    pub structure_equal_bytes_differ: bool,
    pub patch: Vec<u8>,
}

impl Report {
    /// Machine-readable form. It states which certificates hold. The unified diff itself is not
    /// embedded; use the plain rendering for it.
    #[must_use]
    pub fn to_json(&self) -> String {
        let reasons: Vec<String> = self.fallback_reasons.iter().map(|r| jstr(r)).collect();
        let st = match &self.structural {
			Some(s) => format!(
				",\"language\":{},\"cost\":{},\"nodes_before\":{},\"nodes_after\":{},\"parse_errors\":{},\"entries_total\":{},\"entries\":[{}]",
				jstr(s.language),
				s.cost,
				s.nodes_before,
				s.nodes_after,
				s.parse_errors,
				s.entries_total,
				s.entries.iter().map(|e| jstr(e)).collect::<Vec<_>>().join(",")
			),
			None => String::new(),
		};
        format!(
			"{{\"tool\":\"difffold-extdiff\",\"path\":{},\"old_hex\":{},\"new_hex\":{},\"bytes_before\":{},\"bytes_after\":{},\"route\":{},\"fallback_reasons\":[{}],\"patch_bytes\":{},\"patch_included\":false,\"certificates\":{{\"byte\":{{\"holds\":{},\"status\":{},\"detail\":{}}},\"structural\":{{\"holds\":{},\"status\":{},\"reason\":{}{}}},\"structure_equal_bytes_differ\":{},\"note\":{}}}}}",
			jstr(&self.path),
			jstr(&self.old_hex),
			jstr(&self.new_hex),
			self.bytes_before,
			self.bytes_after,
			jstr(self.route),
			reasons.join(","),
			self.patch.len(),
			self.byte_status == "verified",
			jstr(self.byte_status),
			jstr(&self.byte_detail),
			self.structural_status == "replay_verified",
			jstr(self.structural_status),
			jstr(&self.structural_reason),
			st,
			self.structure_equal_bytes_differ,
			jstr("byte and structural certificates are independent; only the byte certificate says the unified diff reproduces the new file exactly"),
		)
    }

    /// Human rendering as bytes. The unified diff section is raw bytes, never lossily decoded.
    #[must_use]
    pub fn to_text(&self, show_unified: bool) -> Vec<u8> {
        let mut o: Vec<u8> = Vec::new();
        let mut line = |s: String| {
            o.extend_from_slice(s.as_bytes());
            o.push(b'\n');
        };
        line(format!(
            "difffold-extdiff: {} ({} -> {} bytes) route={}",
            self.path, self.bytes_before, self.bytes_after, self.route
        ));
        for r in &self.fallback_reasons {
            line(format!("fallback: {r}"));
        }
        line(format!(
            "certificates: byte={} structural={}{}",
            self.byte_status,
            self.structural_status,
            if self.structural_status == "replay_verified" {
                String::new()
            } else {
                format!(" ({})", self.structural_reason)
            }
        ));
        if !self.byte_detail.is_empty() {
            line(format!("byte: {}", self.byte_detail));
        }
        if let Some(s) = &self.structural {
            line(format!(
                "-- structural summary ({}): {} -> {} nodes, tree edit cost {}{}",
                s.language,
                s.nodes_before,
                s.nodes_after,
                s.cost,
                if s.parse_errors {
                    ", PARSE ERRORS: advisory only"
                } else {
                    ""
                }
            ));
            if self.structure_equal_bytes_differ {
                line("   structure unchanged but bytes differ (whitespace or formatting only): only the byte diff is authoritative".into());
            }
            for e in &s.entries {
                line(format!("   {e}"));
            }
            if s.entries_total > s.entries.len() {
                line(format!("   ... {} more", s.entries_total - s.entries.len()));
            }
            line("   (the structural summary is a review aid; the unified diff below is the authoritative change)".into());
        }
        if show_unified && !self.patch.is_empty() {
            line("-- unified diff".into());
            o.extend_from_slice(&self.patch);
        }
        o
    }
}

fn read_side(s: &Side) -> Result<Vec<u8>, String> {
    match &s.file {
        None => Ok(Vec::new()),
        Some(p) => std::fs::read(p).map_err(|e| format!("cannot read {}: {e}", p.display())),
    }
}

/// Run the helper logic for one request.
#[must_use]
pub fn analyze(req: &Request, opts: &Opts) -> Report {
    let (path, new_path, old, new, _hdr) = match req {
        Request::Unmerged { path } => {
            return Report {
                path: path.clone(),
                route: "unmerged",
                byte_status: "not_applicable",
                byte_detail: "unmerged path: git gave no file pair, nothing was diffed".into(),
                structural_status: "not_run",
                structural_reason: "unmerged path".into(),
                ..Report::default()
            };
        }
        Request::Pair {
            path,
            new_path,
            old,
            new,
            rename_header,
        } => (path, new_path, old, new, rename_header),
    };
    let mut r = Report {
        path: path.clone(),
        old_hex: old.hex.clone(),
        new_hex: new.hex.clone(),
        structural_status: "not_run",
        byte_status: "not_applicable",
        ..Report::default()
    };
    let (before, after) = match (read_side(old), read_side(new)) {
        (Ok(b), Ok(a)) => (b, a),
        (Err(e), _) | (_, Err(e)) => {
            r.route = "unreadable";
            r.fallback_reasons.push(e);
            r.structural_reason = "input unreadable".into();
            return r;
        }
    };
    r.bytes_before = before.len();
    r.bytes_after = after.len();
    if before.len() > opts.max_text_bytes || after.len() > opts.max_text_bytes {
        r.route = "too_large";
        r.fallback_reasons.push(format!(
            "input larger than text limit of {} bytes: not diffed, nothing was altered",
            opts.max_text_bytes
        ));
        r.structural_reason = "input too large".into();
        return r;
    }
    if is_binary(&before) || is_binary(&after) {
        r.route = "binary";
        r.fallback_reasons.push(
            "binary input (NUL byte): no text rendering, use `git diff --binary` for a patch"
                .into(),
        );
        r.structural_reason = "binary input".into();
        return r;
    }
    let mut spec = PatchSpec::modify(path);
    if let Some(np) = new_path {
        spec.new_path = np.as_bytes().to_vec();
    }
    spec.old_mode = if old.file.is_some() {
        Some(old.mode.unwrap_or(0o100_644))
    } else {
        None
    };
    spec.new_mode = if new.file.is_some() {
        Some(new.mode.unwrap_or(0o100_644))
    } else {
        None
    };
    match make_patch(&spec, &before, &after, BinaryMode::Refuse) {
        Outcome::Identical => {
            r.route = "identical";
            r.byte_status = "verified";
            r.byte_detail = "inputs are byte-identical".into();
            r.structural_reason = "identical input".into();
            return r;
        }
        Outcome::Text { patch, .. } => {
            match apply_patch(&before, &patch) {
                Ok(out) if out == after => {
                    r.byte_status = "verified";
                    r.byte_detail = "in-process replay of the unified diff on the old bytes equals the new bytes (git apply was not run by this tool)".into();
                }
                Ok(_) => {
                    r.byte_status = "failed";
                    r.byte_detail =
                        "replay produced different bytes: do not trust the unified diff".into();
                }
                Err(e) => {
                    r.byte_status = "failed";
                    r.byte_detail = format!("replay failed: {e}");
                }
            }
            r.patch = patch;
        }
        Outcome::GitBinary { .. } | Outcome::Refused(_) => {
            r.route = "binary";
            r.fallback_reasons.push("patch generation refused".into());
            return r;
        }
    }
    r.route = "unified";
    if old.file.is_none() || new.file.is_none() {
        r.structural_reason = "file added or deleted: nothing to align".into();
        return r;
    }
    let Some(lang) = structural::language_for(path) else {
        r.structural_reason = "no grammar for this extension".into();
        r.fallback_reasons.push(format!(
            "no structural grammar for {path}: plain unified diff"
        ));
        return r;
    };
    let sopts = opts.structural.clone();
    let (b2, a2) = (before.clone(), after.clone());
    let res = std::thread::Builder::new()
        .stack_size(512 << 20)
        .spawn(move || structural::summarize(lang, &b2, &a2, &sopts))
        .map_err(|e| e.to_string())
        .and_then(|h| {
            h.join()
                .map_err(|_| "structural thread panicked".to_string())
        })
        .and_then(|x| x);
    match res {
        Ok(s) => {
            r.structure_equal_bytes_differ = s.cost == 0 && before != after;
            r.structural_status = "replay_verified";
            r.structural_reason = String::new();
            r.route = "structural+unified";
            r.structural = Some(s);
        }
        Err(why) => {
            r.structural_reason = why.clone();
            r.fallback_reasons
                .push(format!("structural summary skipped: {why}"));
        }
    }
    r
}

/// Full helper: analyze and render (JSON when asked).
#[must_use]
pub fn run(args: &[OsString], opts: &Opts) -> Vec<u8> {
    let req = match parse_request(args) {
        Ok(r) => r,
        Err(e) => return format!("difffold-extdiff: {e}\n").into_bytes(),
    };
    let rep = analyze(&req, opts);
    if let Some(p) = &opts.json_sidecar {
        use std::io::Write;
        if let Ok(mut f) = std::fs::OpenOptions::new()
            .create(true)
            .append(true)
            .open(p)
        {
            let _ = writeln!(f, "{}", rep.to_json());
        }
    }
    if opts.json {
        let mut j = rep.to_json().into_bytes();
        j.push(b'\n');
        return j;
    }
    rep.to_text(opts.show_unified)
}
