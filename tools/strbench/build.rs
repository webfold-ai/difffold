//! Compiles Edlib and WFA2-lib from a source checkout into a static archive.
//!
//! The checkout is not part of this repository. Point `STRBENCH_EXT` at the
//! directory holding the `edlib/` and `WFA2-lib/` source trees.

use std::env;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

fn run(cmd: &mut Command) {
    let status = cmd
        .status()
        .unwrap_or_else(|e| panic!("failed to run {cmd:?}: {e}"));
    assert!(status.success(), "command failed: {cmd:?}");
}

fn c_sources(dir: &Path, out: &mut Vec<PathBuf>) {
    for entry in fs::read_dir(dir).unwrap_or_else(|e| panic!("read {}: {e}", dir.display())) {
        let path = entry.expect("dir entry").path();
        if path.extension().is_some_and(|ext| ext == "c") {
            out.push(path);
        }
    }
}

fn main() {
    println!("cargo:rerun-if-env-changed=STRBENCH_EXT");
    println!("cargo:rerun-if-changed=csrc/shim.cpp");
    println!("cargo:rerun-if-changed=build.rs");
    println!("cargo:rustc-check-cfg=cfg(strbench_no_externals)");

    // Without the external sources, Edlib and WFA2-lib are not built. The bench reports their rows as
    // `not-built`, and the RapidFuzz and difffold rows are unaffected.
    let Some(ext) = env::var_os("STRBENCH_EXT").map(PathBuf::from) else {
        println!("cargo:rustc-cfg=strbench_no_externals");
        return;
    };
    let out_dir = PathBuf::from(env::var("OUT_DIR").expect("OUT_DIR"));
    let cc = env::var("CC").unwrap_or_else(|_| "cc".to_string());
    let cxx = env::var("CXX").unwrap_or_else(|_| "c++".to_string());
    let ar = env::var("AR").unwrap_or_else(|_| "ar".to_string());

    let edlib_root = ext.join("edlib/edlib");
    let wfa_root = ext.join("WFA2-lib");

    let mut objects = Vec::new();
    let mut compile = |compiler: &str, src: &Path, include_dirs: &[PathBuf], extra: &[&str]| {
        let stem = src.file_stem().and_then(|s| s.to_str()).expect("stem");
        let parent = src
            .parent()
            .and_then(|p| p.file_name())
            .and_then(|s| s.to_str())
            .unwrap_or("root");
        let obj = out_dir.join(format!("{parent}_{stem}.o"));
        let mut cmd = Command::new(compiler);
        cmd.arg("-c")
            .arg("-O3")
            .arg("-DNDEBUG")
            .arg("-w")
            .arg("-fPIC");
        for inc in include_dirs {
            cmd.arg("-I").arg(inc);
        }
        cmd.args(extra).arg(src).arg("-o").arg(&obj);
        run(&mut cmd);
        objects.push(obj);
    };

    // Edlib: a single C++ translation unit.
    let edlib_inc = edlib_root.join("include");
    compile(
        &cxx,
        &edlib_root.join("src/edlib.cpp"),
        std::slice::from_ref(&edlib_inc),
        &["-std=c++11"],
    );

    // WFA2-lib: every module source under its four library directories.
    let mut wfa_files = Vec::new();
    for dir in ["alignment", "system", "utils", "wavefront"] {
        c_sources(&wfa_root.join(dir), &mut wfa_files);
    }
    wfa_files.sort();
    for src in &wfa_files {
        compile(&cc, src, std::slice::from_ref(&wfa_root), &["-std=gnu99"]);
    }

    // Shim linking the two libraries to plain C signatures.
    compile(
        &cxx,
        Path::new("csrc/shim.cpp"),
        &[edlib_inc, wfa_root],
        &["-std=c++11"],
    );

    let archive = out_dir.join("libstrbench_ext.a");
    let _ = fs::remove_file(&archive);
    let mut cmd = Command::new(&ar);
    cmd.arg("crs").arg(&archive);
    cmd.args(&objects);
    run(&mut cmd);

    println!("cargo:rustc-link-search=native={}", out_dir.display());
    println!("cargo:rustc-link-lib=static=strbench_ext");
    println!("cargo:rustc-link-lib=stdc++");
    println!("cargo:rustc-link-lib=m");
    println!("cargo:rustc-link-lib=pthread");
}
