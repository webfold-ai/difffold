//! Transfer-delta comparison: bytes sent and time to make `after` from `before`.
//! usage: syncbench <diffs-dir> <out.csv> [max-pairs]
//! difffold-delta is a line copy/insert delta from the exact line differ. fast_rsync is the rsync
//! algorithm (the receiver's signature is reported separately because it travels the other way).
//! qbsdiff is bsdiff. Every delta is applied to the base and compared with the target.
use difffold::lines::{diff_text, split_lines};
use fast_rsync::{apply, diff, Signature, SignatureOptions};
use flate2::{write::DeflateEncoder, Compression};
use std::io::Write;
use std::path::PathBuf;
use std::time::Instant;

fn varint(out: &mut Vec<u8>, mut v: usize) {
    while v >= 0x80 {
        out.push((v as u8 & 0x7F) | 0x80);
        v >>= 7;
    }
    out.push(v as u8);
}

fn read_varint(d: &[u8], at: &mut usize) -> usize {
    let (mut v, mut sh) = (0usize, 0);
    loop {
        let b = d[*at];
        *at += 1;
        v |= usize::from(b & 0x7F) << sh;
        if b < 0x80 {
            return v;
        }
        sh += 7;
    }
}

/// Ops: 0 = copy n base lines, 1 = skip n base lines, 2 = insert literal (len, bytes).
fn line_delta(base: &[u8], new: &[u8]) -> Vec<u8> {
    let d = diff_text(base, new);
    let (la, lb) = (split_lines(base), split_lines(new));
    let mut out = Vec::new();
    let (mut i, mut j) = (0, 0);
    while i < la.len() || j < lb.len() {
        if i < la.len() && d.deleted[i] {
            let s = i;
            while i < la.len() && d.deleted[i] {
                i += 1;
            }
            out.push(1);
            varint(&mut out, i - s);
        } else if j < lb.len() && d.inserted[j] {
            let s = j;
            let mut lit = Vec::new();
            while j < lb.len() && d.inserted[j] {
                lit.extend_from_slice(lb[j]);
                j += 1;
            }
            let _ = s;
            out.push(2);
            varint(&mut out, lit.len());
            out.extend_from_slice(&lit);
        } else {
            let s = i;
            while i < la.len() && j < lb.len() && !d.deleted[i] && !d.inserted[j] {
                i += 1;
                j += 1;
            }
            out.push(0);
            varint(&mut out, i - s);
        }
    }
    out
}

fn line_apply(base: &[u8], delta: &[u8]) -> Vec<u8> {
    let la = split_lines(base);
    let (mut out, mut i, mut at) = (Vec::new(), 0, 0);
    while at < delta.len() {
        let op = delta[at];
        at += 1;
        let n = read_varint(delta, &mut at);
        match op {
            0 => {
                la[i..i + n].iter().for_each(|l| out.extend_from_slice(l));
                i += n;
            }
            1 => i += n,
            _ => {
                out.extend_from_slice(&delta[at..at + n]);
                at += n;
            }
        }
    }
    out
}

fn deflated(d: &[u8]) -> usize {
    let mut e = DeflateEncoder::new(Vec::new(), Compression::new(6));
    e.write_all(d).unwrap();
    e.finish().unwrap().len()
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let root = PathBuf::from(&args[1]);
    let cap: usize = args.get(3).and_then(|s| s.parse().ok()).unwrap_or(800);
    let mut out = std::fs::File::create(&args[2]).unwrap();
    writeln!(out, "fixture,bytes_before,bytes_after,tool,delta_bytes,deflated_bytes,side_bytes,us,verified").unwrap();
    let mut n = 0;
    'all: for ds in std::fs::read_dir(&root).unwrap().flatten().map(|e| e.path()).filter(|p| p.is_dir()) {
        for fx in std::fs::read_dir(&ds).unwrap().flatten().map(|e| e.path()).filter(|p| p.is_dir()) {
            let find = |p: &str| std::fs::read_dir(&fx).unwrap().flatten().map(|e| e.path()).find(|x| x.file_name().and_then(|f| f.to_str()).is_some_and(|f| f.starts_with(p)));
            let (Some(bp), Some(ap)) = (find("before."), find("after.")) else { continue };
            let (Ok(a), Ok(b)) = (std::fs::read(bp), std::fs::read(ap)) else { continue };
            if a.len() > 3_000_000 || b.len() > 3_000_000 || a == b {
                continue;
            }
            let name = format!("{}/{}", ds.file_name().unwrap().to_string_lossy(), fx.file_name().unwrap().to_string_lossy());
            let mut row = |tool: &str, delta: usize, defl: usize, side: usize, us: f64, ok: bool| {
                writeln!(out, "{name},{},{},{tool},{delta},{defl},{side},{us:.0},{ok}", a.len(), b.len()).unwrap();
            };
            let t = Instant::now();
            let d = line_delta(&a, &b);
            let us = t.elapsed().as_secs_f64() * 1e6;
            row("difffold-line-delta", d.len(), deflated(&d), 0, us, line_apply(&a, &d) == b);

            let t = Instant::now();
            let sig = Signature::calculate(&a, SignatureOptions { block_size: 512, crypto_hash_size: 8 });
            let sigbytes = sig.serialized().len();
            let isig = sig.index();
            let mut delta = Vec::new();
            diff(&isig, &b, &mut delta).unwrap();
            let us = t.elapsed().as_secs_f64() * 1e6;
            let mut rebuilt = Vec::new();
            apply(&a, &delta, &mut rebuilt).unwrap();
            row("rsync-fast_rsync-512", delta.len(), deflated(&delta), sigbytes, us, rebuilt == b);

            let t = Instant::now();
            let mut patch = Vec::new();
            qbsdiff::Bsdiff::new(&a, &b).compare(&mut patch).unwrap();
            let us = t.elapsed().as_secs_f64() * 1e6;
            let mut rebuilt = Vec::new();
            qbsdiff::Bspatch::new(&patch).unwrap().apply(&a, &mut rebuilt).unwrap();
            row("bsdiff-qbsdiff", patch.len(), deflated(&patch), 0, us, rebuilt == b);
            n += 1;
            if n >= cap {
                break 'all;
            }
        }
    }
    eprintln!("{n} pairs");
}
