//! Times difffold's general ordered tree edit distance on tree files written by `fastted_export` or
//! `tools/fastted_adapters/gen_synthetic.py`. Unit costs: insert, delete and relabel cost 1.
//!
//! usage: fastted_bench --pair NAME --mode unknown|threshold [--tau T] [--reps R] <a.tree> <b.tree>
//!
//! `unknown` calls `ted` (the tool searches the threshold itself). `threshold` calls `ted_within` with the
//! supplied `tau`, and reports `NA` with status `above_tau` when the distance exceeds it.
//!
//! Prints CSV rows `tool,mode,pair,phase,rep,us,distance,status` on stdout. `phase` is `prep` (building the
//! `PostTree` index for both trees) or `dist` (the distance call). Rep 0 is an untimed warm-up with status
//! `warmup`. If any run exceeds 60 s the driver prints a `gt60s` row and stops, so the caller can skip the cell.

use difffold::ted::{ted, ted_within, PostTree};
use std::time::{Duration, Instant};

const CELL_LIMIT: Duration = Duration::from_secs(60);

struct Tree {
    label: Vec<u32>,
    parent: Vec<i64>,
}

fn read_tree(path: &str) -> Tree {
    let text = std::fs::read_to_string(path).unwrap_or_else(|e| panic!("read {path}: {e}"));
    let mut lines = text.lines();
    let n: usize = lines
        .next()
        .expect("tree file has a count line")
        .trim()
        .parse()
        .expect("count line is an integer");
    let mut label = Vec::with_capacity(n);
    let mut parent = Vec::with_capacity(n);
    for line in lines.take(n) {
        let mut parts = line.split_whitespace();
        label.push(parts.next().expect("label").parse().expect("label is u32"));
        parent.push(
            parts
                .next()
                .expect("parent")
                .parse()
                .expect("parent is i64"),
        );
    }
    assert_eq!(
        label.len(),
        n,
        "tree file {path} has fewer nodes than its count"
    );
    Tree { label, parent }
}

/// Builds the postorder `PostTree` index from the parent array. Children stay in left-to-right order.
fn build(t: &Tree) -> PostTree {
    let mut kids = vec![Vec::new(); t.label.len()];
    for (i, &p) in t.parent.iter().enumerate() {
        if p >= 0 {
            kids[p as usize].push(u32::try_from(i).expect("node index fits in u32"));
        }
    }
    PostTree::from_kids(t.label.clone(), &kids)
}

struct Args {
    pair: String,
    mode: String,
    tau: Option<u32>,
    reps: u32,
    a: String,
    b: String,
}

fn parse_args() -> Args {
    let mut pair = String::from("pair");
    let mut mode = String::from("unknown");
    let mut tau = None;
    let mut reps = 7;
    let mut files = Vec::new();
    let mut it = std::env::args().skip(1);
    while let Some(arg) = it.next() {
        match arg.as_str() {
            "--pair" => pair = it.next().expect("--pair needs a value"),
            "--mode" => mode = it.next().expect("--mode needs a value"),
            "--tau" => {
                tau = Some(
                    it.next()
                        .expect("--tau needs a value")
                        .parse()
                        .expect("tau is u32"),
                )
            }
            "--reps" => {
                reps = it
                    .next()
                    .expect("--reps needs a value")
                    .parse()
                    .expect("reps is u32")
            }
            _ => files.push(arg),
        }
    }
    let [a, b] = files.as_slice() else {
        panic!("usage: fastted_bench --pair NAME --mode unknown|threshold [--tau T] [--reps R] <a.tree> <b.tree>");
    };
    assert!(
        mode == "unknown" || mode == "threshold",
        "mode is unknown or threshold"
    );
    assert!(
        mode != "threshold" || tau.is_some(),
        "threshold mode needs --tau"
    );
    Args {
        pair,
        mode,
        tau,
        reps,
        a: a.clone(),
        b: b.clone(),
    }
}

fn main() {
    let args = parse_args();
    let ta = read_tree(&args.a);
    let tb = read_tree(&args.b);
    for rep in 0..=args.reps {
        let status_warm = rep == 0;

        let t0 = Instant::now();
        let pa = build(&ta);
        let pb = build(&tb);
        let prep = t0.elapsed();
        let prep_status = if status_warm { "warmup" } else { "ok" };
        println!(
            "difffold,{},{},prep,{rep},{},,{prep_status}",
            args.mode,
            args.pair,
            prep.as_micros()
        );

        let t1 = Instant::now();
        let (dist, status) = if args.mode == "unknown" {
            (Some(ted(&pa, &pb)), "ok")
        } else {
            let tau = args.tau.expect("checked in parse_args");
            match ted_within(&pa, &pb, tau) {
                Some(d) => (Some(d), "ok"),
                None => (None, "above_tau"),
            }
        };
        let dist_t = t1.elapsed();
        let dist_str = dist.map_or_else(|| "NA".to_string(), |d| d.to_string());
        let dist_status = if status_warm { "warmup" } else { status };
        println!(
            "difffold,{},{},dist,{rep},{},{dist_str},{dist_status}",
            args.mode,
            args.pair,
            dist_t.as_micros()
        );

        if prep + dist_t > CELL_LIMIT {
            println!(
                "difffold,{},{},dist,{rep},{},NA,gt60s",
                args.mode,
                args.pair,
                dist_t.as_micros()
            );
            return;
        }
    }
}
