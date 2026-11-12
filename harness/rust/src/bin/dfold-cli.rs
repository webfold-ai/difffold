//! End-to-end CLI for difffold and the two in-process reference algorithms.
//!
//! usage: dfold-cli --algo <difffold|difffold-distance|difffold-refine|selkow|zs> [--reps N] [--timeout-s S]
//!                  [--max-cells C] BEFORE AFTER
//!
//! Prints one `key=value` line. With `--reps 1` this is the cold production path and is meant to
//! be timed from outside (wall, CPU, RSS). With `--reps N>1` the phases are re-timed in-process
//! on the already parsed trees and reported as med/min/max (hot view).
//!
//! algo:
//!   difffold           parse + intern + diff_checked (script built and replayed against the
//!                      after-tree, cost asserted). This is difffold's production path.
//!   difffold-distance  parse + intern + diff (no replay).
//!   difffold-refine    difffold's production path (`difffold`) followed by the cross-level
//!                      refinement (`difffold::refine`, all phases): the top-down mapping is
//!                      repaired for moves, reorders, wraps and unwraps.
//!   selkow             parse + flatten + plain Selkow DP (objective-matched reference).
//!   zs                 parse + flatten + Zhang-Shasha (cross-objective reference).

use difffold::{diff, diff_checked, Arena};
use difffold_harness::*;
use std::time::{Duration, Instant};
use tree_sitter::Parser;

fn ms(t: Instant) -> f64 {
    t.elapsed().as_secs_f64() * 1e3
}

fn stat(name: &str, v: &mut [f64], out: &mut String) {
    if v.is_empty() {
        return;
    }
    v.sort_by(f64::total_cmp);
    out.push_str(&format!(
        " {name}_med={:.4} {name}_min={:.4} {name}_max={:.4}",
        v[v.len() / 2],
        v[0],
        v[v.len() - 1]
    ));
}

fn real_main() -> i32 {
    let args: Vec<String> = std::env::args().collect();
    let (mut algo, mut reps, mut tmo, mut max_cells) =
        ("difffold".to_string(), 1usize, 55.0f64, 150_000_000u64);
    let mut files = vec![];
    let mut i = 1;
    while i < args.len() {
        match args[i].as_str() {
            "--algo" => {
                algo = args[i + 1].clone();
                i += 1
            }
            "--reps" => {
                reps = args[i + 1].parse().unwrap();
                i += 1
            }
            "--timeout-s" => {
                tmo = args[i + 1].parse().unwrap();
                i += 1
            }
            "--max-cells" => {
                max_cells = args[i + 1].parse().unwrap();
                i += 1
            }
            f => files.push(f.to_string()),
        }
        i += 1;
    }
    let (bp, ap) = (&files[0], &files[1]);
    let Some(l) = lang(ext_of(bp)) else {
        println!("status=unsupported_lang algo={algo}");
        return 3;
    };
    let (bs, as_) = (std::fs::read(bp).unwrap(), std::fs::read(ap).unwrap());
    let mut parser = Parser::new();
    parser.set_language(&l).unwrap();
    let t0 = Instant::now();
    let (tb, ta) = (
        parser.parse(&bs, None).unwrap(),
        parser.parse(&as_, None).unwrap(),
    );
    let parse_cold = ms(t0);
    let deadline = Instant::now() + Duration::from_secs_f64(tmo);
    let mut out = format!("algo={algo} reps={reps} parse_cold={parse_cold:.4}");
    let (mut parse_v, mut conv_v, mut match_v, mut prod_v) = (vec![], vec![], vec![], vec![]);
    if reps > 1 {
        for _ in 0..reps {
            let t = Instant::now();
            let _ = (
                parser.parse(&bs, None).unwrap(),
                parser.parse(&as_, None).unwrap(),
            );
            parse_v.push(ms(t));
        }
    }
    let status;
    match algo.as_str() {
        "difffold" | "difffold-distance" => {
            let production = algo == "difffold";
            let mut cost = 0;
            let mut sizes = (0, 0);
            for r in 0..reps {
                let mut arena = Arena::new();
                let mut it = Interner::default();
                let t = Instant::now();
                let ids = (
                    convert(tb.root_node(), &bs, &mut arena, &mut it),
                    convert(ta.root_node(), &as_, &mut arena, &mut it),
                );
                let c = ms(t);
                if r == 0 {
                    sizes = (arena.size(ids.0), arena.size(ids.1));
                }
                conv_v.push(c);
                if reps == 1 {
                    // Cold path: only the production (or distance-only) computation.
                    let t = Instant::now();
                    cost = if production {
                        diff_checked(&mut arena, ids.0, ids.1).cost
                    } else {
                        diff(&arena, ids.0, ids.1).cost
                    };
                    prod_v.push(ms(t));
                } else {
                    let t = Instant::now();
                    cost = diff(&arena, ids.0, ids.1).cost;
                    match_v.push(ms(t));
                    let t = Instant::now();
                    let c2 = diff_checked(&mut arena, ids.0, ids.1).cost;
                    prod_v.push(ms(t));
                    assert_eq!(cost, c2);
                }
            }
            out.push_str(&format!(
                " nodes_b={} nodes_a={} cost={cost}",
                sizes.0, sizes.1
            ));
            status = "ok";
        }
        "difffold-refine" => {
            let opts = difffold::refine::Options::FULL;
            let mut sizes = (0, 0);
            let (mut cost, mut pairs, mut moved) = (0, 0, 0);
            let mut refine_v = vec![];
            for r in 0..reps {
                let mut arena = Arena::new();
                let mut it = Interner::default();
                let t = Instant::now();
                let ids = (
                    convert(tb.root_node(), &bs, &mut arena, &mut it),
                    convert(ta.root_node(), &as_, &mut arena, &mut it),
                );
                conv_v.push(ms(t));
                if r == 0 {
                    sizes = (arena.size(ids.0), arena.size(ids.1));
                }
                let run_refine = |arena: &Arena, edit: &difffold::Diff| {
                    let corr = difffold::mapping::correspondence(arena, ids.0, ids.1, &edit.edit);
                    let tr = Instant::now();
                    let bf = difffold::refine::Flat::from_arena(arena, ids.0, |l| it.kind_of(l));
                    let af = difffold::refine::Flat::from_arena(arena, ids.1, |l| it.kind_of(l));
                    let (m, _) = difffold::refine::refine(arena, &bf, &af, &corr, &opts);
                    (ms(tr), m.len(), m.moves(&bf, &af))
                };
                // Production: certified top-down seed, then refinement.
                let t = Instant::now();
                let d = diff_checked(&mut arena, ids.0, ids.1);
                cost = d.cost;
                let (rt, p, mv) = run_refine(&arena, &d);
                prod_v.push(ms(t));
                refine_v.push(rt);
                pairs = p;
                moved = mv;
                if reps > 1 {
                    // Hot view: matching without the replay certificate.
                    let t = Instant::now();
                    let d = diff(&arena, ids.0, ids.1);
                    let _ = run_refine(&arena, &d);
                    match_v.push(ms(t));
                }
            }
            out.push_str(&format!(
                " nodes_b={} nodes_a={} cost={cost} pairs={pairs} moves={moved}",
                sizes.0, sizes.1
            ));
            stat("refine", &mut refine_v, &mut out);
            status = "ok";
        }
        "selkow" | "zs" => {
            let mut res = None;
            let mut sizes = (0, 0);
            let mut st = "ok";
            for r in 0..reps {
                let mut it = Interner::default();
                let t = Instant::now();
                let (fa, fb) = (
                    flatten(tb.root_node(), &bs, &mut it),
                    flatten(ta.root_node(), &as_, &mut it),
                );
                conv_v.push(ms(t));
                sizes = (fa.len(), fb.len());
                if algo == "zs" && (fa.len() as u64) * (fb.len() as u64) > max_cells {
                    st = "skipped_size";
                    break;
                }
                let t = Instant::now();
                let c = if algo == "zs" {
                    zhang_shasha(&fa, &fb, deadline)
                } else {
                    Selkow::new(&fa, &fb, deadline).run()
                };
                match c {
                    Some(c) => {
                        match_v.push(ms(t));
                        res = Some(c);
                    }
                    None => {
                        st = "timeout";
                        break;
                    }
                }
                if r == 0 && reps > 1 && ms(t) > 5000.0 {
                    break;
                }
            }
            out.push_str(&format!(" nodes_b={} nodes_a={}", sizes.0, sizes.1));
            if let Some(c) = res {
                out.push_str(&format!(" cost={c}"));
            }
            status = st;
        }
        _ => {
            println!("status=bad_algo");
            return 2;
        }
    }
    stat("parse", &mut parse_v, &mut out);
    stat("convert", &mut conv_v, &mut out);
    stat("match", &mut match_v, &mut out);
    stat("prod", &mut prod_v, &mut out);
    println!("status={status} {out}");
    match status {
        "ok" => 0,
        "skipped_size" => 5,
        _ => 4,
    }
}

fn main() {
    // Deep trees recurse; run on a big stack.
    let h = std::thread::Builder::new()
        .stack_size(1 << 30)
        .spawn(real_main)
        .unwrap();
    std::process::exit(h.join().unwrap());
}
