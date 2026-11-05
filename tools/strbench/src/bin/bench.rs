//! Runs one tool on one matrix cell and prints one TSV line.
//!
//! Usage:
//! `bench --job exact|bounded --tool edlib|wfa|rapidfuzz --len N --alphabet 2|4|256|sparse
//!        --regime <name> [--k K] [--pairs P] [--reps R] [--seed S]`
//!
//! Each pair is checked against an independent oracle before timing. Pairs where the tool
//! disagrees are excluded from timing and printed to stderr. Timing covers only the calls to
//! the tool, with inputs already converted to the representation each tool reads.

use std::hint::black_box;
use std::time::Instant;

use strbench::{
    alphabet, edlib, edlib_bytes, make_pair, oracle_bounded, oracle_exact, random_seq, rapidfuzz,
    wfa, wfa_bytes, Answer, Regime, Rng,
};

/// Work budget, in DP cells, for the exact-distance oracle before falling back to consensus.
const ORACLE_BUDGET: u64 = 400_000_000;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Tool {
    Edlib,
    Wfa,
    RapidFuzz,
}

impl Tool {
    fn parse(s: &str) -> Tool {
        match s {
            "edlib" => Tool::Edlib,
            "wfa" => Tool::Wfa,
            "rapidfuzz" => Tool::RapidFuzz,
            other => panic!("unknown tool {other}"),
        }
    }
    fn name(self) -> &'static str {
        match self {
            Tool::Edlib => "edlib",
            Tool::Wfa => "wfa",
            Tool::RapidFuzz => "rapidfuzz",
        }
    }
}

struct Opts {
    describe: bool,
    exact: bool,
    tool: Tool,
    len: usize,
    sparse: bool,
    sigma: usize,
    regime: Regime,
    k: usize,
    pairs: usize,
    reps: usize,
    seed: u64,
}

fn parse_args() -> Opts {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let mut o = Opts {
        describe: false,
        exact: false,
        tool: Tool::RapidFuzz,
        len: 16,
        sparse: false,
        sigma: 2,
        regime: Regime::Equal,
        k: 1,
        pairs: 5,
        reps: 7,
        seed: 1,
    };
    let mut i = 0;
    while i < args.len() {
        let val = || {
            args.get(i + 1)
                .unwrap_or_else(|| panic!("missing value for {}", args[i]))
                .clone()
        };
        match args[i].as_str() {
            "--job" => {
                o.exact = match val().as_str() {
                    "exact" => true,
                    "bounded" => false,
                    other => panic!("unknown job {other}"),
                }
            }
            "--tool" => o.tool = Tool::parse(&val()),
            "--len" => o.len = val().parse().expect("len"),
            "--alphabet" => match val().as_str() {
                "sparse" => o.sparse = true,
                s => o.sigma = s.parse().expect("alphabet"),
            },
            "--regime" => {
                o.regime = match val().as_str() {
                    "d<k" => Regime::Below,
                    "d==k" => Regime::Equal,
                    "d==k+1" => Regime::AboveOne,
                    "d>>k" => Regime::Far,
                    "tiny-prefix-suffix" => Regime::Tiny,
                    "unrelated" => Regime::Unrelated,
                    "d=16" => Regime::Mid16,
                    other => panic!("unknown regime {other}"),
                }
            }
            "--k" => o.k = val().parse().expect("k"),
            "--pairs" => o.pairs = val().parse().expect("pairs"),
            "--reps" => o.reps = val().parse().expect("reps"),
            "--seed" => o.seed = val().parse().expect("seed"),
            "--describe" => {
                o.describe = true;
                i += 1;
                continue;
            }
            other => panic!("unknown argument {other}"),
        }
        i += 2;
    }
    o
}

struct Pair {
    a: Vec<u32>,
    b: Vec<u32>,
    edlib: Option<(Vec<u8>, Vec<u8>)>,
    wfa: Option<(Vec<u8>, Vec<u8>)>,
}

fn call(tool: Tool, p: &Pair, k: Option<usize>) -> Answer {
    match tool {
        Tool::Edlib => {
            let (a, b) = p.edlib.as_ref().expect("edlib bytes");
            edlib(a, b, k)
        }
        Tool::Wfa => {
            let (a, b) = p.wfa.as_ref().expect("wfa bytes");
            wfa(a, b, k)
        }
        Tool::RapidFuzz => rapidfuzz(&p.a, &p.b, k),
    }
}

fn fmt_answer(a: Answer) -> String {
    match a {
        Answer::Dist(d) => d.to_string(),
        Answer::Exceeds => "exceeds".to_string(),
    }
}

/// The first eight TSV columns: job, tool, length, alphabet, regime, k, designed distance, pairs.
fn prefix(o: &Opts) -> String {
    let job = if o.exact { "exact" } else { "bounded" };
    let designed_k = if o.exact { 0 } else { o.k };
    let designed = if o.exact {
        match o.regime {
            Regime::Tiny => "2".to_string(),
            Regime::Mid16 => "16".to_string(),
            _ => "-".to_string(),
        }
    } else {
        o.regime
            .designed_d(o.len, designed_k)
            .map_or("-".to_string(), |d| d.to_string())
    };
    let k = if o.exact {
        "-".to_string()
    } else {
        o.k.to_string()
    };
    let alph = if o.sparse {
        "sparse-u32".to_string()
    } else {
        o.sigma.to_string()
    };
    format!(
        "{job}\t{tool}\t{len}\t{alph}\t{regime}\t{k}\t{designed}\t{pairs}",
        tool = o.tool.name(),
        len = o.len,
        regime = o.regime.name(),
        pairs = o.pairs,
    )
}

/// Prints the result row: the prefix, then good pairs, status, oracle, median realized
/// distance, mismatch count, min/median/max microseconds per pair, and a note.
#[allow(clippy::too_many_arguments)]
fn emit(
    o: &Opts,
    status: &str,
    oracle: &str,
    realized: &str,
    good: usize,
    mism: usize,
    times: &[f64],
    note: &str,
) {
    let (min, med, max) = if times.is_empty() {
        ("-".to_string(), "-".to_string(), "-".to_string())
    } else {
        let mut t = times.to_vec();
        t.sort_by(|x, y| x.partial_cmp(y).expect("finite"));
        (
            format!("{:.3}", t[0]),
            format!("{:.3}", t[t.len() / 2]),
            format!("{:.3}", t[t.len() - 1]),
        )
    };
    println!(
        "{}\t{good}\t{status}\t{oracle}\t{realized}\t{mism}\t{min}\t{med}\t{max}\t{note}",
        prefix(o)
    );
}

fn skip(o: &Opts, status: &str, note: &str) -> ! {
    emit(o, status, "-", "-", 0, 0, &[], note);
    std::process::exit(0)
}

fn main() {
    let o = parse_args();
    if o.describe {
        println!("{}", prefix(&o));
        return;
    }
    if !o.exact && o.k >= o.len {
        skip(&o, "skip", "k >= n: bound is vacuous");
    }
    let mut rng = Rng::new(
        o.seed
            ^ (o.len as u64) << 20
            ^ (o.sigma as u64) << 8
            ^ (o.k as u64) << 40
            ^ o.regime.name().len() as u64,
    );
    let symbols = alphabet(&mut rng, if o.sparse { 4096 } else { o.sigma }, o.sparse);
    let designed_k = if o.exact { 0 } else { o.k };
    let designed = if o.exact {
        match o.regime {
            Regime::Tiny => Some(2),
            Regime::Mid16 => Some(16),
            Regime::Unrelated => None,
            _ => skip(&o, "skip", "regime not used by the exact-distance job"),
        }
    } else {
        o.regime.designed_d(o.len, designed_k)
    };
    if !o.exact && designed.is_none() && o.regime != Regime::Unrelated {
        skip(
            &o,
            "skip",
            "designed distance not applicable at this length and k",
        );
    }

    let mut pairs = Vec::with_capacity(o.pairs);
    for _ in 0..o.pairs {
        let (a, b) = match designed {
            Some(d) => make_pair(&mut rng, o.regime, o.len, d, &symbols),
            None => (
                random_seq(&mut rng, o.len, &symbols),
                random_seq(&mut rng, o.len, &symbols),
            ),
        };
        let edlib_b = edlib_bytes(&a).zip(edlib_bytes(&b));
        let wfa_b = wfa_bytes(&a).zip(wfa_bytes(&b));
        pairs.push(Pair {
            a,
            b,
            edlib: edlib_b,
            wfa: wfa_b,
        });
    }

    let supported = match o.tool {
        Tool::Edlib => pairs.iter().all(|p| p.edlib.is_some()),
        Tool::Wfa => pairs.iter().all(|p| p.wfa.is_some()),
        Tool::RapidFuzz => true,
    };
    if !supported {
        let why = match o.tool {
			Tool::Edlib => "unsupported: symbols must be below 256 (byte strings)",
			Tool::Wfa => "unsupported: WFA2-lib reserves '!' and '?' as end sentinels, so only 253 byte symbols are usable",
			Tool::RapidFuzz => unreachable!(),
		};
        skip(&o, "unsupported", why);
    }

    // Check each pair against the oracle. Expected values are computed outside the timed region.
    let mut expected: Vec<(Answer, bool)> = Vec::with_capacity(pairs.len());
    for p in &pairs {
        let e = if o.exact {
            match oracle_exact(&p.a, &p.b, ORACLE_BUDGET) {
                Some(d) => (Answer::Dist(d), true),
                None => (rapidfuzz(&p.a, &p.b, None), false),
            }
        } else {
            (oracle_bounded(&p.a, &p.b, o.k), true)
        };
        expected.push(e);
    }
    let oracle_kind = if o.exact {
        if expected.iter().all(|e| e.1) {
            "oracle-band"
        } else {
            "consensus-rapidfuzz"
        }
    } else {
        "oracle-band"
    };

    let mut good: Vec<usize> = Vec::new();
    let mut mism = 0usize;
    for (idx, p) in pairs.iter().enumerate() {
        let k = if o.exact { None } else { Some(o.k) };
        let got = call(o.tool, p, k);
        if got == expected[idx].0 {
            good.push(idx);
        } else {
            mism += 1;
            eprintln!(
				"DISAGREE tool={} job={} len={} regime={} k={:?} pair={idx} got={} expected={} oracle={}",
				o.tool.name(),
				if o.exact { "exact" } else { "bounded" },
				o.len,
				o.regime.name(),
				k,
				fmt_answer(got),
				fmt_answer(expected[idx].0),
				oracle_kind,
			);
        }
    }
    let realized = {
        let mut ds: Vec<usize> = expected
            .iter()
            .filter_map(|e| match e.0 {
                Answer::Dist(d) => Some(d),
                Answer::Exceeds => None,
            })
            .collect();
        ds.sort_unstable();
        if ds.is_empty() {
            "-".to_string()
        } else {
            format!("{}", ds[ds.len() / 2])
        }
    };
    if good.is_empty() {
        emit(
            &o,
            "all-disagree",
            oracle_kind,
            &realized,
            0,
            mism,
            &[],
            "every pair disagreed; not timed",
        );
        return;
    }

    let k = if o.exact { None } else { Some(o.k) };
    let run_once = || {
        let mut acc = 0usize;
        for &i in &good {
            let r = call(o.tool, &pairs[i], k);
            acc = acc.wrapping_add(match r {
                Answer::Dist(d) => d,
                Answer::Exceeds => 1,
            });
        }
        black_box(acc)
    };
    // Warm-up, then timed repetitions. Each value is mean microseconds per pair.
    black_box(run_once());
    let mut times = Vec::with_capacity(o.reps);
    for _ in 0..o.reps {
        let t = Instant::now();
        black_box(run_once());
        let us = t.elapsed().as_secs_f64() * 1e6 / good.len() as f64;
        times.push(us);
    }
    let note = if mism > 0 {
        "some pairs excluded; see stderr"
    } else {
        ""
    };
    emit(
        &o,
        "ok",
        oracle_kind,
        &realized,
        good.len(),
        mism,
        &times,
        note,
    );
}
