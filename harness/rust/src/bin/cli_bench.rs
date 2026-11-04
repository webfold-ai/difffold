//! Cold-process benchmark driver. Runs each external CLI per fixture as a fresh process and
//! records wall clock, user and system CPU, and peak RSS from `wait4`, plus exit status, timeout
//! and fallback flags.
//!
//! usage: cli_bench --manifest M.tsv --tools T.tsv --out OUT.csv [--timeout-s 60] [--max-reps 5]
//!                  [--slow-ms 1000] [--seed N] [--tmp DIR]
//!
//! Tool order is shuffled for every repetition round of every fixture (seeded). A tool that
//! timed out, failed, or took longer than --slow-ms in a round is not repeated beyond round 3
//! (round 1 when it timed out), so slow tools get 3 samples and fast ones get --max-reps.

use std::collections::HashSet;
use std::fs::{self, File};
use std::io::Write;
use std::process::{Command, Stdio};
use std::sync::mpsc;
use std::time::{Duration, Instant};

struct Tool {
    name: String,
    objective: String,
    langs: Vec<String>,
    ok_codes: Vec<i32>,
    marker: String,
    keep: bool,
    env: Vec<(String, String)>,
    cmd: Vec<String>,
    rounds: usize,
}

struct Fx {
    id: String,
    dataset: String,
    fixture: String,
    lang: String,
    before: String,
    after: String,
    bytes_b: String,
    bytes_a: String,
    omni_ms: String,
}

struct Sample {
    wall: f64,
    user: f64,
    sys: f64,
    rss: i64,
    code: i32,
    sig: i32,
    timeout: bool,
}

fn run_once(t: &Tool, f: &Fx, tmp: &str, tmo: f64) -> Sample {
    let args: Vec<String> = t.cmd[1..].iter().map(|a| a.replace("{B}", &f.before).replace("{A}", &f.after)).collect();
    let so = File::create(format!("{tmp}/stdout")).unwrap();
    let se = File::create(format!("{tmp}/stderr")).unwrap();
    let mut c = Command::new(&t.cmd[0]);
    c.args(&args).stdin(Stdio::null()).stdout(so).stderr(se).env("LC_ALL", "C");
    for (k, v) in &t.env {
        c.env(k, v);
    }
    let t0 = Instant::now();
    let child = match c.spawn() {
        Ok(ch) => ch,
        Err(_) => return Sample { wall: 0.0, user: 0.0, sys: 0.0, rss: 0, code: 127, sig: 0, timeout: false },
    };
    let pid = child.id() as i32;
    let (tx, rx) = mpsc::channel::<()>();
    let wd = std::thread::spawn(move || {
        if rx.recv_timeout(Duration::from_secs_f64(tmo)).is_err() {
            unsafe { libc::kill(pid, libc::SIGKILL) };
            true
        } else {
            false
        }
    });
    let mut status = 0;
    let mut ru: libc::rusage = unsafe { std::mem::zeroed() };
    unsafe { libc::wait4(pid, &mut status, 0, &mut ru) };
    let wall = t0.elapsed().as_secs_f64() * 1e3;
    let _ = tx.send(());
    let timeout = wd.join().unwrap();
    let tv = |t: libc::timeval| t.tv_sec as f64 * 1e3 + t.tv_usec as f64 / 1e3;
    let (code, sig) = if libc::WIFEXITED(status) { (libc::WEXITSTATUS(status), 0) } else { (-1, libc::WTERMSIG(status)) };
    std::mem::forget(child);
    Sample { wall, user: tv(ru.ru_utime), sys: tv(ru.ru_stime), rss: ru.ru_maxrss, code, sig, timeout }
}

fn med(v: &[f64]) -> f64 {
    let mut s = v.to_vec();
    s.sort_by(f64::total_cmp);
    s[s.len() / 2]
}

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
}

fn main() {
    let a: Vec<String> = std::env::args().collect();
    let arg = |k: &str, d: &str| a.iter().position(|x| x == k).map_or(d.to_string(), |i| a[i + 1].clone());
    let (manifest, tools_p, out) = (arg("--manifest", ""), arg("--tools", ""), arg("--out", ""));
    let tmo: f64 = arg("--timeout-s", "60").parse().unwrap();
    let max_reps: usize = arg("--max-reps", "5").parse().unwrap();
    let slow_ms: f64 = arg("--slow-ms", "1000").parse().unwrap();
    let seed: u64 = arg("--seed", "1").parse().unwrap();
    let tmp = arg("--tmp", "/tmp/cli_bench_tmp");
    fs::create_dir_all(&tmp).unwrap();

    let tools: Vec<Tool> = fs::read_to_string(&tools_p)
        .unwrap()
        .lines()
        .filter(|l| !l.starts_with('#') && !l.trim().is_empty())
        .map(|l| {
            let c: Vec<&str> = l.split('\t').collect();
            Tool {
                name: c[0].into(),
                objective: c[1].into(),
                langs: c[2].split(',').map(String::from).collect(),
                ok_codes: c[3].split(',').map(|x| x.parse().unwrap()).collect(),
                marker: c[4].into(),
                keep: c[5] == "1",
                env: c[6].split(';').filter(|s| !s.is_empty() && !s.starts_with("ROUNDS=")).map(|kv| { let (k, v) = kv.split_once('=').unwrap(); (k.into(), v.into()) }).collect(),
                cmd: c[7].split_whitespace().map(String::from).collect(),
                rounds: c[6].split(';').find_map(|kv| kv.strip_prefix("ROUNDS=")).map_or(max_reps, |v| v.parse().unwrap()),
            }
        })
        .collect();
    let fixtures: Vec<Fx> = fs::read_to_string(&manifest)
        .unwrap()
        .lines()
        .skip(1)
        .map(|l| {
            let c: Vec<&str> = l.split('\t').collect();
            Fx { id: c[0].into(), dataset: c[1].into(), fixture: c[2].into(), lang: c[3].into(), before: c[5].into(), after: c[6].into(), bytes_b: c[7].into(), bytes_a: c[8].into(), omni_ms: c[9].into() }
        })
        .collect();

    let mut done = HashSet::new();
    let fresh = !std::path::Path::new(&out).exists();
    if !fresh {
        for l in fs::read_to_string(&out).unwrap().lines().skip(1) {
            let c: Vec<&str> = l.split(',').collect();
            done.insert(format!("{}|{}", c[0], c[2..4].join("/")));
        }
    }
    let mut f = fs::OpenOptions::new().create(true).append(true).open(&out).unwrap();
    if fresh {
        writeln!(f, "tool,objective,dataset,fixture,lang,bytes_b,bytes_a,omni_ms_recorded,loadavg1,reps,order_pos,status,exit_code,timeout,fallback,out_bytes,wall_ms_med,wall_ms_min,wall_ms_max,wall_ms_all,cpu_user_ms_med,cpu_sys_ms_med,maxrss_kb_med,maxrss_kb_max,stdout_line").unwrap();
    }
    let mut rng = Rng(seed.wrapping_mul(0x9E3779B97F4A7C15) | 1);
    for (fi, fx) in fixtures.iter().enumerate() {
        let active: Vec<usize> = (0..tools.len())
            .filter(|&i| (tools[i].langs[0] == "*" || tools[i].langs.contains(&fx.lang)) && !done.contains(&format!("{}|{}/{}", tools[i].name, fx.dataset, fx.fixture)))
            .collect();
        if active.is_empty() {
            continue;
        }
        let load = fs::read_to_string("/proc/loadavg").unwrap_or_default().split(' ').next().unwrap_or("").to_string();
        let mut samples: Vec<Vec<Sample>> = active.iter().map(|_| vec![]).collect();
        let mut pos: Vec<Vec<usize>> = active.iter().map(|_| vec![]).collect();
        let mut fallback = vec![false; active.len()];
        let mut out_bytes = vec![0u64; active.len()];
        let mut line = vec![String::new(); active.len()];
        for round in 0..max_reps {
            let mut order: Vec<usize> = (0..active.len()).collect();
            for i in (1..order.len()).rev() {
                order.swap(i, (rng.next() % (i as u64 + 1)) as usize);
            }
            for (p, &k) in order.iter().enumerate() {
                let t = &tools[active[k]];
                if round >= t.rounds {
                    continue;
                }
                if let Some(last) = samples[k].last() {
                    let bad = last.timeout || !t.ok_codes.contains(&last.code);
                    let slow = samples[k].iter().any(|s| s.wall >= slow_ms);
                    if bad || (slow && round >= 3) {
                        continue;
                    }
                }
                let s = run_once(t, fx, &tmp, tmo);
                if round == 0 {
                    let o = fs::read(format!("{tmp}/stdout")).unwrap_or_default();
                    out_bytes[k] = o.len() as u64;
                    if !t.marker.is_empty() {
                        let e = fs::read(format!("{tmp}/stderr")).unwrap_or_default();
                        let m = t.marker.as_bytes();
                        fallback[k] = o.windows(m.len()).any(|w| w == m) || e.windows(m.len()).any(|w| w == m);
                    }
                    if t.keep {
                        line[k] = String::from_utf8_lossy(&o).lines().next().unwrap_or("").chars().take(600).collect();
                    }
                }
                pos[k].push(p);
                samples[k].push(s);
            }
        }
        for (k, &ti) in active.iter().enumerate() {
            let t = &tools[ti];
            let s = &samples[k];
            if s.is_empty() {
                continue;
            }
            let last = s.last().unwrap();
            let timeout = s.iter().any(|x| x.timeout);
            let status = if timeout {
                "timeout".to_string()
            } else if last.sig != 0 {
                format!("signal_{}", last.sig)
            } else if last.code == 127 && last.wall == 0.0 {
                "spawn_fail".into()
            } else if t.ok_codes.contains(&last.code) {
                "ok".into()
            } else {
                format!("exit_{}", last.code)
            };
            let w: Vec<f64> = s.iter().map(|x| x.wall).collect();
            let rss: Vec<f64> = s.iter().map(|x| x.rss as f64).collect();
            writeln!(
                f,
                "{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{:.3},{:.3},{:.3},{},{:.3},{:.3},{:.0},{:.0},\"{}\"",
                t.name, t.objective, fx.dataset, fx.fixture, fx.lang, fx.bytes_b, fx.bytes_a, fx.omni_ms, load, s.len(),
                pos[k].iter().map(|x| x.to_string()).collect::<Vec<_>>().join(";"),
                status, last.code, timeout, fallback[k], out_bytes[k], med(&w),
                w.iter().cloned().fold(f64::MAX, f64::min), w.iter().cloned().fold(0.0, f64::max),
                w.iter().map(|x| format!("{x:.2}")).collect::<Vec<_>>().join(";"),
                med(&s.iter().map(|x| x.user).collect::<Vec<_>>()), med(&s.iter().map(|x| x.sys).collect::<Vec<_>>()),
                med(&rss), rss.iter().cloned().fold(0.0, f64::max), line[k].replace('"', "'")
            )
            .unwrap();
        }
        f.flush().unwrap();
        if fi % 20 == 0 {
            eprintln!("fixture {}/{} {}", fi + 1, fixtures.len(), fx.id);
        }
    }
}
