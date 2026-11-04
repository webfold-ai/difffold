# Comparison summary

```
date: 2026-11-04T14:05:13Z
nproc: 4
cpu: Intel(R) Xeon(R) Processor @ 2.10GHz
mem_total_kb: 16477348
kernel: Linux 6.18.44-fc-v233 #1 SMP PREEMPT_DYNAMIC @0
loadavg_at_start: 0.57 0.92 0.97 2/106 6921
rustc: rustc 1.97.0 (2d8144b78 2026-07-07)
cargo_profile: release (opt-level 3, debug=1, no LTO), -j2 builds
git: git version 2.43.0
java: openjdk version "21.0.12.1" 2026-08-18
difftastic: Difftastic 0.72.0 (cargo install --locked --version 0.72.0)
omnidiff:  src_head=ca43e07 profile=ci (release, no LTO, 16 CGUs)
gumtree: 4.0.0-beta4 (GitHub release zip, matcher gumtree-simple default, generators by extension: java-jdt, go-treesitter-ng, c-treesitter-ng)
difffold_src_head: ed61c79
tree-sitter crates: "tree-sitter" "0.25.10" "tree-sitter-c" "0.24.2" "tree-sitter-go" "0.25.0" "tree-sitter-java" "0.23.5"
apeiron: source = "git+https://github.com/webfold-ai/apeiron?rev=07ab506#07ab506eb5e8639cf35c9c30a7b87a9ea3b65d9b"
threads: all tools single-threaded except the JVM (GC and JIT threads) and difft (rayon, default); no taskset
limits: 60 s wall per run (SIGKILL); apted worker under prlimit --as=8GiB; zs gated at n*m>25e6 nodes; dfold-cli internal 55 s deadline
cost_model: git/difft/gumtree/omnidiff own models; difffold and selkow unit cost per node (top-down); zs unit ins/del/relabel (general TED); apted: omnidiff's rename-cost model
input_representation: tree-sitter CST incl. anonymous tokens, leaf label = (kind, text), inner label = kind (difffold, selkow, zs); omnidiff/apted use omnidiff's own Code trees; difft its own syntax tree; gumtree its own generators
```

## Wall time per tool (ms, median of reps, process start to exit)

| tool | objective | ok | failed | fallback | total | median | p90 | p99 | max |
|---|---|---|---|---|---|---|---|---|---|
| difffold | top-down Selkow (exact) | 80 | 0 | 0 | 1105 | 9.5 | 21.1 | 103.9 | 103.9 |
| diffsitter | AST node diff (tree-sitter and own) | 80 | 0 | 0 | 2215 | 16.2 | 37.7 | 553.1 | 553.1 |
| difftastic | syntax graph shortest-path (own) | 80 | 0 | 0 | 7267 | 40.4 | 128.0 | 1540.7 | 1540.7 |

## Ratio to difffold (tool time / difffold time, fixtures both completed)

| tool | n | median | min | max | total tool / total difffold |
|---|---|---|---|---|---|
| diffsitter | 80 | 1.4 | 0.76 | 5.5 | 2.0 |
| difftastic | 80 | 3.8 | 1.78 | 58.5 | 6.6 |
