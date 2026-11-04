# difffold: incumbent landscape, round 2

Date: 2026-11-04. Scope: tools and papers NOT yet in our comparison
(git myers/patience/histogram/minimal, difftastic 0.64, GumTree 4.0.0-beta4, similar, imara-diff).

## 0. How this was verified

- VERIFIED = fetched this session from crates.io API / PyPI JSON API (versions, licenses, repo URLs), or from a
  web search result that quoted the primary page (arXiv, Springer, PMC, Salzburg DB group).
- UNVERIFIED = from memory of the literature or tool docs; GitHub API/README access was blocked in this sandbox
  ("GitHub access not enabled for this session"), so ALL GitHub-only facts (Go/Java/C tools, licenses, latest
  release tags) are UNVERIFIED and must be re-checked before they go in a report.
- Sandbox reachability observed: crates.io API and PyPI JSON API answer; api.github.com does not. Assume
  Maven Central, npm and proxy.golang.org are NOT reachable (not in the stated allow-list), so Go tools
  (jd, dyff) and Java tools (GumTree variants, RefactoringMiner, ChangeDistiller) need a pre-fetched jar/binary
  or a GitHub release asset, and that path is UNVERIFIED.

### Important version drift to fix first

- difftastic on crates.io is now **0.72.0** (updated 2026-10-29, VERIFIED). Our 4.2x median was against 0.64.
  Re-run against 0.72.0 (and keep 0.64 as a pinned baseline) before publishing, since the speedup claim may shift.
- similar is now 3.2.1 (2026-10-24), imara-diff 0.2.0 (2025-06-14), VERIFIED. Confirm what we pinned.
- Caveat on the headline: GNU/git default Myers uses heuristics and is NOT minimal; only `--minimal`/`-d` is.

## 1. Incumbent table

Legend for "Offline install": C = `cargo install/add` works from crates.io (VERIFIED registry presence);
P = `pip install` works from PyPI (VERIFIED); S = system package or source build only; G = needs GitHub release
or git clone (UNVERIFIED reachability); N = not obtainable/proprietary.

### 1a. Line / sequence differs (same objective family as ours (a))

| Name | Version | Lang | Objective | CLI / library use | License | Offline |
|---|---|---|---|---|---|---|
| dissimilar | 1.0.11 (2026-03-15) | Rust | char-level diff of two strings, semantic-cleanup (diff-match-patch style, NOT minimal-guaranteed) | `dissimilar::diff(a,b)` returns Chunks; lib only | Apache-2.0 | C |
| diff-match-patch (Rust port, distill-io) | 0.3.1 (2026-09-16) | Rust | char/line diff + patch + fuzzy match; Myers bisect with timeout and cleanup | lib: `DiffMatchPatch::new().diff_main(..)`; `diff_lines_to_chars` trick for line mode | MIT | C |
| diff-match-patch (Google, PyPI repack) | 20241021 | Python | same as above, reference semantics (Diff_Timeout default 1s makes results non-minimal unless set to 0) | `dmp = diff_match_patch(); dmp.Diff_Timeout=0; dmp.diff_main(a,b)` | Apache-2.0 (upstream; PyPI license field empty, UNVERIFIED) | P |
| lcs-diff | 0.1.1 (2018-02-13) | Rust | LCS-based line/element diff; dormant | lib `lcs_diff::diff(&a,&b)` | MIT | C |
| diff (diff.rs) | 0.1.13 (2022-06-29) | Rust | LCS/DP diff of slices, O(NM) memory | lib `diff::slice/lines/chars` | MIT OR Apache-2.0 | C |
| diffy | 0.5.2 (2026-08-31) | Rust | Myers line diff + unified patch parse/apply | lib `diffy::create_patch` | MIT OR Apache-2.0 | C |
| seal | 0.1.6 (2025-06-25) | Rust | edit-script / LCS lib | lib | UNVERIFIED (not fetched) | C |
| patience-diff | 0.1.0 (2015) | Rust | patience | lib | UNVERIFIED | C (stale) |
| fastdiff | 0.3.0 | Py (C ext, "pure Python fallback") | Myers-style diff on lists/strings | `fastdiff.compare(a,b)` | MIT | P |
| myers (PyPI) | 1.0.1 | Python | pure-Python Myers diff of lists | `myers.diff(a,b)` | MIT | P |
| cydifflib | 1.2.0 | Python/C | difflib (Ratcliff-Obershelp, NOT minimal) fast port | drop-in difflib | UNVERIFIED | P |
| difflib | stdlib | Python | Ratcliff/Obershelp gestalt matching, junk heuristics, NOT minimal; useful as a "bad baseline" | `difflib.SequenceMatcher(None,a,b,autojunk=False)` | PSF | stdlib |
| GNU diffutils `diff` | 3.10 installed here (VERIFIED `diff --version`) | C | line Myers with heuristics; `-d/--minimal` for minimal; `--speed-large-files` | `diff -d -u a b`; `diff --normal` for edit counting | GPL-3+ | S (present in sandbox) |
| BSD / busybox diff | - | C | Hunt-McIlroy-style (BSD/OpenBSD diff uses Myers variant since 2020, UNVERIFIED) | `diff` | BSD (UNVERIFIED) | S |
| xdiff (inside git) | git version of sandbox | C | Myers/minimal/patience/histogram | `git diff --no-index --minimal`; we already cover this | LGPL-2.1+ (UNVERIFIED) | S |
| libgit2 (`git_diff_*`) | 1.9.x (UNVERIFIED) | C | its own xdiff copy, same algos | `pygit2` (PyPI 1.20.1, GPLv2 w/ linking exception, VERIFIED) binds it: `repo.diff`, `Patch.create_from(old,new)` | GPLv2+LE | P (pygit2 wheels bundle libgit2) |
| JGit DiffAlgorithm | 7.x (UNVERIFIED) | Java | Myers (`MyersDiff`) and Histogram (`HistogramDiff`) - Histogram in JGit is the original of git's | `org.eclipse.jgit.diff.HistogramDiff().diff(cmp, a, b)` | EDL-1.0 (BSD-3, UNVERIFIED) | G/Maven (not reachable) |
| zdiff | UNVERIFIED | ? | Name is ambiguous (zlib-diff `zdiff` shell wrapper in gzip: compares compressed files by piping to diff; there may also be Zig/other projects). Treat as: `zdiff` = gzip's wrapper, no new algorithm | n/a | GPL | S |
| wdiff | 1.2.2 (UNVERIFIED) | C | word-level diff; shells out to GNU diff on a word-per-line transformation | `wdiff a b`, `-3` | GPL-3+ | S |
| git `--word-diff`, `--color-words` | git | C | token split + xdiff on tokens | already measurable via git | LGPL | S |
| delta (git-delta) | 0.20.1 (2026-10-04); old `delta` crate 0.2.1 is an unrelated crate | Rust | pager and syntax highlighter; line diff comes from git, intra-line highlighting uses its own Levenshtein-like alignment (`edits.rs`, UNVERIFIED detail) | `git diff \| delta`; `delta a b` | MIT | C (`cargo install git-delta`) |
| jj diff (jj-lib `diff` module) | jj 0.3x (UNVERIFIED) | Rust | jj implements its own line diff (compacted histogram-style/unique-token anchoring, plus word-level refinement). Algorithm details UNVERIFIED | `jj diff --git`, `jj diff --color-words`; lib `jj_lib::diff::{Diff, find_line_ranges}` | Apache-2.0 | C (`jj-lib` crate; UNVERIFIED that its diff API is public/stable) |
| Sapling / Mercurial bdiff | hg 6.x / sl (UNVERIFIED) | C (bdiff.c) + Rust | Mercurial's `bdiff` is a Ratcliff-Obershelp-like (longest common block, recursive) line diff, NOT minimal; Sapling also has Rust `xdiff` use. Python: `mercurial.bdiff.blocks(a,b)` | `pip install mercurial` (PyPI package exists, UNVERIFIED version) then `from mercurial import bdiff` | GPL-2+ | P (probable) |
| Pijul / libpijul | 1.0-beta (UNVERIFIED) | Rust | `libpijul::diff` Myers on vertices of graph file (UNVERIFIED); objective = patch theory, not text diff | `pijul diff` | GPL-2+ | C (`cargo install pijul`, UNVERIFIED) |
| Darcs | 2.18 (UNVERIFIED) | Haskell | patch theory; line diff via internal Myers-style LCS ("lcs.hs") | `darcs whatsnew` | GPL-2 | S |
| rustc `diff`-like crates: `similar-asserts`, `pretty_assertions` | similar-asserts 2.0.0 (VERIFIED) | Rust | wrappers over similar; not new algorithms | n/a | Apache-2.0 | C |

Notes:
- Only Myers-family codes with `minimal`/no-cutoff settings are valid correctness peers for our (a). Every
  heuristic tool (dissimilar, dmp with timeout, difflib, bdiff, histogram, patience, jj) needs the metric
  "script length / optimal script length", not a pass/fail. Report that ratio.
- diff-match-patch has two traps: Diff_Timeout default 1.0 s, and its post-processing (`diff_cleanupSemantic`)
  deliberately inflates the edit script. Run with timeout 0 and without cleanup for the apples-to-apples row.
- dissimilar always applies semantic cleanup; there is no minimal mode (UNVERIFIED, from README memory).

### 1b. Bit-parallel and wavefront aligners (lower-bound / oracle candidates)

None of these produce line-level `diff` output out of the box. They are edit-distance engines on small
alphabets. Use them as oracles for the optimal distance after mapping each distinct line to a symbol, or
as speed ceilings. Our objective (indel-only, unit cost, no substitution) is LCS distance, which differs from
Levenshtein. Substitution must be disabled or priced 2 to compare like with like.

| Name | Version | Lang | Objective | How to run | License | Offline |
|---|---|---|---|---|---|---|
| Myers 1999 bit-vector (original) | JACM 46(3) | n/a | Levenshtein/k-differences, O(ceil(m/w) n) | implement from paper; Hyyrö 2001 clarifies block extension and gives LCS/indel variant | n/a | n/a |
| Hyyrö bit-parallel LCS (Crochemore/Allison-Dix, Hyyrö 2004) | papers | n/a | LCS length in O(n m / w), the right oracle for indel-only distance (distance = n + m - 2 LCS) | implement; ~50 lines | n/a | n/a |
| edlib | PyPI 1.3.9.post1 (VERIFIED) | C++ (+Py) | Myers 1999 + Ukkonen cutoff, Hirschberg traceback; modes NW/HW/SHW; supports custom equality; edit distance = Levenshtein | `edlib.align(q, t, task="path")` | MIT | P; Rust `edlib_rs` 0.1.2 (2021, MIT/Apache, C) |
| triple_accel | 0.4.0 (2021) | Rust | SIMD Hamming and Levenshtein (+ traceback via `levenshtein_exp`) | lib | MIT | C (stale) |
| editdistancek | 1.0.2 (2023) | Rust | k-bounded Levenshtein | lib | MIT | C |
| editdistance | PyPI 0.8.1 | C++ | Hyyrö-based Levenshtein distance only, no path | `editdistance.eval` | MIT | P |
| rapidfuzz | PyPI 3.14.6 | C++ | Levenshtein/Indel with bit-parallel (Hyyrö) and **`Indel` metric + `Indel.editops`**. Directly matches our objective for strings and sequences of hashables | `from rapidfuzz.distance import Indel; Indel.distance(a,b); Indel.editops(a,b)` | MIT (UNVERIFIED) | P |
| bio (rust-bio) | 4.2.2 (2026-10-12) | Rust | `bio::pattern_matching::myers` (Myers 1999), plus pairwise DP aligners; not diff | lib | MIT | C |
| WFA2-lib | 2.3.x (UNVERIFIED) | C | wavefront alignment (WFA, 2021), edit/gap-linear/affine, O(n s) time; includes BiWFA (low-memory, 2023) | CLI `align_benchmark -a edit-wfa` and `bialign` (UNVERIFIED flag names); C API | MIT (UNVERIFIED) | G |
| pywfa | PyPI 0.6.0 (VERIFIED) | C ext over WFA2-lib | WFA2 bindings | `from pywfa import WavefrontAligner` | UNVERIFIED | P |
| libwfa (rs-wfa) | 0.1.2 (2020, MIT) | Rust | stale bindings to old WFA | lib | MIT | C (stale; prefer building WFA2-lib from GitHub) |
| BiWFA | Bioinformatics 2023 (btad074) | C | O(s) memory optimal alignment | in WFA2-lib | see above | G |
| difflib / python-Levenshtein | 0.27.5 | C++ | Levenshtein distance/editops | `Levenshtein.editops` | GPL-2+ | P (GPL: do not link in our crate) |

Practical oracle plan: map lines to ints; Indel distance via rapidfuzz (P) must equal our edit script length
on every pair. That cross-check is cheap and independent of `similar`. For edlib, alphabets are limited
(edlib handles a byte-sized alphabet, so it cannot take arbitrary line IDs; UNVERIFIED), so prefer rapidfuzz
or WFA2-lib with an int alphabet for line-level work.

### 1c. Tree and syntax-aware differs (same family as ours (b))

| Name | Version | Lang | Objective | How to run | License | Offline |
|---|---|---|---|---|---|---|
| diffsitter | 0.9.0 (2025-04-26, VERIFIED) | Rust | tree-sitter AST, leaf-level LCS diff on "entities" (not a true tree edit distance; matches leaves in order with Myers/dp), no move detection | `cargo install diffsitter`; `diffsitter a.java b.java -o json` (flags UNVERIFIED) | MIT | C |
| difftastic | 0.72.0 (VERIFIED) | Rust | tree-sitter + Dijkstra shortest path over a graph of syntax-node edits; per-file graph limit (`DFT_GRAPH_LIMIT`) forces fallback to line diff, so timing includes fallback cases | `cargo install difftastic`; `difft --display json a b` (JSON gated by `DFT_UNSTABLE=yes`, UNVERIFIED) | MIT | C |
| mergiraf | 0.20.0 (2026-09-26, VERIFIED, now at codeberg.org/mergiraf/mergiraf) | Rust | structured 3-way merge on tree-sitter trees; matching uses GumTree classic (per search snippets); fallback to line merge first | `cargo install mergiraf`; `mergiraf merge base left right`; as git merge driver | GPL-3.0-only (VERIFIED) | C. Note GPL: use as external binary only |
| GumTree 4.0.0-beta4 | have | Java | AST matching (top-down greedy + bottom-up) + edit-script (Chawathe) with move | have | LGPL-3 (UNVERIFIED) | have |
| GumTree variants (classic/greedy, simple, hybrid, stable, "iterative Java matcher" IJM) | in 4.x: `gumtree textdiff -m <matcher>`; names like `gumtree-simple`, `gumtree-hybrid` (UNVERIFIED), IJM from Matsumoto (UNVERIFIED) | Java | tree matching with move/update/insert/delete | `gumtree textdiff -m gumtree-simple-id a b -f JSON` (matcher ids UNVERIFIED) | LGPL-3 | G |
| HyperDiff / HyperAST | Rust (Martinez lab, TU Delft theses 2025) | Rust | GumTree Simple/Greedy/Stable on a lazily-built shared AST | research code on GitHub | UNVERIFIED | G |
| truediff | PLDI 2021 | Scala | linear-time tree diff with move, structural sharing | research artifact | UNVERIFIED | G |
| ChangeDistiller | 2007; Eclipse plugin, later `changedistiller` Maven | Java | AST differencing: bottom-up leaf match by string similarity, then edit script (insert/delete/update/move) tuned to Java source change types | lib `ChangeDistiller.extractChanges` | Apache-2.0 (UNVERIFIED) | G (unreliable) |
| MTDiff | Dotzler & Philippsen, "Move-optimized source code tree differencing", ASE 2016 | Java | edit-script with optimized moves. NOTE: the task brief says "Matsumoto MTDiff"; the ASE 2016 authors are Dotzler/Philippsen. Matsumoto's work is the IJM matcher. UNVERIFIED which is which; fix before citing | research code | UNVERIFIED | G |
| RefactoringMiner | 3.x (UNVERIFIED) | Java | detects refactorings between commits, AST statement-level mapping, not a general diff; its statement mapping is the basis of a precision/recall benchmark (Tsantalis SANER 2025 keynote slides, search snippet) | `RefactoringMiner -c repo commit` (Maven/Gradle build) | MIT (UNVERIFIED) | G |
| SemanticDiff | commercial (VS Code ext, GitHub app) | ? | language-aware diff with move/refactor hiding | no offline path | proprietary | N |
| "Weave" (semantic merge by entity) | UNVERIFIED: could not identify a canonical project; do not cite until the repo is located | ? | ? | ? | ? | ? |
| XYDiff / Diffxml | classic XML tree differs | C++/Java | XML trees with move | UNVERIFIED | ? | G |
| APTED / RTED | PyPI `apted` 1.0.3 (MIT, VERIFIED), Java original (MIT per search snippet); Rust `apted` 0.1.1 (2026-10-01, 32 downloads, immature), `tree-edit-distance` 0.4.0 (2022, MIT, VERIFIED) | Py / Java / Rust | general ordered tree edit distance (Zhang-Shasha class, O(n^3) worst-case time): operations are node insert/delete/rename WITH children promotion. This is a DIFFERENT objective from top-down (Selkow) where a deleted node removes its whole subtree | `from apted import APTED; APTED(t1,t2).compute_edit_distance()` | MIT | P / C |
| zss (Zhang-Shasha) | PyPI 1.2.0 (VERIFIED) | Python | Zhang-Shasha TED, O(n^2 min(depth,leaves)^2) | `zss.simple_distance` | UNVERIFIED | P |
| treediff | 5.0.0 (2024) | Rust | key-value tree diff visitor (serde_json-ish); not an edit-distance | lib | MIT/Apache | C |

A correctness point for (b): to claim "exact" for the Selkow objective we should verify against an independent
implementation. Neither APTED nor zss solve that objective directly. A simple independent check is a textbook
O(n m) top-down DP (Selkow 1977) written in Python on small trees (<=300 nodes) and compared on cost. Cost model
caveat: GumTree and difftastic optimize different objectives (moves, graph path cost), so compare edit-script
cost under one common metric (node ins/del count) after normalizing, and also report runtime separately.

### 1d. Structured-data diffs (JSON/YAML/CSV)

| Name | Version | Lang | Objective | How to run | License | Offline |
|---|---|---|---|---|---|---|
| jd | v2 (UNVERIFIED) | Go | JSON/YAML semantic diff, array LCS options (set/multiset/list), emits own diff format (and RFC 6902/7386) | `jd a.json b.json` | MIT (UNVERIFIED) | G binary release (Go modules proxy likely unreachable) |
| dyff | UNVERIFIED (homeport/dyff) | Go | YAML/Kubernetes-aware, order-aware path diff | `dyff between a.yaml b.yaml` | Apache-2.0 (UNVERIFIED) | G |
| jsondiffpatch | UNVERIFIED (benjamine) | JS | JSON object diff, array LCS | npm | MIT | not via crates/pypi |
| json-patch (crate) | 4.2.0 (VERIFIED) | Rust | RFC 6902 `diff(a,b)` over serde_json values | lib `json_patch::diff` | MIT/Apache-2.0 | C |
| jsondiff (PyPI) | 2.2.1 (VERIFIED, MIT) | Python | JSON-like diff | `jsondiff.diff(a,b)` | MIT | P |
| DeepDiff | 9.1.0 (VERIFIED) | Python | nested Python object diff, `ignore_order` option | `DeepDiff(a,b)` | UNVERIFIED (Zepworks / MIT) | P |
| xdiff PyPI `xdiff` 0.1.0 | VERIFIED | Python | compare data structures/files CLI | CLI | MIT | P (toy) |

Objective note: these are object/value diffs and mostly use LCS on arrays and key matching on maps. They are
not comparable with an edit-script minimizer except via JSON-as-tree conversion (Selkow on JSON trees). Use
them only in the JSON scenario (section 4) with a common cost: count of leaf/ path changes after normalizing.

### 1e. Binary and delta encoders (different objective: smallest delta, not human-readable script)

| Name | Version | Lang | Objective | How to run | License | Offline |
|---|---|---|---|---|---|---|
| bsdiff (Percival 2003) | crate `bsdiff` 0.2.1 (2025-03-31, BSD-2); PyPI `bsdiff4` 1.4.1 | C/Rust/Py | suffix-array based delta + bzip2 | `bsdiff4.diff(a,b)` | BSD | C, P |
| qbsdiff | 1.4.4 (2025-08-24, MIT) | Rust | fast bsdiff | lib/CLI | MIT | C |
| xdelta3 / VCDIFF RFC 3284 | PyPI `pyxdelta` 0.2.3; crates `xdelta3` 0.1.5 (2019), `vcdiff` 0.1.0 (2016) | C | VCDIFF (RFC 3284) copy/add encoding, rolling hash | `xdelta3 -e -s old new delta` | Apache-2.0 (xdelta3, UNVERIFIED) | P/C (stale crates; prefer binary) |
| rsync / librsync / zsync | rsync 3.x | C | rolling checksum block matching, not minimal | `rsync --only-write-batch`; `librsync` `rdiff signature/delta` | GPL / LGPL | S |
| zstd `--patch-from` | zstd 1.5.x (`zstd-safe` 8.2.0 VERIFIED) | C | dictionary-based delta compression | `zstd --patch-from=old new` | BSD/GPL dual | C/S |
| git packfile deltas | git | C | `diff-delta.c` copy/insert deltas, rolling hash windows | `git pack-objects`/`git repack -adf --window=N` | GPL-2 | S |

Use as a size lens only: report patch bytes (as compressed delta) vs our script bytes. They are never "more
optimal" in the Myers sense; they minimize bytes with arbitrary copies including moves.

### 1f. Version-control and patch-theory systems (context, not algorithms to beat)

- Pijul/Darcs: objective is commutation-aware patch algebra; underlying text diff is a Myers-class LCS.
  Nothing to benchmark except libpijul's diff call, UNVERIFIED.
- Sapling/Mercurial: `bdiff` (see above); also Sapling's `sl diff` uses its own Rust xdiff binding (UNVERIFIED).
- Unison / structured editors (Hazel, Projectional editors, Unison codebase manager): content-addressed ASTs;
  there is no general text diff to compare against. Unison diffs compare names -> hashes. Treat as out of
  scope except as related work (UNVERIFIED, no primary source fetched).
- jj: see 1a; its diff is used for conflict materialization and `jj diff --color-words`.

## 2. Papers

| Paper | Venue / URL | What it measured or claims | Status |
|---|---|---|---|
| Myers, "An O(ND) difference algorithm and its variations" | Algorithmica 1(2), 1986. DOI 10.1007/BF01840446 | O(ND) greedy, linear-space refinement, expected O(N + D^2) | UNVERIFIED (from memory), canonical |
| Hunt & McIlroy, "An algorithm for differential file comparison" | Bell Labs CSTR 41, 1976 (no DOI) | candidates/k-threshold LCS, original Unix diff | UNVERIFIED |
| Hunt & Szymanski, "A fast algorithm for computing longest common subsequences" | CACM 20(5) 1977, DOI 10.1145/359581.359603 | O((r+n) log n) with r matching pairs | UNVERIFIED |
| Miller & Myers, "A file comparison program" | Software: Practice & Experience 15(11), 1985, DOI 10.1002/spe.4380151102 | O(ND)-style predecessor of Myers' paper | UNVERIFIED |
| Wu, Manber, Myers, Miller, "An O(NP) sequence comparison algorithm" | Information Processing Letters 35, 1990, DOI 10.1016/0020-0190(90)90035-V | O(NP), P = number of deletions; faster when sequences nearly same length | UNVERIFIED |
| Ukkonen, "Algorithms for approximate string matching" | Info & Control 64, 1985, DOI 10.1016/S0019-9958(85)80046-2 | diagonal-cutoff band, O(ND) for edit distance | UNVERIFIED |
| Landau & Vishkin, "Fast parallel and serial approximate string matching" | J. Algorithms 10(2), 1989, DOI 10.1016/0196-6774(89)90010-2 | O(nk) with suffix-tree LCE jumps | UNVERIFIED |
| Hirschberg, "A linear space algorithm for computing maximal common subsequences" | CACM 18(6) 1975, DOI 10.1145/360825.360861 | linear-space divide and conquer used in Myers and edlib | UNVERIFIED |
| Myers, "A fast bit-vector algorithm for approximate string matching based on dynamic programming" | JACM 46(3), 1999, DOI 10.1145/316542.316550 | O(ceil(m/w) n) Levenshtein with bit-vectors | UNVERIFIED (confirmed by search snippet to be what Hyyrö and edlib extend) |
| Hyyrö, "Explaining and extending the bit-parallel approximate string matching algorithm of Myers" | TR A-2001-10, Univ. Tampere, 2001; thesis https://trepo.tuni.fi/bitstream/10024/67325/1/951-44-5840-0.pdf (VERIFIED link from search) | clearer derivation, block extension, edit-distance variant used by the `editdistance` package | partially VERIFIED |
| Hyyrö & Navarro, "Faster bit-parallel approximate string matching" | CPM 2002. https://users.dcc.uchile.cl/~gnavarro/abstracts/cpm02.2.html (VERIFIED link) | improves Myers 1999 for large k | VERIFIED existence |
| Navarro, "A guided tour to approximate string matching" | ACM Computing Surveys 33(1), 2001, DOI 10.1145/375360.375365 | survey: DP, automata, bit-parallel, filtering | UNVERIFIED |
| Marco-Sola, Moure, Moreto, Espinosa, "Fast gap-affine pairwise alignment using the wavefront algorithm" | Bioinformatics 37(4), 2021, DOI 10.1093/bioinformatics/btaa777 | WFA, O(ns) time, vs KSW2/Parasail/edlib on genome reads | UNVERIFIED |
| Marco-Sola, Eizenga, Guarracino, Paten, Garrison, Moreto, "Optimal gap-affine alignment in O(s) space" (BiWFA) | Bioinformatics 39(2), 2023, btad074, DOI 10.1093/bioinformatics/btad074. https://pmc.ncbi.nlm.nih.gov/articles/PMC9940620 | bidirectional WFA gives O(s) memory, same O(ns) time, "comparable or better than WFA" | VERIFIED via search |
| Selkow, "The tree-to-tree editing problem" | Info. Proc. Letters 6(6), 1977, DOI 10.1016/0020-0190(77)90064-3 | top-down tree edit with subtree-level ins/del, O(nm); our objective (b) | UNVERIFIED |
| Zhang & Shasha, "Simple fast algorithms for the editing distance between trees and related problems" | SIAM J. Comput. 18(6), 1989, DOI 10.1137/0218082 | general ordered TED, O(n^2 depth^2) | UNVERIFIED |
| Bille, "A survey on tree edit distance and lowest common ancestor..." (correct title: "A survey on tree edit distance and related problems") | Theoretical Computer Science 337, 2005, DOI 10.1016/j.tcs.2004.12.030 | survey of TED variants incl. top-down, bottom-up, constrained | UNVERIFIED (title details from memory) |
| Pawlik & Augsten, "RTED: A robust algorithm for the tree edit distance" | PVLDB 5(4) 2011/2012. arXiv:1201.0230 https://arxiv.org/pdf/1201.0230.pdf (VERIFIED link) | strategy selection makes TED shape-independent; beats Zhang-Shasha, Klein, Demaine on worst shapes | VERIFIED existence |
| Pawlik & Augsten, "Tree edit distance: robust and memory-efficient" (APTED) | Information Systems 56, 2016, pp.157-173, DOI 10.1016/j.is.2015.08.004 (VERIFIED via search) | AP-TED: optimal all-path strategy, no RTED 2x memory overhead | VERIFIED |
| Chawathe, Rajaraman, Garcia-Molina, Widom, "Change detection in hierarchically structured information" | SIGMOD 1996 | the edit-script generation (insert/delete/update/move, align) that GumTree reuses | UNVERIFIED |
| Fluri, Wuersch, Pinzger, Gall, "Change distilling: tree differencing for fine-grained source code change extraction" | IEEE TSE 33(11), 2007, DOI 10.1109/TSE.2007.70731 | ChangeDistiller; evaluated vs line diff on Eclipse history, classifies change types | UNVERIFIED |
| Falleri, Morandat, Blanc, Martinez, Monperrus, "Fine-grained and accurate source code differencing" | ASE 2014, DOI 10.1145/2642937.2642982 | GumTree: top-down greedy + bottom-up; evaluated vs ChangeDistiller and RTED-style on Java/C | UNVERIFIED |
| Falleri & Martinez, "Fine-grained, accurate and scalable source differencing" | ICSE 2024 (DOI UNVERIFIED) | GumTree Simple: faster and more accurate than classic; benchmark of script sizes and runtimes | UNVERIFIED |
| Dotzler & Philippsen, "Move-optimized source code tree differencing" | ASE 2016, DOI 10.1145/2970276.2970347 | MTDiff: better move handling, benchmark vs GumTree and ChangeDistiller | UNVERIFIED (authorship differs from the task brief) |
| Tsantalis, Mansouri, Eshkevari, Mazinanian, Dig, "Accurate and efficient refactoring detection in commit history" | ICSE 2018, DOI 10.1145/3180155.3180206 | RefactoringMiner 2.0 precision and recall vs RefDiff etc. | UNVERIFIED |
| Tsantalis, Ketkar, Dig, "RefactoringMiner 2.0" | IEEE TSE 48(3), 2022, DOI 10.1109/TSE.2020.3007722 | extended evaluation | UNVERIFIED |
| Tsantalis, SANER 2025 keynote "Source code diff revolution" | https://speakerdeck.com/tsantalis/source-code-diff-revolution (VERIFIED, slides not a paper) | benchmark of 800 Defects4J bug-fix commits + 187 refactoring commits with a constructed "perfect" diff, precision/recall per diff tool | VERIFIED existence |
| Nugroho, Hata, Matsumoto, "How different are different diff algorithms in Git? Use --histogram for code changes" | Empirical Software Engineering 25(1):790-823, 2020, DOI 10.1007/s10664-019-09772-z; arXiv:1902.02467 https://arxiv.org/abs/1902.02467 | Myers vs Histogram on 14 Java projects: churn differs in 1.7% to 8.2% of commits; histogram better on patch-application quality | VERIFIED via search |
| "Analyzing and Evaluating the Behavior of Git Diff and Merge" | arXiv:2507.22071 (2025) https://arxiv.org/pdf/2507.22071 | runtime and optimality of myers/minimal/patience/histogram; Myers fastest avg, then histogram, minimal, patience slowest; 95th percentile per diff under 0.5 ms; Myers/patience slightly more often optimal than histogram. Directly relevant: gives baseline per-pair timing and a way to define "optimal" | VERIFIED via search (read the full text before citing numbers) |
| "Toward Interactive Optimization of Source Code Differences: An Empirical Study of Its Performance" | arXiv:2409.13590 (2024) https://arxiv.org/pdf/2409.13590 | user-in-the-loop diff optimization performance; details not read | VERIFIED existence only |
| LastMerge, Duarte, Borba, Cavalcanti, "LastMerge: a language-agnostic structured tool for code integration" | arXiv:2507.19687 (2025) https://arxiv.org/abs/2507.19687 | generic tree-sitter structured merge vs Spork and Mergiraf (Java); accuracy impact not significant | VERIFIED via search |
| "Semistructured merge with language-specific syntactic separators" | arXiv:2407.18888 (2024) | semistructured merge evaluation | VERIFIED existence only |
| TU Delft BSc/MSc theses (2025): "Evaluating stable tree differencing with GumTree and HyperDiff", "Scalable structural code diffs", "Analyzing iterative improvements to structural code diffs", GumTree Hybrid hyperparameters | https://repository.tudelft.nl/record/uuid:0643d32b-2bba-4c1f-b54b-ae71307d919d , .../uuid:ae09e916-f0bf-41a6-bfd9-69f1a062d9b9 , .../uuid:a9ac5f85-5e63-4541-9172-7fa5e6d72ccf | GumTree Simple uses far fewer CPU cycles than Greedy; stable variant adds slight overhead; lazy evaluation reduces runtime; recovery phase is O(n^3) | VERIFIED via search (theses, low peer-review weight) |
| Jimenez et al., "Dissecting diff algorithms" (as named in the brief) | could not locate | UNVERIFIED: I could not find a paper with this title. Possibly mixed up with Nugroho et al. or with Mining-software-repos "diff impacts" studies. Ask for a citation |  UNVERIFIED |
| Ukkonen/Wu line: "Myers diff" cited as optimal; Skeena, Neubauer... | n/a | no further papers found | - |
| 2024-2026 arXiv on exact line differs, bit-parallel diff, or tree top-down benchmarking | searched twice | none found; our result (a) appears unclaimed in the arXiv listing. Worth one more targeted search (e.g. "linear space edit script SIMD") before claiming novelty | UNVERIFIED negative |

## 3. Prioritized test list (what to add to the harness)

Priority 1 (cheap, installable here, directly comparable):
1. GNU `diff -d` (present), `git diff --minimal` (have), `diffy` 0.5.2, `dissimilar` 1.0.11,
   `diff-match-patch` crate 0.3.1 with timeout off, `fastdiff` PyPI, `difflib` (as a floor),
   `rapidfuzz.distance.Indel` as optimality oracle (P), `pygit2` (libgit2 xdiff copy), `myers` PyPI.
2. diffsitter 0.9.0 and difftastic 0.72.0 (cargo install), mergiraf 0.20.0 as 3-way tree matcher (external binary).
3. APTED (PyPI) and zss on small trees for cost cross-checks only.
Priority 2 (need a GitHub fetch, verify reachability first):
4. WFA2-lib `bialign` / `align_benchmark` for edit-distance speed ceiling; GumTree Simple/Hybrid matcher ids;
   JGit Histogram; xdelta3 binary.
Priority 3: jd / dyff (Go binaries), RefactoringMiner, ChangeDistiller, MTDiff. Mostly of related-work interest.
Out of scope: SemanticDiff (proprietary), Unison, Pijul/Darcs patch algebra.

## 4. New benchmark scenarios (not yet run) and how to build each corpus offline

General rules: store every pair as files `corpora/<scenario>/<id>.{a,b}`; record per-pair
(n, m, D_optimal, D_tool, wall time, peak RSS). Always validate script by applying it and checking equality
with b. Use a fixed seed in every generator. For optimality report D_tool / D_opt using the Indel oracle.

1. Huge generated files. Generator: synthetic lines from a Zipf distribution over a vocabulary, size 10^5,
   10^6, 10^7 lines, edits as k random insert/delete bursts with k in {10, 1e3, 1e5}. Also adversarial
   cases: totally different files (D = n+m, worst case for O(ND)), one huge repeated line ("aaaa...") and
   many identical lines (hash collisions, histogram bail-outs). Offline: pure Rust/Python generator, no inputs.
   Measures the scaling exponent and memory; checks linear-space fallback and any cost cutoffs.
2. Minified JS single-line. Corpus: pairs of `*.min.js` from successive wheels of the same PyPI project
   (for example plotly, bokeh, jupyterlab wheels ship minified bundles; version choice UNVERIFIED, pick by
   downloading wheel JSON from PyPI). Two modes: whole file as one line (n=1: line diff degenerates, tests char/token mode),
   and tokenized (split on `;`,`,`,`{`,`}` to emulate token streams). Also covers tree differs failing to parse.
3. Lockfiles. Corpus: Cargo.lock from consecutive crates.io source tarballs of bin crates
   (`https://crates.io/api/v1/crates/<name>/<ver>/download`, tar.gz; Cargo.lock included for binaries; fetch
   difftastic, mergiraf, diffsitter, git-delta across versions). Also `poetry.lock`/`uv.lock` from PyPI
   sdists where present (UNVERIFIED which packages ship them). Properties: highly repetitive TOML blocks,
   `checksum` lines unique, reorders of dependency lists: stress for patience/histogram anchoring.
4. CSV. Corpus: CSVs bundled in pip wheels (scikit-learn `datasets/data/*.csv`, pandas test data, seaborn is
   not bundled; use `pip download scikit-learn` and unzip), and synthetic: 1e5 rows, apply row insert, row delete,
   column insert (changes every line), sorted-vs-unsorted variants. Report line-level vs cell-level (tokenize on `,`)
   distances. Column insert is the classic worst case for line diffs.
5. JSON. Corpus: pretty-printed versus compact JSON from the same data (jsonschema test suites in PyPI
   `jsonschema` sdist; GeoJSON-like synthetic), plus key-order permutation of objects. Compare: line diff on
   pretty form, tree diff (Selkow) on JSON trees, `json-patch` crate `diff`, `jsondiff`, `DeepDiff`.
   Cost normalisation required (leaf changes). Also huge arrays (1e6 numbers) with one element changed.
6. Vendored directories (tree of files). Corpus: unpacked old/new releases of the same crate or wheel
   (`cargo vendor` offline from a Cargo.lock; `~/.cargo/registry/src/*/` already holds many version pairs of
   the same crate when several are resolved). Compare directory-level throughput: files/second with a
   shared thread pool, rename pairing (hash match) cost, binary file skip, `git diff --no-index` as baseline.
7. Rename-heavy refactors. Build: take a real source tree and rename an identifier across all files with
   `sed -E 's/\bOldName\b/NewName/g'` (changes many lines by a few characters), and a mechanical reformat
   (`rustfmt` on Rust crates, `black` from PyPI on Python) as a rename-like whole-file churn proxy.
   Measures: line differ D vs token differ D (intra-line), and tree differ edit counts (should be small for
   renames in a tree differ with rename op and large for Selkow without rename op: report both, honestly).
8. Reorder-heavy changes. Build: shuffle top-level items (functions/impls/classes) of a real file, or sort
   imports and `use` blocks, or alphabetize match arms. Line differs (Myers) see a big D; patience/histogram
   anchor differently; tree differs with move support (GumTree, MTDiff) can win. Selkow cannot express moves; quantify the loss
   explicitly rather than hiding it.
9. Moved blocks. Build: cut a contiguous block of 20 to 500 lines and paste it elsewhere in the same file
   (programmatic, seeded). Variation: move + small edit inside the block. Report D for line/tree tools; for
   GumTree variants report whether a move action was emitted. Packfile delta (xdelta3, bsdiff) as the
   "copy" lower-bound lens.
10. Whitespace-only and EOL changes. Build: re-indent (tabs <-> spaces), trailing-space strip, CRLF <-> LF
    conversion on 1000 real files (`unix2dos`-style via python). Cases: line differ with whitespace ignore flags
    (`-w`, `-b`, `--ignore-space-at-eol`) versus normalize-then-diff; check that D=0 under normalization and
    time stays linear. Many tools fail here: difftastic reports changes inside strings, dmp cleans up.
11. 3-way merge (diff3 / conflict resolution). Build: for each crate with >=3 versions v1 < v2 < v3 from the
    cargo registry or crates.io tarballs, use base=v1, ours=v2, theirs=v3 per file; compare `git merge-file`
    (diff3 style), `mergiraf merge` (tree), and an ours-vs-theirs equal-conflict count. Ground truth: use
    real merges from PyPI sdists that include history?? NO - UNVERIFIED availability. Fallback ground truth:
    synthetic merges where non-overlapping edits are applied to base and the expected merged file is known
    (apply edit set E1 then E2 in either order; both orders must equal expected). Metric: number of conflict
    hunks, unresolved conflicts, merge time.
12. LLM-edit streams. Build: emulate agent edits offline. (i) take a real file (n lines) and produce a growing
    stream: append 1 to 5 lines at a time then run a diff against the previous version (n diffs of a growing
    document, total cost O(n * diff)); (ii) apply "search/replace" style block edits chosen by a seeded script
    (replace 3 to 40 line windows, re-indent, rename a variable); (iii) whole-file rewrite where 80% of lines
    are unchanged but shifted. Metrics: per-diff latency percentiles (p50/p99, since the use case is interactive),
    warm vs cold start, incremental reuse (cache of line hashes between runs), memory. Recorded real transcripts
    are not available offline, so label the corpus synthetic.

Cross-scenario metrics to report for every run: script length ratio to oracle optimum, time (median, p95),
peak RSS, correctness (apply-and-compare), and failures/timeouts/fallbacks (difftastic graph-limit fallback to
line diff, dmp timeout, histogram bail-out). Include both cold-process and in-process timings, since our 1.8x
claim is in-process while CLI baselines pay process-spawn cost.

## 5. Open items / caveats

- GitHub API unreachable here: confirm every Go/Java/C tool version and license from its README before citing.
- Confirm that difffold results hold against difftastic 0.72.0, not only 0.64.
- Resolve the "Jimenez Dissecting diff algorithms" and "Matsumoto MTDiff" citations with the requester; I could
  not find either as described (MTDiff is Dotzler & Philippsen ASE 2016, UNVERIFIED).
- Weave and zdiff could not be identified unambiguously; do not include in published tables until clarified.
- GPL licenses (mergiraf GPL-3.0-only, GNU diff, wdiff, hg, python-Levenshtein, pijul): invoke as external
  processes, do not link or copy code into difffold.
