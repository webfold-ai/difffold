# difffold adversarial test plan: grounded in history
Status legend: VERIFIED = I read a primary source (or a fetch of it) this session.
SECONDARY = only seen via search-result summaries or aggregators.
UNVERIFIED = recalled from background knowledge or not found; do not cite as fact.

Research limits: several primary hosts (lore.kernel.org, gnu.org manual, nvd.nist.gov,
difftastic manual pages) returned 403/404/503 or empty bodies to the fetch tool.
WebFetch output is a model summary, not raw text, so quotes should be rechecked
against the URL before being copied into docs. No GumTree/RTED/JGit/libgit2-xdiff/
similar/imara-diff/dissimilar issue-tracker bugs were found; those are UNVERIFIED gaps.

Test notation: `T:` = one-line test we could write. "oracle" = brute-force O(NM) LCS DP
on small inputs, or a reference differ, compared on edit-script length.
---------------------------------------------------------------------------
## 0. Design facts from git xdiff that directly shape difffold (VERIFIED)

Source: https://raw.githubusercontent.com/git/git/master/xdiff/xdiffi.c
        https://raw.githubusercontent.com/git/git/master/xdiff/xprepare.c

- xdl_do_diff sets `mxcost = bogosqrt(ndiags)`, clamped to `XDL_MAX_COST_MIN` (256).
  In xdl_split, `if (ec >= mxcost)` ends the search early and returns a non-minimal
  split. So git "Myers" is NOT minimal by default.
- Heuristic skipped only when `need_min` (XDF_NEED_MINIMAL / `--minimal`). Constants:
  XDL_HEUR_MIN_COST 256, XDL_SNAKE_CNT 20, XDL_K_HEUR 4.
- xdl_cleanup_records drops lines with zero matches on the other side (marked
  changed immediately). That is exactly difffold's "drop lines on only one side".
  Under XDF_NEED_MINIMAL the multimatch limit becomes PTRDIFF_MAX so the lossy
  "INVESTIGATE" discard (XDL_MAX_EQLIMIT 1024, XDL_SIMSCAN_WINDOW 100, XDL_KPDIS_RUN 4)
  is off, but the zero-match discard stays. Zero-match discard is exact for edit
  distance (such lines can never be in an LCS), so it is safe; the multimatch discard
  is not.
- Hash table: classifier sized from `xdl_guess_lines` (sample of 256 lines, or 20
  for histogram) so `hbits` is derived from an estimate, not the true line count.
  I could not see xdl_hashbits body. Underestimated tables mean long chains.
  T: file with 1e6 distinct short lines where first 256 lines are all identical; assert
     intern time is O(n) (e.g. under 5x the time of the same file shuffled).

Implication for difffold tests:
  T: for random small inputs, edit-script length == oracle length (exactness), and also
     with the one-sided-line drop disabled, to prove the drop never changes length.
  T: same inputs with D ~ N (see 1.1) must still equal oracle length; git's default
     would fail this, so use `git diff --minimal` as a comparison tool, not default.
---------------------------------------------------------------------------
## 1. Algorithmic worst cases

### 1.1 Myers O(ND) with D ~ N  [background + VERIFIED git mitigation]
- What: Myers is O((N+M)D) time. Two files with no common lines have D=N+M. Linear-space
  variant (middle snake) is O(ND) time, O(N) space; naive stores O(D^2) trace.
- Why it matters: git adds the mxcost cutoff above precisely because of this.
  Source: xdiffi.c URL above (VERIFIED).
- Trigger shape: completely disjoint files (but difffold drops one-sided lines, so
  that case becomes trivial); hard case is many shared lines in near-reversed or
  interleaved order, e.g. a = 1..n, b = n..1 (all lines shared, LCS length 1, D ~ 2n).
  Also a = (x y)^n vs b = (y x)^n with only two distinct lines: interning gives high
  frequency, nothing dropped, D ~ 2.
- T: a=[1..20000], b=reverse(a); assert the result is exact (LCS len 1) and finishes
  inside a stated budget; record time as an explicit known O(N^2) case, not a hang test.
- T: assert D-dependent work counter (if we expose one) is <= c*(N+M)*D.

### 1.2 Quadratic/degenerate patience diff with no unique lines  [background]
- What: patience diff anchors on lines unique in both files; with none, it must fall
  back. git's patience falls back to xdl_do_classic_diff for subranges without unique
  common lines. imara-diff and JGit similarly fall back.
- Trigger: files where every line repeats (e.g. all blank, all "}").
- Source: https://git-scm.com/docs/git-diff documents the algorithms (VERIFIED, but it
  does not describe the fallback; the fallback is UNVERIFIED from a primary source here).
- T: a = ["}"]*10000, b = ["}"]*10001; expect single insertion, linear-ish time.

### 1.3 Histogram high-frequency lines  [SECONDARY]
- What: histogram diff caps chain length (git MAX_CHAIN_LENGTH 64; imara-diff
  MAX_CHAIN_LEN 63 per a TS port) and falls back to Myers if no low-occurrence
  match. Docs for imara-diff 0.1.1 say histogram heuristic works poorly with small,
  often-repeated tokens and may output longer scripts than Myers.
  https://gist.github.com/jjrv/ac616cea4c039b8c94b4fdc354e063bc
  https://docs.rs/imara-diff/0.1.1/src/imara_diff/lib.rs.html
  https://download.eclipse.org/jgit/site/6.1.0.202203080745-r/apidocs/org/eclipse/jgit/diff/HistogramDiff.html
- Trigger: every line occurs >64 times on both sides, alternating pattern.
- T: lines drawn from alphabet of 3 symbols, n=5000 each side; exactness vs oracle
  on n<=200, and wall-time scaling check at 5000 (time(2n)/time(n) < 6).
- difffold relevance: we do NOT want chain-cap heuristics; only an exact path.

### 1.4 Histogram + hash collisions bug report  [SECONDARY; thread not readable]
- A 2021 git list thread titled "Bad behavior in xhistogram.c in the face of hash
  collisions?" reports histogram logic that compares only hashes and so can treat
  colliding distinct lines as equal; reporter says JGit port has the same pattern.
  Seen only in a search summary (the thread itself returned 403 to the fetcher).
  https://lore.kernel.org/git/4e0eff48-4a3e-4f0e-9ed2-d01ec38442a5@www.fastmail.com/T/
- Why it matters: if difffold interns lines by hash and compares ids, a collision
  would silently produce a WRONG (not slow) diff.
- T: inject a hasher that maps all lines to the same hash (feature flag or generic
  over Hasher); assert output is identical to the real hasher's output.
- T: two different lines with a known 64-bit FNV or crc collision; assert not equal.

### 1.5 Hash flooding of the line table  [UNVERIFIED as a documented git/diff CVE]
- I found no CVE or git-list thread establishing a hash-flooding attack on
  xdiff's line table. I searched; the only xhistogram thread is 1.4. Treat the
  quadratic-chain attack as a plausible threat model, not history.
- Trigger shape: many distinct lines crafted to share a bucket in a non-keyed
  hash (xdl_hash_record is a fixed function, so precomputation is possible).
- T: use std HashMap with a fixed-key hasher and N colliding keys of 1e5 lines (generate
  via birthday search in test setup); assert interning stays under budget, or that the
  table is keyed with random state (assert two runs use different seeds).

### 1.6 Huge single lines / no newlines  [background]
- What: one 100MB line makes line interning, prefix/suffix cut and byte compare
  matter. Byte-level prefix/suffix cut turns identical huge lines to O(N) memcmp.
  Two huge lines that differ by 1 byte in the middle are still one "changed" line.
- T: two 64 MiB single-line buffers differing at the midpoint; assert 1 delete + 1
  insert, peak RSS bounded (< 4x input).
- T: 1e6 lines of 1 byte each vs 1 line of 1e6 bytes (no newline); assert correct.

### 1.7 Lines with identical hash but different lengths, NUL, CR  [background]
- T: lines "a\0b" vs "a\0c" vs "a" must be distinct ids (no C-string truncation).
  Historic xdiff is length-based, but any strcmp/strlen use would break this.
- T: "a\r\n" vs "a\n" distinct unless an explicit option normalizes them.
---------------------------------------------------------------------------
## 2. GNU patch and diffutils: CVEs and bugs

All CVE IDs in this section dated 2026 were read via CERT.PL and INCIBE pages
(VERIFIED text) but NVD itself returned an empty page, so scores/dates are SECONDARY.

### 2.1 CVE-2026-56289: GNU patch infinite loop on huge hunk line number
- What: unified diff specifying an extremely large hunk line number makes patch loop
  searching for the position, burning CPU indefinitely. patch <= 2.8.0.
  Fixed upstream in GNU patch after 2.8.0.
- Source: https://cert.pl/en/posts/2026/07/CVE-2026-56288 (VERIFIED)
- Trigger: `@@ -9223372036854775807,1 +1,1 @@`.
- T (difffold's patch applier, if any): apply hunk with start = i64::MAX / u64::MAX;
  expect a fast error, not a loop or overflow panic.
- T: parser for `@@ -a,b +c,d @@` rejects/handles values > usize without wrap.

### 2.2 CVE-2026-56288: GNU patch NULL deref, consecutive EOF newline markers
- What: crafted unified diff with consecutive "end-of-file newline" markers corrupts
  hunk structures; NULL passed to fwrite(); crash. patch <= 2.8.0.
  Fixed upstream in GNU patch after 2.8.0.
- Source: https://cert.pl/en/posts/2026/07/CVE-2026-56288 (VERIFIED)
- Trigger: two `\ No newline at end of file` lines in a row, or one at the start of
  a hunk with no preceding line.
- T: parse hunk body "\\ No newline at end of file\n\\ No newline at end of file\n";
  expect a parse error, no panic.

### 2.3 CVE-2026-53910: GNU diffutils diff3 heap overflow via integer overflow
- What: signed integer overflow in line-mapping calc in diff3 leads to under-allocation
  and OOB write; requires attacker controlling output of the diff program
  (`--diff-program`). Maintainers dispute security relevance. Low CVSS 4.0 (2.1).
  Fixed upstream in GNU diffutils after 3.12.
- Source: https://www.incibe.es/en/incibe-cert/early-warning/vulnerabilities/cve-2026-53910 (VERIFIED)
- Lesson: line numbers/counts read from an external script are not trusted.
- T: for any parser of hunks/edit scripts we accept, feed counts near usize::MAX and
  assert checked arithmetic (error, not wrap).

### 2.4 CVE-2014-9637: GNU patch <= 2.7.2 memory consumption and segfault
- What: crafted diff file. NVD CWE-399. Fixed in GNU patch 2.7.3.
- Sources: https://cve.circl.lu/cve/CVE-2014-9637 (VERIFIED, aggregator of NVD)
  Savannah bug 44051 listed there (not opened).
- Exact trigger shape: UNVERIFIED (I did not read the Savannah bug).
- T: hunk header claiming 1e12 lines with a 3-line body; assert no preallocation
  proportional to claimed count (use Vec::with_capacity(min(claim, body_len))).

### 2.5 Other GNU patch CVEs (SECONDARY, one search summary of third-party trackers)
- CVE-2018-1000156 (ed-style diff, EDITOR_PROGRAM/ed code execution),
  CVE-2019-13638 (shell command injection via ed-style diff, metacharacters),
  CVE-2018-6951 (NULL deref, mangled rename patch), CVE-2018-6952 (double free),
  CVE-2016-10713 (out-of-bounds in patch before 2.7.6).
- Source: https://security-tracker.debian.org/tracker/CVE-2019-13638
  (search hit; not opened). Other IDs from search summary only.
- Relevance: difffold emits/consumes only unified/internal script presumably; the
  lesson is filenames and ed-style input are injection surfaces.
- T: filenames in headers containing `;`, `$(...)`, newline, tab, quotes, and
  non-UTF-8 bytes round-trip through our header writer/parser unchanged.

### 2.6 GNU diff heuristics (UNVERIFIED this session)
- diff(1) has `--minimal`, `--speed-large-files`, `--horizon-lines`, and by default
  uses heuristics that are not minimal. The manual pages returned 503 so I did not
  verify wording. Git uses the same libxdiff-derived design (section 0, VERIFIED).
  https://www.gnu.org/software/diffutils/manual/html_node/diff-Options.html (not read)
- T: compare our script length to `diff --minimal` output length on corpora; ours
  must be <= always, and equal to the oracle.
---------------------------------------------------------------------------
## 3. git / libgit2 / JGit

### 3.1 git default Myers is non-minimal; `minimal` exists  [VERIFIED]
- https://git-scm.com/docs/git-diff : myers is default "basic greedy diff algorithm";
  minimal "spend extra time to make sure the smallest possible diff is produced".
- T: construct input where default xdiff gives longer script than minimal (large D,
  mxcost cutoff at >=256 diagonals); use as a regression fixture that difffold
  equals `git diff --minimal` length, with the corpus checked in as bytes.
  Generating such a fixture is TODO; I did not construct one.

### 3.2 git indent heuristic / slider ambiguity  [VERIFIED docs, SECONDARY effect]
- `--indent-heuristic` shifts hunk boundaries and is on by default
  (https://git-scm.com/docs/git-diff). This is a post-pass on an equal-length script,
  so exact minimal diffs have many equally valid answers.
- T: for a = "A\nB\nB\n", b = "A\nB\nB\nB\n" the inserted line can be at 3 positions;
  assert the chosen one is deterministic and documented, and that applying it works.

### 3.3 libgit2 xdiff  [UNVERIFIED]
- libgit2 vendors xdiff (xhistogram.c exists in libgit2 1.3.0 tree per search hit
  https://grok.dragonflybsd.org/xref/dports/devel/libgit2/libgit2-1.3.0/src/xdiff/xhistogram.c).
  I found no xdiff-specific CVE. CVE-2024-24575 is an infinite loop in
  git_revparse_single, NOT xdiff (SECONDARY:
  https://api.osv.dev/v1/vulns/CVE-2024-24575). Do not cite as a diff bug.

### 3.4 JGit  [partly VERIFIED docs]
- HistogramDiff javadoc: chain length is capped to keep linear; falls back to another
  algorithm (default MyersDiff) when exceeded.
  https://download.eclipse.org/jgit/site/6.1.0.202203080745-r/apidocs/org/eclipse/jgit/diff/HistogramDiff.html
- JGit-specific bugs/CVEs: UNVERIFIED (not searched deeply).
---------------------------------------------------------------------------
## 4. Library-level issues

### 4.1 Python difflib autojunk  [VERIFIED docs]
- What: SequenceMatcher is quadratic worst case; autojunk (default on) treats any
  element of sequence b that is over 1% of a >=200 item list as junk. Heuristic is
  asymmetric and changes results (not exact).
- Source: https://docs.python.org/3/library/difflib.html
- Trigger: b with >=200 lines where one line ("", "}") is >1% of b.
- T (as a negative control for our exactness claim): difflib with autojunk on yields
  a longer script than the oracle on a 300-line input with a repeated line; ours must
  match the oracle. This also validates the oracle harness.
- Note: difflib is Ratcliff/Obershelp-like (longest contiguous match), not Myers;
  it does not produce minimal scripts even with autojunk=False. (Background; the
  quoted doc says "cubic ... Ratcliff-Obershelp", VERIFIED only for complexity.)

### 4.2 difflib lineterm / missing newline  [VERIFIED docs]
- unified_diff emits header lines with "\n" by default; for inputs lacking trailing
  newlines you must pass lineterm="". It does NOT emit `\ No newline at end of file`.
- T: diff "a" vs "a\n" via our API; output must carry the no-newline marker and a
  patch applier must reproduce the exact bytes (see 7.2).

### 4.3 Google diff-match-patch: surrogate pairs  [SECONDARY]
- What: diffs work on UTF-16 code units so a common prefix can include the high
  surrogate of a pair; diff_toDelta/patch_toText then use encodeURI and throw
  "URI malformed" on a lone surrogate. Issue #149: patch_make("🧮 **a","🧮 **")
  fails in patch_toText because Patch_Margin context splits a pair.
  PR #80 / dmsnell fork adds diff_cleanupSplitSurrogates.
- Sources: https://github.com/google/diff-match-patch/pull/80
  https://git.huazai-net.workers.dev/google/diff-match-patch/issues/149 (mirror)
  https://github.com/dmsnell/diff-match-patch/pull/1
  Upstream merge status UNVERIFIED.
- difffold relevance: only if we diff characters/UTF-16 or if a char-level pass runs
  inside a changed line. Byte-level cuts can split a UTF-8 sequence similarly.
- T: byte prefix cut on "é" (C3 A9) vs "è" (C3 A8) must not produce a split that
  corrupts when a char-level view/JSON output is rendered; assert output is valid
  UTF-8 or explicitly bytes.
- T: emoji pair differing in low surrogate/last byte: render each hunk and check
  `String::from_utf8` ok for text mode.

### 4.4 Rust crates: similar / imara-diff / dissimilar  [mostly UNVERIFIED]
- imara-diff README: Myers with heuristics for pathological cases, histogram ported
  from git, fuzz tests cover postprocessing and MyersMinimal.
  https://raw.githubusercontent.com/pascalkuthe/imara-diff/master/README.md (VERIFIED)
- No specific bug reports for imara-diff, similar, or dissimilar found; the search
  returned only rustc issues. UNVERIFIED that any exist. Suggest a manual read of
  https://github.com/mitsuhiko/similar/issues and https://github.com/dtolnay/dissimilar/issues
  before relying on this section.
- Recall (UNVERIFIED): similar offers a `deadline` and `Algorithm::Patience` etc;
  dissimilar is a char-based Myers with semantic cleanup that is not minimal.
- T (generic, from fuzz tests in imara-diff README): property test over random byte
  inputs that applying the script to a yields b, and script length == oracle.

### 4.5 difftastic  [partly VERIFIED titles]
- Release 0.30.0 replaced `--node-limit` with `--graph-limit` (DFT_GRAPH_LIMIT):
  old estimate-based limit led to very slow diffs when the estimate was wrong; now
  always tries structural diff first and gives up after traversing N graph nodes.
  https://newreleases.io/project/github/Wilfred/difftastic/release/0.30.0 (SECONDARY)
- Issue titles seen (descriptions inferred from titles only, bodies not read):
  #429 out of memory with rust-analyzer; #698 "Fix memory leak in neighbours array";
  #685 exceeded DFT_GRAPH_LIMIT; #477 lower limit to 1,000,000; #629 slow diffs for
  small changes in JSON; #814 --time-limit request; #1007 Dijkstra to A*.
  https://github.com/Wilfred/difftastic/issues (listing page, VERIFIED titles only)
- Byte limit (DFT_BYTE_LIMIT) and parse-error limit exist; parse-error fallback to
  line diff is on the tricky-cases page (VERIFIED, default value not stated):
  https://difftastic.wilfred.me.uk/tricky_cases.html
- Lesson for tree differ: shortest-path over a product graph explodes with
  repeated/identical siblings and large JSON arrays.
- T: JSON array of 5000 identical small objects vs same with one removed in the
  middle; assert exact threshold-DP result and a node/work budget.
- T: tree differ exposes a work counter; assert it stays under a stated bound for
  wide (1e5 leaf children) trees.
---------------------------------------------------------------------------
## 5. Tree differ worst cases

### 5.1 Exact tree edit distance cost  [VERIFIED]
- Demaine, Mozes, Rossman, Weimann: O(n^3) time, O(nm) space worst case, optimal
  among decomposition-strategy algorithms; lower bound
  Theta(n m^2 (1 + log(n/m))) for m<n.
  https://erikdemaine.org/papers/TreeEdit_ICALP2007/paper.pdf
  https://arxiv.org/abs/cs/0604037
- An unordered or general exact differ cannot beat this; a "top-down" differ
  (root-aligned, children sequences) is a different, cheaper problem. State clearly
  which problem difffold solves; tests should not conflate them.
- T: top-down differ on two trees equal up to a rotated root child is NOT the edit
  distance; assert documented semantics with a fixture.

### 5.2 GumTree / RTED memory blowups  [UNVERIFIED]
- Search found no GumTree issue about OOM or stack overflow. RTED (Pawlik & Augsten)
  details not found. I have no primary source; do not claim history here.
- Background reasoning only: any DP table of size |T1|*|T2| for 1e5 nodes each
  is 1e10 cells. T: tree differ on two 20k-node trees with a memory cap (ulimit -v
  or counting allocator); assert it either completes within cap or returns a typed
  "limit exceeded" error, never aborts.

### 5.3 Stack overflow on deep trees  [background; not tied to a diff tool source]
- Recursive descent over a path-shaped tree of depth 1e5-1e6 overflows the default
  8 MiB main / 2 MiB thread stack. Search results on rustc stack overflow are about
  the compiler (e.g. https://github.com/rust-lang/rust/issues/123686) and are
  not evidence about diff tools.
- Trigger: linked-list tree (each node one child), depth 1e6; also deeply nested
  JSON `[[[[...]]]]`; also drop of such a tree (recursive Drop overflows too).
- T: build chain depth 1_000_000; run diff in a thread with 256 KiB stack; assert no
  overflow (iterative) or a clean "depth limit" error.
- T: drop a 1e6-deep tree in a small-stack thread.

### 5.4 Shapes to include (all UNVERIFIED as history; derived from the DP)
- Wide: 1 root with 1e5 leaf children (reduces to line-diff of children).
- Deep: chain 1e6.
- Caterpillar: spine with a leaf at each level.
- Complete binary tree depth 17 vs same with one subtree swapped.
- Repeated identical subtrees: 1e4 copies of the same 10-node subtree (hash-consing
  of subtrees blows up if hashing is structural-without-memo, or collides).
- Mismatched labels everywhere (no shared labels): threshold DP worst case.
- T: each shape, n varies 4 sizes; fit log-log slope and assert <= declared exponent.
- T: for the threshold DP, run with threshold = 0, = exact distance, = distance-1;
  assert results found / not found accordingly and monotone cost.
---------------------------------------------------------------------------
## 6. Input-encoding edge cases for the line differ

(None of these are tied to a specific CVE here; they are the standard failure axes
and each pairs with a VERIFIED or SECONDARY item above where noted.)

- Binary files / NUL bytes: git treats files with NUL in the first 8000 bytes as
  binary (background; UNVERIFIED this session). T: input with NUL in middle line
  diffs as ordinary bytes, no truncation (see 1.7).
- Invalid UTF-8 (lone 0x80, overlong C0 80, truncated E2 82, CESU surrogates ED A0 80):
  T: round-trip a/b through diff -> apply; bytes identical. Output text mode must not
  use `String::from_utf8_lossy` in the apply path.
- CRLF/LF mixes: T: a="x\r\ny\r\n", b="x\ny\n" gives 2 changed lines (no silent
  normalization); with an explicit `strip_cr` option gives 0. Lone "\r" is not a line
  separator unless declared.
- Missing final newline: T: ("a\nb", "a\nb\n") must be 1 delete+1 insert of "b" vs
  "b\n", and the marker is emitted; ("a", "a") is empty; ("", "\n") is one insertion.
- Very long run of one repeated byte: prefix/suffix cut overlap must not double count.
  T: a="aaaa", b="aaa" prefix and suffix cuts together must not exceed min(len).
  This is the classic prefix/suffix overlap bug (background, UNVERIFIED as history).
- Prefix/suffix cut at byte level vs line level: cutting bytes may land mid-line;
  T: a="x1\n", b="x2\n": byte-common prefix "x" must be rolled back to a line start
  before interning (or cut only whole lines). Assert output lines are whole lines.
---------------------------------------------------------------------------
## 7. Correctness pitfalls in patch output / application

### 7.1 Ambiguous hunks (sliding)  [VERIFIED docs for git indent heuristic; see 3.2]
- Repeated lines let an insertion/deletion slide up/down with identical result text.
  Any canonical choice is fine, but patch must apply at the intended spot.
- T: for every generated pair, shift a hunk to all legal positions; apply each;
  all results == b.
- T: apply a patch whose context matches at 2 places; applier picks nearest to the
  stated line (GNU patch uses offset/fuzz; behavior UNVERIFIED here), or errors.

### 7.2 `\ No newline at end of file`  [VERIFIED as the CVE 2.2 trigger area]
- Marker applies to the line before it; belongs to old or new side depending on
  whether that line is `-`, `+`, or context. A context line with the marker applies to
  BOTH sides only if both lack newline.
- T: four combos (old/new has/lacks final newline) x (last line changed/unchanged);
  apply and compare bytes (16 cases, table-driven).
- T: marker after a `-` line only, then `+` line with newline.
- T: parser rejects two consecutive markers (CVE-2026-56288 shape).

### 7.3 Whitespace handling
- Options like ignore-space-change make "equal" lines unequal bytes; the script then
  does not reproduce b from a. T: if difffold has such an option, the applier uses
  the new side's text, and apply(a, diff) == b byte-exact.
- Trailing whitespace on context lines in patches is often stripped by editors/mail;
  GNU patch may need fuzz (background, UNVERIFIED here).
  T: strip trailing spaces from empty context lines (" " -> "") and ensure our parser
  treats a bare empty line in a hunk body as an empty context line, or errors, not
  silently desyncs counts.

### 7.4 Hunk header arithmetic
- `@@ -0,0 +1,N @@` for empty old file; `-1 +1` when count omitted means 1; count 0
  uses the line BEFORE (start = previous line). Off-by-one is the classic bug.
  (Background; UNVERIFIED as cited history.)
- T: table-driven: empty->nonempty, nonempty->empty, single-line, delete first/last
  line, insert at BOF/EOF; apply and compare.
- T: header counts disagree with body (claimed 3, body 2; claimed 2, body 3) -> error.

### 7.5 Round-trip property (the master test)
- T: proptest over (a,b) from small alphabets, random newline placement, random
  CR/NUL/high bytes: apply(a, diff(a,b)) == b; len(script)==oracle; diff(a,a)==empty;
  diff(a,b) and diff(b,a) have equal length; reversing the script transforms b to a.
---------------------------------------------------------------------------
## 8. Suggested priority order

1. Exactness vs oracle on small inputs, with/without one-sided-line drop (sec 0).
2. Hash-collision injection (1.4) since a collision yields a wrong diff, not a slow one.
3. Round-trip with all byte classes and EOF-newline combos (6, 7.2, 7.5).
4. Size-claim/overflow parsing (2.1, 2.3, 2.4) if difffold parses patches.
5. D~N and high-frequency timing curves (1.1, 1.3) with documented budgets.
6. Tree: deep chain on a small stack, wide fan-out, repeated subtrees (5.3, 5.4).
