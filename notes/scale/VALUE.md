# difffold: where diff cost and quality matter at scale

Date: 2026-11-04. Scope: desk research, ~20 fetches/searches. Evidence labels:
VERIFIED = a fetched primary source (vendor docs, engineering blog, changelog) states it.
SECONDARY = only a summary, aggregator or mailing list was seen.
UNVERIFIED = recalled or inferred, not checked this session. Treat as a to-do.
Inputs taken from the brief, not re-measured: line differ 1.8x faster in-process than similar/imara-diff
with identical minimal output; tree differ 4.2x median faster than difftastic; hash-consing basis.

## 0. Headline reading of the evidence

1. Almost every large-scale system studied does NOT pay for the diff algorithm itself. They pay for
   (a) deciding what to diff (path/blob selection, I/O), (b) rendering and transfer, (c) model tokens,
   (d) humans reading noise. Raw Myers-class speed is rarely the first bottleneck.
2. The places where algorithm cost is explicitly visible and capped by vendors are: GitHub/GitLab diff
   size limits, difftastic's graph and byte limits (fallback to line diff), diffoscope memory and
   time blowups, and LLM output tokens for edits. Those are where an exact + fast + structural differ can
   move a number.
3. Content-addressed "skip identical subtree by hash" is NOT novel: Git trees, Dolt prolly trees,
   Iceberg manifests, Bazel hashing, Blackbird sharding all use it. Our defensible novelty is applying
   it to intra-file syntax trees with an exact minimal output, not the idea of hashing.

---

## 1. GitHub

Cost drivers (VERIFIED unless noted):
- Published limits (docs "Repository limits"): PR diff 20,000 lines or 1 MB raw; single file diff
  20,000 lines or 500 KB, with only 400 lines / 20 KB auto-loaded; max 300 files per diff; 25
  renderable files. The docs page on comparing branches only says diffs "may not display if a PR exceeds
  repository diff limits"; the exact "Large diffs are not rendered by default" UI text was NOT seen in a
  fetched source (UNVERIFIED wording).
- 2016 engineering post "How we made diff pages three times faster": the diff is computationally
  expensive, so limits were conservative. Fix was lazy per-file patch loading using
  `git diff-tree --raw`, `--numstat --shortstat`, and `git diff-pairs` (upstreamed to Git), with old and
  new paths run side by side in prod. No per-diff algorithm time given in what I read. Cost driver was
  therefore fan-out and I/O, not the diff core.
- merge-ort (Git 2.33 highlights, Elijah Newren): >500x on a large rename-heavy merge, >9000x on a
  rebase of similar merges versus merge-recursive. Author says those cases were chosen as worst cases
  for merge-recursive; typical case only "a bit faster". Gain came from caching and avoiding
  redundant rename detection, i.e. reuse of prior computation, not a faster line diff.
- Code search (Blackbird): 115 TB of content reduced to 28 TB unique, 15.5 billion documents, sharding
  by Git content hashes (SECONDARY: TechRadar/Register, Feb 2023; the primary post was found but its
  dedup section not read). Content addressing is the scale lever there.
- Blame: no GitHub primary number found. Mailing-list material (SECONDARY) says changed-path Bloom
  filters speed `git log -- path` and `-L` (2-4x typical for line-log), but are explicitly NOT helpful for
  `blame -C -C` copy/move detection. That is a gap structural diff could address in principle.

What difffold could change:
- Raise or remove the "diff too large" cliff for single files by making per-file diff cost small and
  bounded; today's limits are product choices around cost and DOM size, so raising them needs the
  renderer too.
- Move-aware, formatting-insensitive tree diffs reduce reviewed lines for refactors (see section 4).
- Repeated re-diff of a PR across pushes: cached subtree hashes make force-push and rebase re-diffs
  cost proportional to the edit, if the hash cache is persisted.

What it could NOT change:
- The 1 MB / 300 file limits are dominated by transfer, DOM rendering, and storage of the diff, not by
  diff computation. A 1.8x faster line diff is invisible against that.
- Git packfile/object format. Anything we store must round-trip to Git-compatible patches.
- merge-ort wins came from rename detection and caching; a faster line differ does not touch them.

Single experiment: take the 1,000 largest merged PRs in 3 public monorepos (Linux, Chromium, a
TypeScript repo). Measure per-file wall time of `git diff --patience/--histogram` (via `git diff
--minimal` as exact reference) vs difffold line mode, and report what fraction of total
"files-changed" server time that is. Metric: diff compute as % of end-to-end API latency, plus count of
files that would drop under GitHub's 20 KB auto-load threshold after move/whitespace-aware reduction.
Decision rule: if compute is <10% of latency, do not pitch GitHub on speed.

---

## 2. GitLab

Cost drivers (VERIFIED from GitLab development docs "Working with diffs", with some conflicts):
- Collection limits are enforced in Gitaly: collapse after 100 files, 5,000 lines, 500 KB; stop
  rendering at 1,000 files. Per-file limit `diff_max_patch_bytes` (application setting) governs
  "Changes are too large to be shown". Older docs said collapse at 10% of that value; current docs
  differ. Gitaly returns `Diff.Collapsed` when collection limits are exceeded.
- Diffs are persisted to Postgres per MR version (SECONDARY from older mirror docs).
- I did not find a GitLab number for diff compute time. UNVERIFIED that compute is the bottleneck.

Could change: Gitaly could run a faster exact diff with fewer early cut-offs; collapse decisions made
cheaply from hash-equal subtrees. Could not change: DB persistence cost, UI rendering, safety limits
intended to protect Rails.

Experiment: replay `git diff` RPC equivalents on 100 MRs hitting the 5,000-line collapse. Metric: Gitaly
CPU-seconds per MR diff with limits off, line mode vs difffold. Reports how much headroom exists to
lift the collapse threshold.

---

## 3. Gerrit / Phabricator / Review Board / Sapling / ReviewStack

- Interdiff (diff between two revisions of a patch) is a recognized hard quality problem: Review Board
  has an internal "Debugging Interdiffs" guide (title seen only; content not read, UNVERIFIED).
- ReviewStack/Sapling: reviewer can see one commit, changes between two commits, or all (SECONDARY
  tutorial). Whether rebase noise is filtered in version-to-version views: UNVERIFIED.
- Cost driver here is quality (noise from rebases, stack churn), not CPU. No numbers found.

Could change: with content-addressed trees, "patch set N vs N+1 after rebase" is a diff of two
diffs; subtrees identical by hash can be dropped exactly, giving a principled interdiff. Could not
change: review UX, comment anchoring policy, server storage models in those tools.

Experiment: take 200 Gerrit changes (public: Android, Chromium) with >=3 patch sets that were
rebased. Metric: lines shown by naive `diff(PS_n, PS_n+1)` vs "interdiff with base-change excluded" vs
difffold structural interdiff; report % noise lines removed and exactness check (reconstruct PS_n+1).

---

## 4. Semantic-diff review tools

SemanticDiff (VERIFIED, product docs): parses per language, ignores syntax-irrelevant changes, per-
language invariances (example: Python keyword arg reorder `foo(a=1,b=2)` == `foo(b=2,a=1)`), detects
moved code and groups refactorings (rename). Runs the diff locally. 14+ languages (list varies by
page). Falls back to plain diff for unsupported files. Requires syntactically correct code.
Important: its invariances are lossy by design (reordered kwargs treated equal). Ours claims EXACT; those
are different promises and should not be conflated.

Greptile/CodeRabbit/Graphite (SECONDARY): Greptile claims 82% bug catch on a 50-PR, 5-repo benchmark it
ran itself (CodeRabbit 44%, Cursor 58%, Copilot ~54%, Graphite 6%); independent leaderboard numbers are
much lower (UNVERIFIED, from an aggregator). Greptile builds a repo graph; CodeRabbit reviews diff plus
context. None of these claims is about the diff algorithm; a better diff would only change the input
size and noise given to the model. Diffblue: not researched (UNVERIFIED relevance; it generates unit
tests, not diffs).

Could change: smaller, noise-free review input (formatting-only and moved hunks dropped or labeled)
for both human and LLM reviewers; deterministic moved-code labels cheaper than LLM judging.
Could not change: bug-finding quality, which depends on context retrieval and the model.

Experiment: 100 PRs with known injected bugs (Greptile's public set if released, else build one).
Run the same LLM reviewer with line diff vs difffold tree diff (moves collapsed, whitespace-only
dropped). Metrics: input tokens, catch rate, false positives. Claim only the token delta unless catch
rate moves with confidence intervals.

---

## 5. AI coding agents and LLM companies

Verified data points:
- Aider unified-diff post: GPT-4 Turbo 20% baseline (SEARCH/REPLACE) to 61% with unified diffs,
  lazy comments 12 tasks to 4 (3x reduction); gpt-4-0613 26% to 59%. This is the 2023 laziness
  benchmark on a specific model; it shows edit FORMAT changes quality massively. No whole-file figure
  on that page. Aider docs: "whole" is easiest for an LLM but uses many tokens and limits editable file
  size; diff-like formats edit larger files cheaper.
- Cursor "Editing files at 1000 tokens/s" (May 2024, via search summary of primary blog): fine-tuned
  Llama-3-70b with speculative edits (the original file is the draft), ~13x over vanilla inference,
  ~9x over prior GPT-4 speculative edits; Fireworks hosted. Cursor says Anthropic models could not do
  speculative edits. Vendor claim; no independent benchmark found.
- Morph fast apply: >10,000 tok/s per AWS case study (vendor-sponsored); 96% accuracy appears only in
  third-party listings (UNVERIFIED, low trust).
- Agentpatterns.ai example (single illustrative, not a benchmark): 5-line change in 1,200-token file,
  whole-file rewrite ~1,200 output tokens vs ~150-250 for search/replace.
- Claude Code issue reports: a one-line edit on a ~2,000-line file consumed ~30k tokens (tool result
  echoed file), closed Feb 2026; Write tool echoing full file doubled cost (user reports, SECONDARY).
- Anthropic's text editor tool uses `str_replace` with a uniqueness requirement (SECONDARY claim).
- Patch-apply failure rates for unified diffs in the wild: no primary number found. UNVERIFIED.

Cost driver: output tokens (decode is the slow, priced step) and apply failures. Diff algorithm CPU is
negligible next to LLM latency.

Where difffold could change things:
1. Apply-side determinism: fuzzy-apply (match anchor by tree position and hash instead of exact text)
   could cut str_replace "no match / multiple matches" retries. The retry rate is UNVERIFIED; measure it.
2. Feedback to the model: return a minimal tree diff of what changed (not the file) after an edit.
   Direct token saving on the tool_result side, which the Claude Code issues show is a real cost.
3. Speculative-edit drafts: Cursor uses the original file as draft; a structural alignment can supply
   better draft tokens after the first divergence. Gain unmeasured, UNVERIFIED.
4. Context compression across turns: send "diff against what the model last saw" using content-hashed
   file versions. Tokens saved scale with the unchanged fraction.

Could NOT change: decode speed/price per token; the model's decision to be lazy; the fact that models
emit text edits in formats they were trained on (changing format costs quality, as aider shows
both ways). A faster differ does not make the model faster.

Single experiment: SWE-bench-Verified-style run (or aider polyglot) with one model, three conditions:
(a) baseline edit tool, (b) baseline + minimal tree-diff tool_result instead of echo, (c) (b) + hash-
anchored fuzzy apply. Metrics: total input+output tokens per solved task, edit-apply failure count,
pass@1. Report tokens saved at equal pass@1 with bootstrap CI.

---

## 6. Web crawlers, Exa, Firecrawl

- Firecrawl change tracking (VERIFIED docs): `changeTracking` format on scrape/crawl/batch compares
  markdown against the previous scrape of the same URL by team (optionally tagged); returns status
  new/same/changed/(removed); `git-diff` mode returns a line diff (text and structured JSON); `json`
  mode compares schema fields via LLM extraction, 5 credits per page; basic tracking and git-diff no
  extra cost (pricing UNVERIFIED against live page). It diffs markdown, i.e. already loses DOM
  structure.
- Exa: no primary source found on change detection. UNVERIFIED anything about Exa internals.
- Cost driver: fetching and rendering the page (network, headless browser), not diffing. Boilerplate
  churn (ads, timestamps, nonces) causes false "changed" signals; that is a quality problem.
- Crawler dedup typically uses simhash/minhash (background knowledge, UNVERIFIED this session).

Could change: DOM/markdown tree diff with hash-consed subtrees gives a stable "what changed" feed that
ignores reordered/volatile blocks, O(changed) storage per page version (versions share subtrees), and
cheap "same?" via root hash. Could not change: fetch cost, JS-rendering cost, robots/politeness,
near-duplicate detection across different pages (that is similarity, not exact diff).

Experiment: re-crawl 10k pages daily for 14 days. Metrics: (a) storage per page-version vs gzip of
full markdown and vs delta store; (b) precision of "meaningful change" flag vs Firecrawl git-diff
labeled by 500 human-annotated pairs; (c) diff time per page. Claim only what wins.

---

## 7. CI and build systems

- bazel-diff (VERIFIED README via search): SHA-256 per target, source files hashed by content; two
  hash maps compared to get impacted targets; external repos treated as opaque unless opted in; supports
  query and cquery modes. Target Determinator is the sibling; Spotify describes the same workflow.
  No published cost numbers found.
- Cost driver: computing the build graph and hashing inputs (Bazel query/cquery), not the file diff.
  The VirtusLab text says fingerprints detect change, they do not prove affectedness.
- Test selection from diffs: the signal is which files/symbols changed. A symbol-level (tree) diff can
  distinguish comment/format-only changes from real ones, shrinking impacted sets. Magnitude
  UNVERIFIED; depends on how many commits are no-op for the build.

Could change: skip rebuilds for edits that are tree-identical after normalization (whitespace,
comments) when the build system lets you feed a normalized hash. Could not change: dependency graph
computation, remote-cache hit logic, flaky tests.

Experiment: on one Bazel repo's last 1,000 commits, compute the fraction of commits where normalized
tree hash of all changed files is identical (formatting/comment-only). Metric: percent of CI target
executions avoidable with a normalized-input hash, and false-negative count (must be 0, validated
by full build equivalence of outputs).

---

## 8. Package registries and supply chain

- diffoscope (VERIFIED via issue/list threads): 30 minutes on two 20 MB APK files (issue #272);
  ran out of 16 GB RAM on large kernel packages (Debian kernel MR); a Yocto patch capped diff block
  size cutting peak RSS from ~1.3 GB to ~400 MB on a 10 MB binary; upstream skips jsondiff over 100 KiB
  because it is O(n^2). The cost is recursive unpack plus quadratic text diffs on huge outputs.
- crates.io/npm release-diff tools: not researched (UNVERIFIED).
- Reproducible builds need bit-identical comparison: the useful operation is "hash equal -> done",
  which Merkle structure gives; diffs matter only for the unequal remainder.

Could change: replace quadratic/memory-heavy text diff of extracted members with a bounded, exact,
fast diff; dedupe identical members by hash across releases so cross-version diffs scale with change.
Could not change: unpacking formats, disassembly, binary-specific normalization (timestamps, paths),
which are where diffoscope's value lies.

Experiment: pick 50 diffoscope-hard Debian packages (kernel, browsers). Swap the text comparator for
difffold line diff at the leaf. Metrics: wall time, peak RSS, and byte-identical output of reported
differences up to the format. Honest framing: only the leaf comparator changes.

---

## 9. Documents, CRDTs, VCS

- Dolt (VERIFIED): "cost of computing a diff scales with size of the diff, rather than the size of the
  index", via prolly-tree hash-equal subtree skipping; SQLite diff is linear in both; SQLite is faster
  for small tables. Dolt query-diff is brute force, not this mechanism. THIS IS DIRECT PRIOR ART for the
  O(changed) claim; for rows, not syntax trees.
- CRDT performance (SECONDARY, one benchmark repo, methodology unverified): apply of a text-editing
  trace ~344 ms Automerge, 63 ms Loro, 20 ms diamond-types, ~4.2 s yrs. CRDTs avoid diffing during
  collaboration (operations are recorded), so diff is needed only at boundaries: importing external
  edits (a file changed on disk becomes ops) and presenting history.
- Pijul/jj/Sapling: not researched this session (UNVERIFIED). Known design: jj/Sapling track change
  identity across rewrite; a diff engine is a component, not the bottleneck.

Could change: "text file edited externally -> minimal exact ops" ingest into a CRDT; exact minimal
output matters because non-minimal diffs create spurious deletes/inserts that conflict in merges.
Could not change: CRDT convergence semantics, tombstone growth, history compaction.

Experiment: take 1,000 real file revisions from a repo; convert each to CRDT ops via (a) similar's
Myers, (b) imara-diff histogram, (c) difffold exact. Metrics: ops count, resulting history size, and
merge-conflict rate when replaying two concurrent branches.

---

## 10. Databases and lakehouses

- Iceberg incremental scan (SECONDARY): not in the spec; library feature using snapshot parent links;
  manifests whose added-snapshot-id is outside the range are skipped without being opened. Qualitative
  only; no benchmark found. lakeFS: not found (UNVERIFIED).
- Dolt as above.

Cost driver: metadata I/O (manifest reads from S3), not comparison. Our change-native storage on S3
competes on manifest layout rather than diff speed; that is a storage design argument, not a differ one.

Could change: a hash-consed layout gives Dolt-like O(changed) diffs for semi-structured/text files
inside a lake. Could not change: Parquet-level columnar diff, partition pruning, or catalog commit
contention.

Experiment: store 1,000 snapshots of a source tree (e.g. 1M files, 0.1% churn per snapshot) in
difffold vs Iceberg-style manifests vs plain git. Metrics: bytes read from S3 to compute
diff(snapshot i, i+k), GET count, and storage growth per snapshot.

---

## 11. Cross-cutting: honesty about our own numbers

- "1.8x faster than similar/imara-diff, identical minimal output": the correct comparison for exactness
  is against Myers minimal output; imara-diff's histogram is heuristic and is usually not minimal
  (UNVERIFIED this session), so say "same size as the minimal diff" and show the output-equality test.
- "4.2x median vs difftastic": difftastic documents Dijkstra on a lazily built graph and a graph limit
  (`DFT_GRAPH_LIMIT`), a byte limit (`DFT_BYTE_LIMIT`) and fallback to line diff for large files and
  parse errors (VERIFIED, changelog). Median hides tail behaviour; the value is in files where
  difftastic hits the limit. Report p95/p99 and the share of files that difftastic falls back on, with the
  fallback share at identical limits as the key figure. Also check if difffold output cost equals
  difftastic's cost metric; otherwise "better" is not comparable.

---

## 12. Five most defensible claims (ranked)

1. Output-token and tool-result-token reduction for coding agents: returning a minimal, exact, move-
   aware diff instead of echoing files, backed by aider (format changes 20% to 61%) and Claude Code
   issue reports as evidence the cost is real. Measure on a fixed agent benchmark.
2. Exact structural diff without the fallback cliff: difftastic documents falling back to line diff
   above graph/byte limits; difffold can state the fraction of real files that stay structural.
   Defensible only with measured p95 and fallback share.
3. Bounded time and memory for the leaf comparator in tools that blow up today (diffoscope 30 min on
   20 MB APKs; 16 GB OOM; O(n^2) jsondiff guard). Narrow, measurable, honest about scope.
4. Re-diff cost proportional to the change via hash-consed subtrees across versions (interdiff after
   rebase, repeated crawls, repeated agent turns), explicitly framed as bringing Dolt/Git-style
   Merkle skipping to syntax trees inside files.
5. Exactness as a property: identical minimal output at lower cost lets downstream systems (CRDT
   ingest, patch application, review) rely on deterministic, reproducible diffs. Show byte-equal output
   tests against a reference minimal differ.

## 13. Five claims we should NOT make

1. "Speeds up GitHub/GitLab diff pages": their documented limits are about transfer, rendering and
   storage; the 2016 GitHub post shows the fix was I/O fan-out. Compute share is unmeasured.
2. "Makes AI code editing faster/cheaper end to end" without a token and pass@1 experiment: decode
   speed and model price dominate; Cursor and Morph speedups came from speculative decoding with trained
   models, which we are not replacing.
3. "Better code review / finds more bugs": the bug-catch numbers (Greptile 82%) are vendor-run and
   attributed to retrieval and models, not to diff algorithm. Only claim input reduction.
4. "O(1) re-diff" unqualified: it is O(1) for hash-equal roots and O(changed paths) otherwise, needs a
   warm hash cache, and is not new in principle (Dolt, Git trees, Iceberg manifests, Bazel). Don't
   claim invention of content-addressed diffing.
5. "Replaces Git/diffoscope/SemanticDiff/Bazel tooling": each owns large non-diff parts (object
   storage and transfer, unpacking and normalization, per-language semantic rules, dependency graphs).
   Also avoid "semantic" equivalence promises: SemanticDiff-style invariances (kwarg reorder) are lossy,
   which conflicts with "exact".

## 14. Open items to verify next

- Fetch GitHub's "Large diffs are not rendered" exact text and the primary Blackbird post's dedup
  section; GitHub's 2025 diff-rendering post (only a secondary summary seen).
- Primary Cursor blog (cursor.com/blog/instant-apply) quotes; aider edit leaderboard numbers per
  format; any published str_replace failure rate.
- Exa internals; crates.io/npm diff tools (cargo-vet, diff.rs, npmdiff); lakeFS diff docs; Pijul/jj docs.
- imara-diff minimality; verify against our own harness before the "identical minimal output" claim.
