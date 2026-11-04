# difffold and a correspondence layer inside webfold

Scope: what exists in `webfold` (`/home/user/webfold`), `superdocuments`, and the bench repos, read from code. Paths are
relative to `webfold/` unless prefixed. Status tags: **[read]** seen in code, **[inferred]** reasoned, **[not evidenced]**.
No code was built or run, so no performance or accuracy claim is made for any integration below.

## 0. What the code says (the five findings that drive everything else)

1. **The only change detector is a Markdown line diff, and it lies about acquisition failures.** `src/watch.rs:99-164` fetches via
   `WebSource` (`src/record.rs:78`), which never reads `resp.status` (a 404 or 503 page becomes a normal `Record`), then diffs
   rendered text with `similar` (`src/diff.rs:121`). `ChangeKind::Unavailable` is "rendered text is empty" (`watch.rs:132`).
   A login wall, CAPTCHA page or JS shell that renders to nothing is reported as "GONE"; one that renders to some text is
   reported as `ContentChanged`. Also `change_watch_check` builds a fresh `WatchState` each call (`src/mcp.rs:1665`), so over MCP
   every check is `FirstSeen`. **[read]**
2. **A BLAKE3 Merkle DOM signature already exists but is unused by anything except a CLI row printer.**
   `src/node_signature.rs:34` hashes tag + five attributes + normalised text + child digests, ignoring style/handlers.
   Only caller: `src/main.rs:168`. It does not hash `href`, `src`, `value`, `checked`, `disabled`, `aria-*` other than
   `aria-label`, or position, and node ids are parse-arena positions. So it is a ContentId-like value, not an identity. **[read]**
3. **The block signature and its two copies disagree.** `Block.sig` is a 64-bit hash of the normalised block body
   (`src/html_extract.rs:225`, `norm_sig` L989, apeiron `mix2`), taken *before* the markdown prefix and blockquote prefix
   are added, so `# X`, `## X` and `> X` collide by design and ASCII case is folded. `superdocuments/src/html/extract.rs:639`
   still uses FNV-1a with a different byte feed (`fnv1a_bytes` in webfold is dead code, L65). The two crates therefore
   assign different `sig` to identical blocks, and neither is collision-checked. Its only consumer is `Template` frequency
   counting for boilerplate removal (`html_extract.rs:1127-1175`), which wants *lossy* equality. Reusing it as change identity
   would be wrong; replacing it with an exact interner would change boilerplate semantics. **[read]**
4. **Acquisition status is rich in the browser path and absent in the diff path.** `BrowserState{Rendered,Empty,Challenge,
   Authentication,HttpError,ReadinessUnmet}` (`src/acquisition/browser.rs:106`, classified at L1372-1404 by status >= 400 and
   substring matches such as "verify you are human"), `ResponseKind{Clean,Blocked,Empty}` (`coordinator.rs:13`),
   `ReadinessRefusal` (`readiness.rs:59`), `TerminalClass{Accepted,Partial,Refused,Unavailable,Exhausted}` (`evaluation.rs:41`).
   None of it reaches `Record`, `WatchEvent`, or the index. `Webfold::scrape` returns `Result<String,String>` (`src/lib.rs:396`). **[read]**
5. **Derived data is invalidated by replacement, never by dependency.** `CrawlIndex::index_page` retracts a URL's old postings and
   reinserts all of them (`src/crawl_index.rs:562-590`, no `remove`, no unchanged short-circuit); the JSONL index overwrites by URL
   and stores `markdown_hash` computed with `std::hash::DefaultHasher` (`src/bin/webfold_mcp.rs:2170`, not stable across Rust
   versions) that nothing compares; `index_prune` is age-only (L1993). The folder index re-reads and re-embeds a whole file
   when (size, mtime) changes, with fixed 25-line windows (`src/folder.rs:125-180`), so one inserted line shifts every later
   passage. `webfold-exad/` is an empty scaffold for "derived state" (AGENTS.md). **[read]**

Other facts used below: `WebSource` text goes through `to_blocks` (flat `Vec<Block>`, no tree, no node ids; links held in a
parallel `links` vec). `AxNode` is an ordered tree with role/name/value/properties (`src/a11y/axtree.rs:31`), the best
browser-side node for a differ. `webmcp` addresses controls by index into `Document::elements` (`src/webmcp/mod.rs:9`), which
shifts when the DOM changes. WARC code reads/writes payload digests but has no revisit records (grep found none), and
`ArchiveRef` + `payload_digest` already give a citation a stable raw-bytes anchor (`src/corpus/citation.rs:35-45`).

## 1. Representations

| Rep | Where | Shape | Node identity today | Ordered |
|---|---|---|---|---|
| Parse DOM | `src/htmlfold/dom.rs` | arena `Vec<Node>`, `children: Vec<id>` | position in parse (unstable under insertion) | yes |
| Live DOM | `src/dom.rs` (`Document.elements`, `nodes`) | arena + `ChildRef::{Element,Text}`; `id_map` for HTML `id` | index; CDP `backendNodeId` = that index | yes |
| Accessibility tree | `src/a11y/axtree.rs` | `Vec<AxNode>` with `parent_id`, `children: Vec<String>` | `ax:{el}` / `ax:t{n}` = DOM index | yes |
| Node signature | `src/node_signature.rs` | flat `Vec<NodeSignature{node_id,tag,digest}>`, postorder | digest = content, `node_id` = position | derived from order |
| Blocks | `src/html_extract.rs` `Block{md,sig,links}` | flat list in source order | none; `sig` is a 64-bit content hash, duplicates allowed | yes |
| Traced blocks | `extraction_state.rs` `TracedBlock{text,start,end,depth}` | flat list with source byte offsets | byte offset | yes; not wired to `Block` |
| Markdown chunks | `chunk_markdown` -> `ChunkSeed` | byte ranges `TextChunk{start,end}` | chunk index | yes |
| Record | `src/record.rs` | one `text` string + `metadata: Vec<(String,String)>` | `id` = URL | n/a (line-ordered text) |
| Doctree | `src/doctree/mod.rs` | heading tree + page index over Markdown | heading path | yes |
| Answer passage | `search/answer.rs` | `Passage{source,heading_path,byte_range}` | heading path + range | yes |
| Folder passage | `folder.rs` `Chunk` | fixed 25-line windows per file | `(path, window#)` | yes |
| Lifted office doc | `superdocuments/src/document.rs` `LiftedDoc` | hash table `DocCoord=(u32,u32,u32)` -> cell text + `order: Vec<DocCoord>` | coordinate (sheet,row,col / para / block idx) | yes via `order` |
| Markdown AST | `superdocuments/src/markdown.rs` | arena `nodes` + `roots` | arena index | yes |
| PDF | `superdocuments/src/pdf/mod.rs` | `extract_pages_markdown -> Vec<String>`; `LayoutBlock{kind,text,level,...}` | page index; no stable block id | yes |
| `DocumentGraph` | `superdocuments/src/graph.rs:215` | `pages -> regions -> spans`, regions carry `reading_order`, optional `bbox`, `Source` (model/version) | page `number` + position; none per region | yes, but a list, not a tree; cells via `Span.cell` |
| EPUB / XLSX | `epub.rs`, `xlsx.rs` | spine list; `Worksheet.rows` | spine id; sheet index, row, col | yes |
| LLM structured output | `src/extract.rs` | untyped JSON by caller schema | none | n/a |
| WARC / citation | `src/warc`, `src/corpus/citation.rs` | record with digests; `ArchiveRef` | `record_id` + payload digest | n/a |

Only the DOM, AX tree and Markdown AST are genuine trees. Everything the product searches over is flat.

## 2. Existing change detection / hashing

| Item | Path | Compares | Failure modes |
|---|---|---|---|
| `Record::diff_with`, `diff_markdown` | `src/diff.rs:115-145` | rendered Markdown, line level, Myers via `similar` | line = block only by accident; reorders are add+remove; ignores link destinations unless they are in the Markdown; blind to control state; fed text from a non-200 page |
| `WatchState::check` | `src/watch.rs:99` | `Record.text` vs previous; first `$NNN.NN` price | empty text == gone (L132); first price token only; no status/challenge check; state not persisted over MCP (`mcp.rs:1665`); clock is the literal `"2026-08-30"` (L115) |
| `diff_snapshots` MCP tool | `src/mcp.rs:1432` | two caller-supplied strings | same as above |
| `Block.sig` | `html_extract.rs:225,989` | normalised block body, case-folded, 64-bit | prefix (heading level, list marker, quote depth) excluded; collisions unchecked; links in `Block.links` not hashed separately (inline `[t](u)` text is in the body, bare `links` entries are not) |
| `Template` / `render(min_pages)` | `html_extract.rs:1127-1175` | per-page presence counts of sigs | wants lossy equality; counts wrap mod 2^32; can remove repeated valid content (documented in ARCHITECTURE.md) |
| FNV-1a `norm_sig` | `superdocuments/src/html/extract.rs:639` | same intent as above, different function | divergent sigs between crates (hashtrinity-bench README "webfold#1") |
| `node_signature::signatures` | `src/node_signature.rs:34` | BLAKE3 over tag, 5 attrs, text, child digests | omits `href/src/value/checked/disabled/aria-*`; empty subtrees get no digest (so deleting an empty element is invisible); unused in product paths |
| `markdown_hash` | `src/bin/webfold_mcp.rs:2087,2170` | whole-page Markdown | `DefaultHasher` is not stable across toolchains; stored, never compared |
| folder stamp | `src/folder.rs:88,125` | (size, mtime) | mtime-only touch re-embeds everything; same-size same-mtime edit missed |
| HTTP cache revalidation | `src/http_cache/revalidation.rs` | `ETag`/`Last-Modified` via 304 | transport validators; a 200 with changed ads/timestamps looks changed; a CDN ETag can lie |
| `DocumentCache` | `src/document/cache.rs:16`, `superdocuments/document.rs:1429,1503` | source bytes (webfold: numeric id + equal bytes; superdocuments: caller `u64`) | exact on bytes, so any byte change is a miss; FNV `fingerprint_bytes` is non-cryptographic |
| claim fingerprint | `src/claim_ledger.rs` | BLAKE3 of claim | not tied to a document version |
| URL dedup | `news_crawl.rs:222`, `streaming_crawl.rs:139` | URL strings | content duplicates under different URLs not detected |
| WARC `Payload-Digest` | `src/warc/records.rs` | payload bytes | no revisit/dedup records; digest is the raw body, so any dynamic token changes it |

## 3. Observation and acquisition status

- Fetch path: `FetchBackend::fetch -> FetchResponse{status,headers,body}`; `effective_url` only via `FetchedResponse` (`fetch.rs:13-25`).
  `WebSource` and `Record` discard status, headers and effective URL.
- Tiered scrape: `classify_response(status, html, headers, word_count)` -> `BlockClassification{Clean,Empty,Blocked{challenge,status,detail}}`
  -> `ResponseKind` -> `Strategy` (`lib.rs:470-492`, `coordinator.rs:26-50`). Output to callers is a String.
- Browser path: `BrowserSnapshot{http_status, state, readiness_route, blockers, ...}` (`browser.rs:131`). State is decided by
  status >= 400, then three challenge phrases, then three auth phrases, then readiness, then emptiness. Phrase lists are small English substrings **[read]**.
- A SPA loading state is `ReadinessUnmet` or `Empty` only on the rendered path; the plain `to_blocks` path has no concept
  (hydration fallback fires when initial text < 50 words, `ARCHITECTURE.md`).
- Mistakable for "content removed" (code-evidenced): non-2xx pages through `WebSource`; empty render (`watch.rs:132`);
  challenge/login pages with some text (they become `ContentChanged`); a partial capture cut by byte/node/action limits
  (`ExtractionRefusal::{OutputExceeded,BlockLimitExceeded}` are logged in `BoundedExtraction` but not on `Record`);
  an `Exhausted`/`Refused` terminal class exists only in the evaluator.

## 4. Derived data and invalidation

| Derived data | Where | Keyed by | When page changes |
|---|---|---|---|
| Markdown, title | `PageNode`, JSONL `markdown` | URL | overwritten |
| Term frequencies, postings | `crawl_index.rs` `postings`, `slot_terms`; JSONL `term_freq` | URL -> slot | full retract + reinsert (L562-590) |
| Outlinks / adjacency | `adj`, JSONL `outlinks` | URL | overwritten; no edge diff, no tombstone |
| Passage chunks | `chunk_markdown` (`ChunkSeed`), `folder.rs` windows | byte range / line window | recomputed whole; positional ids shift |
| Embeddings | `folder.rs` `Chunk.vec`, saved index; model id from `Embedder::id` | file path + stamp | whole-file re-embed on stamp change; full rebuild on model change |
| Cited answers / quotes | `search/answer.rs`, `corpus/citation.rs` | quote + `ArchiveRef` | citations stay valid against the archived bytes; nothing marks them stale against the live page |
| Claim ledger | `claim_ledger.rs` | claim text vs source text | recomputed on demand |
| Document conversions | `DocumentCache` | bytes | miss on any byte change |
| Agent evidence/receipts | `ExtractionRefusal.code()` "receipts", `acquisition/evaluation.rs` | case | scored offline; not linked to page versions |
| HTTP bodies | `http_cache` | request key + Vary | revalidated by ETag/Last-Modified |

So there is no dependency record from "block X of page P at version V" to chunk, posting, embedding, claim or answer. **[read]**

## 5. Bench conventions relevant to a diff track

- `ptyktos-evals/registry.toml`: add `[layers.<layer>.benches.<name>]` with `bench_cmd, dataset, metric, baseline, default_signal`
  and `thresholds_{pass,drift,degraded,fail}` (min/max keyed by metric). A diff track would sit in `web_format_translation` or a new `web_change` layer.
- `webfold-bench/bench/<track>/` holds a Rust runner (`structured-h2h/src/main.rs`); results land in `bench/results/<track>-<date>.json`
  with `<track>-<date>.provenance.json` (corpus, upstream revision, fixture SHA-256, runner SHA-256, rustc). `spbench/webfold-structured/run.sh`
  is the thin runner (`--warmup --samples --iterations --out`). `superdocuments-bench` currently has only `ocr/`.
- `webfold-bench/governance/STANDARD.md`: new kernels need non-vacuous contracts, mutation controls (GREEN -> RED -> GREEN), file <= 1,500 lines, <= 12 files per directory.
- difffold already has `harness/spbench-track` and `harness/run_all.sh` (not read in detail here); results format should match the above so `registry.toml` can point at it. **[not evidenced: compatibility of difffold's CSV with webfold-bench JSON]**
- Fixtures: webfold has `fixtures/warc/*.warc` and `tests/data`; there is no multi-version page corpus in any bench read. A diff track needs one (see 6d).

## 6. (a) Integration points, ranked

Value = what it fixes or enables. Risk = chance of semantic regressions or scope creep. Ordered by value/risk.

| # | Integration | Value | Risk | Files to touch | Adapter needed |
|---|---|---|---|---|---|
| 1 | **Observation envelope + status-gated change events** (not difffold itself; the precondition). `Record`/`WatchEvent` carry `Observation{status,state,final_url,truncation,digest}`; "removed" only on a trusted `Accepted` observation; otherwise `Unobserved{reason}` | Highest: stops false "GONE" now | Low | `src/record.rs`, `src/watch.rs`, `src/mcp.rs:1660`, `src/lib.rs:470-492`, `src/acquisition/browser.rs:131` | map `BrowserState`/`BlockClassification`/`ExtractionRefusal` to one `ObservationStatus` enum (section 6c) |
| 2 | **Block-sequence differ for the extractor** (`Vec<Block>` -> depth-2 tree: page -> blocks -> inline children) replacing `diff.rs` line diff; ContentId interning of blocks | High, low-medium risk: gives per-block add/remove/update with replay-checked scripts, tables as units | Medium: must keep `Template` semantics untouched | new `src/changeset.rs` (or crate `webfold-delta`); `diff.rs` stays as a fallback; `watch.rs` | root label `page`; child label = interned `(kind, normalised text, link set)`; leaf = block; table block = one leaf with row/cell children optional; normalisation = NFC, collapse whitespace, keep case, keep markdown prefix (unlike `sig`) |
| 3 | **Replace FNV-1a block sig in superdocuments with the existing `mix2` `norm_sig`, then use a separate collision-checked ContentId for change** | Medium: removes the cross-crate divergence (webfold#1) | Low if done as "make superdocuments match webfold"; Template counts change | `superdocuments/src/html/extract.rs:639`, `hashtrinity-bench` | none; add golden test that both crates give equal `sig` on `tests/fixtures` |
| 4 | **Accessibility-tree differ for browser action preconditions** | High for agents; medium-high risk | Medium-high: needs OccurrenceId and relevance policy | `src/a11y/axtree.rs` (adapter), `src/webmcp/{plan,execute}.rs`, `src/cdp/pw/*` | label = `(role, name, ignored, selected properties: disabled, checked, expanded, required, invalid, readonly, url, value-hash)`; kids = ordered AX children; leaf = text node or childless control; text normalised like `node_signature::normalized_text`; exclude `ignored` subtrees; the precondition is "subtree of the target + its form + its ancestors' roles unchanged", not "page unchanged" |
| 5 | **Delta-driven index invalidation** (chunk/posting/embedding records get dependency edges to block ContentIds) | High long-term | Medium-high: needs piece 3 of 6b | `src/crawl_index.rs:555-600`, `src/bin/webfold_mcp.rs:2063-2160`, `src/folder.rs`, `webfold-exad/` | edge = (derived record id) -> set of block ContentIds + extractor version; chunk by blocks not 25-line windows |
| 6 | **DOM structural delta for HTML (record level)**: use `node_signature` Merkle digests as ContentIds, difffold on `htmlfold` arena | Medium: explains *where* on the page | Medium: arena positions, best-effort parser differs from browsers (documented in the file) | `src/node_signature.rs` (extend attr set: `href`, `src`, `type`, `name`, `value`, `disabled`, `checked`), `src/htmlfold/dom.rs` | label = `(tag, selected attrs)`; leaf = text node (normalised); do not give empty subtrees no digest (they must exist to be deletable) |
| 7 | **Structured-record deltas** for `extract.rs` JSON and site extractors (`booking`, `cms`, `next_data_fallback`) | Medium | Medium-high: no stable schema or entity key exists | `src/extract.rs`, `src/html_extract/*` | JSON -> ordered tree: object keys sorted, label = key/scalar kind, leaf = scalar canonical string; list items need a caller-supplied key for OccurrenceId, else positional |
| 8 | **PDF/document page-level change** | Medium | Medium | `superdocuments/src/pdf/mod.rs:89`, `document.rs`, `epub.rs` | tree = document -> page/sheet/slide -> block/row -> cell; leaf = cell/line text; page = `<!-- page N -->` section; NOTE `page_blocks` is a Markdown classifier, bbox absent |
| 9 | **`DocumentGraph` deltas with provenance** | Medium; strongest provenance story (`Source{model,version}`) | Medium-high: only `from_native`/`from_ocr_markdown` builders exist, regions have no ids, OCR output is noisy | `superdocuments/src/graph.rs` | tree = doc -> page -> region -> span; label = `(kind, reading_order-independent text hash)`; keep `Source` as a *non-compared* annotation so an OCR model bump is reported as provenance change, not content change |
| 10 | **WARC revisit records / payload dedup** | Low-medium | Low | `src/warc/records.rs` | digest-equal payloads emit `revisit`; not related to difffold except as storage for VersionId |
| 11 | **Cross-version memo of pair results** (paper 6.6 #2) | Perf only | Low | difffold | key (before ContentId, after ContentId, objective, repr policy) |

Notes: #1 should ship even if difffold never lands. #2 and #4 are the two places where exact ordered correspondence is
actually the right tool; #6 duplicates #2 for a different layer and should wait. Moves are not detected by difffold
(README: "Moves, wrap/unwrap and cross-level matches are not implemented"), so a reordered product grid will read as
delete+insert until recorded-edit or similarity layers exist.

## 6. (b) The three missing pieces

**1. OccurrenceId assignment** (paper 6.1). difffold gives ContentId only: arena ids are equal iff structure is equal, and are
`u32`, per-arena, label = `u32`.
- Where: new crate `webfold-delta` (or module `src/changeset/`), *not* inside difffold, because it needs webfold representations.
  difffold provides `Correspondence` (`src/mapping.rs`); webfold stores it.
- Rule for the first slice: an occurrence is `(page_key, role-path, ordinal-among-same-ContentId-siblings-at-first-sight)`; on a
  new version, carry the OccurrenceId across every pair in the difffold script (`Keep` and `Update`), mint fresh ids for
  inserts, retire ids for deletes. Identical sibling cards therefore keep ids positionally and only a reordering breaks them,
  which is the documented gap. **[inferred]** Where the page offers a key (HTML `id`, `data-testid`, `href`, JSON key) use it
  to pin the id; those attributes already feed `node_signature`.
- Cross-process stability requires a canonical content hash. difffold's arena ids are not stable across runs; `node_signature`
  uses BLAKE3 over length-prefixed fields, which is the right shape. Persist `(blake3 content digest, occurrence id)`; use
  arena ids only inside one diff.

**2. Observation-status model.** One enum shared by fetch, browser and extractor, attached to every stored version:
`Observed{complete|partial(reason)}`, `Unobserved{http_error(status)|challenge|auth_required|timeout|readiness_unmet|blocked_by_policy|transport_error}`.
- Where: `src/record.rs` (the type), populated by `src/lib.rs:470-492` (`BlockClassification`), `src/acquisition/browser.rs:1372-1404`
  (`BrowserState`), `extraction_state.rs` (`ExtractionRefusal` -> `partial`). Reuse `TerminalClass` names where they fit
  (`Accepted/Partial/Refused/Unavailable/Exhausted`, `evaluation.rs:41`) instead of inventing new words.
- Rule: a delta may contain `Removed` only between two `Observed{complete}` versions of the same canonical URL with the same
  extractor/policy version. Otherwise emit `NotComparable{why}`. Absence after a redirect to a login host is `auth_required`, not removal.
- Known weakness to keep visible: the challenge and auth detectors are English substring lists (`browser.rs:1380-1398`), so
  localised walls will pass as `Rendered`. **[read]**

**3. Dependency edges from deltas to derived records.** Needed so a delta can answer "which chunks, postings, embeddings,
claims, answers are stale".
- Where: `webfold-exad/` (already scoped as the derived-state engine; today empty, `serde_json`/`reqwest` banned) holds the edge
  store and invalidation query; `crawl_index.rs`, `folder.rs`, `claim_ledger.rs` register edges when they derive.
- Edge: `derived_id -> {(page_key, occurrence_id, content_digest)}` plus `{extractor_version, chunker_version, embed_model_id}`.
  Invalidate when any input ContentId changed *or* a version tag changed (`Embedder::id` already exists for the latter).
- The chunker must stop using positional windows for HTML-derived text or the edges will point at everything after the first change.
- Citations keep working independently via `ArchiveRef.payload_digest`; the new edge adds "the live page no longer supports this quote".

## 6. (c) Candidate observation-to-delta schema

JSON-shaped for readability; webfold's own rule (`webfold-exad/AGENTS.md`) is hashtrinity not serde_json, and the repo-wide
norm is versioned binary, so the on-disk form should be decided separately.

```text
Observation {                         // one immutable VersionId
  version_id:   blake3(canonical bytes of the fields below, excluding version_id)
  page_key:     canonical URL after policy (fragment stripped, tracking params policy named)
  requested_url, final_url, fetched_at_ms
  acquisition:  { tier: http|headless|cdp_render, http_status?, state: ObservationStatus,
                  readiness_route?, blockers[], truncation[], backend_version }
  raw:          { payload_digest, archive_ref? {warc_path, record_id, offset, length} }
  extraction:   { extractor_version, policy_hash, repr: "blocks-v1" | "ax-v1" | "dom-v1" | "docgraph-v1" }
  root_content_id: blake3(...)          // Merkle root over canonical tree
  nodes?:       [ { occurrence_id, content_id, label, parent_occurrence, ordinal, source_span? } ]  // optional, large
}

Delta {
  delta_id, kind: historical | optimal | presented,
  from_version, to_version, objective: "selkow-unit-v1", repr_policy_hash,
  comparable: yes | no(reason)          // from ObservationStatus gate
  ops: [ Keep{occ} | Update{occ, from_content, to_content}
       | Insert{occ_new, content, parent_occ, ordinal} | Delete{occ, content, subtree_size} ]
  cost: u32, certified: bool, replay_checked: bool, difffold_version
  provenance: { source: recorded | inferred(tier), evidence[] }   // every inference named
}

Dependency { derived_id, derived_kind: chunk|posting|embedding|claim|answer,
             inputs: [ {page_key, occurrence_id, content_id} ], versions: {extractor, chunker, model} }

Invalidation { delta_id -> [derived_id], reason: input_changed | version_tag_changed | input_unobserved }
```

`Unobserved` observations produce no `Delete` ops. They produce a `Delta` with `comparable=no`. Fields not in the repr
(link destinations, control state) must be in `label`, otherwise the delta is silently incomplete: that is the principal
adapter risk.

## 6. (d) First vertical slice (about one week)

**Goal:** a block-level, status-gated change feed for one URL, with difffold as the engine and a persisted OccurrenceId, wired
into `ChangeWatch`. Excludes DOM/AX, indexes, and moves.

Day 1-2: `webfold-delta` crate (path dependency on difffold). Types: `ObservationStatus`, `Observation`, `BlockTree` builder.
Adapter: `Vec<Block>` -> arena tree `page( block_i )` where each block is a node with label table entry
`(md_prefix_kind, normalised_text, sorted_link_destinations)` and, for table blocks, one child per row. Persist the label table
with BLAKE3 digests as the cross-process content hash.
Day 3: wire status: change `WebSource` to return `Observation` and refuse to build a `Record` from `HttpError/Challenge/Auth`;
`watch.rs` emits `NotComparable`. Fix `mcp.rs:1665` persistence of `WatchState` (store last version).
Day 4: run `diff_checked`, convert `Correspondence` to ops, assign OccurrenceIds (rule in 6b).
Day 5: corpus + bench entry. Build a multi-version fixture set (see below), a runner in `webfold-bench/bench/change-delta/`,
a `registry.toml` entry, results + provenance JSON.

**Acceptance tests**
1. Replay: for every fixture pair, `apply(before, ops) == after` and `cost == dist` (difffold C3/C4 already enforce this on trees; test it again through the adapter, including label-table round-trip).
2. Status gate: a 404 page, a challenge page ("verify you are human"), a login page, and an empty render after a good capture
   each yield `comparable=no`; none yields a `Delete`. Negative control: disable the gate, tests go red.
3. Link-only change: change an `href` with identical visible text; old `diff.rs` reports `Unchanged` or a line modify depending on rendering;
   new path reports `Update` on that block. (Confirm the old behaviour empirically; expectation is **[inferred]**.)
4. Control-only change on a form block is NOT visible to blocks (documented limit) and must be listed as `not_in_representation`, not claimed unchanged.
5. Occurrence stability: insert one block in the middle; OccurrenceIds of all other blocks unchanged; insert an identical-duplicate block: ids stay positional.
6. Determinism: same HTML twice gives identical `root_content_id` across two processes; shuffling attribute order does not change it.
7. No regression: `Template`/`render` outputs byte-identical on `tests/data` and `webfold-bench/bench/structured-h2h` fixtures (Track A 1.000 quality unchanged).
8. Cost: report adapter + diff time per fixture against `Record::diff_with` as measured data, no pass/fail threshold until measured.

**Corpus needed (does not exist in the repos read):** at least 30 before/after page pairs with labelled change type
(text edit, link edit, insert, delete, reorder, pure-chrome change, outage page, challenge page). Sources: synthetic mutations of
`webfold-bench/bench/structured-h2h` HTML fixtures (honest label: synthetic), plus any real recrawled WARC pairs if available.

## 6. (e) Risks and what is NOT evidenced

- **Not evidenced:** that difffold's speed (README: 14.2x over OmniDiff's recorded diff time on code fixtures) transfers to web
  trees. All measured data is Java/Go/C. Web DOMs are wider and more repetitive (cards, rows), which the README says is where
  threshold widening costs more.
- **Not evidenced:** accuracy of the Selkow top-down objective on web pages. Insertion of a wrapper `<div>`, a very common
  redesign change, costs the entire wrapped subtree (delete + insert) because matching needs matched parents. Paper 8.5 accuracy is `PENDING`.
- **Not evidenced:** that block-level change detection beats the line diff on real pages; no labelled corpus exists. Today's
  line diff already operates at block granularity for most text because `to_blocks` emits one paragraph per line (inferred, unchecked).
- Moves, reorders of keyed lists, and cross-level matches are not supported by difffold; product grids reorder constantly.
- Representation gap is the dominant risk: `Block` loses DOM structure, form state, hidden-state toggles, link destinations
  outside the inline Markdown, `aria-*` beyond what rendering keeps. Anything not in the label is invisible to the diff.
- Noise: timestamps, CSRF tokens, ad slots, A/B variants change content on every fetch. Nothing in webfold models volatile
  regions; `Template` only removes recurring blocks across pages, not across time. A per-site volatility policy is out of
  scope here and needed for alert fatigue.
- Hash functions: FNV-1a (superdocuments), mix2 (webfold), `DefaultHasher` (JSONL), FNV-style `fingerprint_bytes` (document cache),
  BLAKE3 (`node_signature`, claim ledger, doc-cache bench provenance). Any new identity must pick BLAKE3 over canonical bytes and say so.
- Duplicate code: `to_blocks` exists in both webfold and superdocuments; a webfold change that is not mirrored will diverge
  (it already has on `norm_sig`). Webfold's `ARCHITECTURE.md` says superdocuments owns it and webfold re-exports, but `src/html_extract.rs` is a full local copy.
- Governance: new kernels need the DoD pillars (contracts, mutation controls, size and fanout limits) before merge.
- `webfold-exad/` is explicitly "empty of engine logic by owner decision"; placing dependency edges there is a proposal that needs the owner's sign-off, not a given.
- Not read: `transport`, `tas-media-proxy`, `calamine-apeiron`, `webfold-dag/*` planning docs (may already specify a derived-state
  design: `webfold-exad/AGENTS.md` cites "Part 3b of the WEBFOLD-SEARCH architecture doc", which was not located).
