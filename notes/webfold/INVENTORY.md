# Inventory of code read (webfold / superdocuments / bench repos)

Read-only. Paths are relative to the repo named. Nothing was built; no `cargo check` was run.
Clones: `/home/user/webfold`, `/home/user/webfold-bench`, `/home/user/spbench`, `/home/user/superdocuments-bench`,
`/home/user/ptyktos-evals`, `/home/user/hashtrinity-bench`, `/home/user/ptyktos-api`, and
`/home/user/superdocuments` (cloned this session, depth 1). `transport`, `tas-media-proxy` and `calamine-apeiron` were not read.

## webfold (`/home/user/webfold`)

| Path | One line |
|---|---|
| `ARCHITECTURE.md` | Authoritative prose map. States `htmlfold`/`pdfcn` are NOT exported runtime modules; subtree-signature path includes `htmlfold/dom.rs` privately. |
| `src/html_extract.rs` | `to_blocks`, `Block{md,sig,links}` (L58), `norm_sig` mix2 fold (L989), `Template` (L1127), `render` (L1157), `chunk_markdown` (L1258). `fnv1a_bytes` (L65) is dead code here. |
| `src/html_extract/extraction_state.rs` | `BoundedExtraction`, `TracedBlock{text,start,end,depth}` (L206), `ExtractionRefusal` (L78): source-offset-carrying path, not wired to `Block`. |
| `src/html_extract/{table,booking,cms,next_data_fallback,...}.rs` | Table accumulation, site-specific extractors, hydration JSON fallback. |
| `src/node_signature.rs` | BLAKE3 Merkle signature per HTML element (`signatures`, L34), ignores style/handlers, normalises text, keeps `id/class/role/aria-label/data-testid`. Only caller: `src/main.rs:168` (CLI). |
| `src/htmlfold/dom.rs` | Immutable parse arena (`Dom`, `Node`, `NodeData`); node id = push position. |
| `src/dom.rs` | Mutable live DOM (`Document`, `Element`, `Node`); ids are indexes into `elements`/`nodes`. |
| `src/a11y/axtree.rs` | `AxNode{id,role,name,value,ignored,properties,parent_id,children}` (L31); ids `ax:{el}` / `ax:t{node}` (L64,68). Ordered children. |
| `src/cdp/dom.rs`, `src/cdp/inspect.rs` | CDP DOM (`backendNodeId == node id`) and `DOMSnapshot.captureSnapshot` (L663). |
| `src/cdp/pw/observers.rs` | `MutationObserver` that snapshots and compares subtrees at microtasks: an in-engine mutation log, not persisted. |
| `src/webmcp/*` | WebMCP form-tool discovery and fill plans; controls addressed "by index into `Document::elements`" (`mod.rs` L9). |
| `src/diff.rs` | The only existing differ: line diff of rendered Markdown via `similar`, then add/remove/modified classification. |
| `src/watch.rs` | `ChangeWatch` (`WatchState::check`, L99). Per-URL last `Record`, text diff, price/`Unavailable` heuristics. |
| `src/record.rs` | `Record`, `Source`, `WebSource` (L56). Drops `FetchResponse.status`. |
| `src/mcp.rs` | MCP tool bodies; `diff_snapshots` (L1432), `change_watch_check` (L1660). |
| `src/bin/webfold_mcp.rs` | Index JSONL maintenance: `index_record` (L2063), `merge_index_records` (L2146), `index_prune` (L1993), `content_hash` (L2170). |
| `src/crawl_index.rs` | In-memory `CrawlIndex`: pages table, adjacency, postings; `index_page` replaces a URL's postings wholesale (L562); no remove. |
| `src/folder.rs` | Local folder BM25/hybrid index with (size, mtime) stamp invalidation and 25-line window passages; optional embeddings (L120-180, 545-600). |
| `src/embed.rs` | `Embedder` trait (model id stable identity) and HTTP client; vectors only live in the folder index. |
| `src/postings.rs`, `src/search/answer.rs` | BM25 postings; passage ranking, `heading_path` + `byte_range`, citation check. |
| `src/acquisition/browser.rs` | CDP rendered capture: `BrowserSnapshot` (L131) and `BrowserState{Rendered,Empty,Challenge,Authentication,HttpError,ReadinessUnmet}` (L106; classified L1372-1404). |
| `src/acquisition/coordinator.rs` | `ResponseKind{Clean,Blocked,Empty}` -> `Strategy` table (L13-50), `ExecutionOutcome`. |
| `src/acquisition/readiness.rs` | Settle/readiness policy over text observations; `ReadinessRefusal` incl. `StableEmptyShell`, `TargetAbsent`. |
| `src/acquisition/evaluation.rs` | `TerminalClass{Accepted,Partial,Refused,Unavailable,Exhausted}` (L41): scored outcome vocabulary. |
| `src/acquisition/{plan,frames,redoc}.rs` | Effect-typed plan checker, frame tree policy, OpenAPI/ReDoc acquisition. |
| `src/lib.rs` (~L420-500) | `scrape_tiered_with_budget`; maps `stealth::BlockClassification` to `ResponseKind`. `scrape` returns `Result<String,String>`: status is lost to callers. |
| `src/fetch.rs` | `FetchBackend`, `FetchResponse{status,headers,body}` (L13), `FetchedResponse.effective_url`. |
| `src/http_cache/*` | moli-derived on-disk HTTP cache: ETag / Last-Modified revalidation, Vary, eviction. Transport-level, keyed by request. |
| `src/warc/*`, `src/corpus/{source,citation,ask}.rs`, `src/citation/` | WARC read/write with Block/Payload digests; `ArchiveRef{warc_path,record_id,offset,length,payload_digest}`; citation = quote + digest + archive ref. No revisit records. |
| `src/document.rs`, `src/document/cache.rs` | Office/EPUB/CSV conversion and `DocumentCache` keyed by numeric identity plus equal source bytes. |
| `src/claim_ledger.rs` | Per-claim `Grounded/Computed/Exhausted` by substring match; BLAKE3 claim fingerprint for dedup. |
| `src/jobs.rs`, `src/news_crawl.rs`, `src/streaming_crawl.rs` | Check jobs; frontier with seen-URL set; crawl. URL dedup only. |
| `src/extract.rs` | LLM -> JSON-schema extraction (the "structured record" path). Output is unversioned, untyped JSON. |
| `src/doctree/mod.rs` | Heading/page/outline tree over Markdown (`DocTree`, `PageIndex`) used for walk/search. |
| `src/view/structured_surface.rs` | Query layer over `superdocuments::graph::DocumentGraph`. |
| `webfold-exad/` | Empty scaffold crate for a "derived-state engine" (AGENTS.md: no `serde_json`/`reqwest`, no engine logic yet). The natural home for dependency edges. |
| `webfold-bench` (see below) | Harness. |

## superdocuments (`/home/user/superdocuments`, depth 1, 13k lines)

| Path | One line |
|---|---|
| `src/graph.rs` | `DocumentGraph{pages:Vec<Page>}` -> `Page{number,regions}` -> `Region{kind,bbox,reading_order,source,spans,link}`; `Span{text,bbox,cell}`; `Source` (Native/Ocr/Vlm/External with model+version). Builders `from_native`, `from_ocr_markdown`. |
| `src/html/extract.rs` | Second copy of `to_blocks`; `norm_sig` here still uses FNV-1a (L639), webfold's copy uses `mix2`. |
| `src/html/mod.rs` | `parse` -> `HtmlDocument{blocks:[HtmlBlock{markdown,signature,links}],markdown}`. |
| `src/document.rs` | `convert_bytes`, `LiftedDoc` with `DocCoord=(u32,u32,u32)` cells (L1385-1425), `DocumentCache` keyed by caller `u64` (FNV `fingerprint_bytes` L1503). |
| `src/markdown.rs` | Markdown block arena parser (`MarkdownDocument{nodes,roots}`; `Node{kind,children}`): a real ordered tree. |
| `src/pdf/mod.rs`, `src/pdf/geometry.rs` | PDF extraction, `extract_pages_markdown` (L89), `LayoutBlock` (geometry.rs L147), `page_blocks` is a Markdown-line classifier (L1968), not geometric. |
| `src/epub.rs`, `src/xlsx.rs` | Spine/manifest reader; `Worksheet{rows}` (sheet name is `Sheet N`). |
| not present | DOCX/PPTX/ODF/RTF live inside `src/document.rs`; there is no separate DOCX tree type. |

## Benchmarks and registries

| Path | One line |
|---|---|
| `webfold-bench/README.md`, `bench/STRUCTURED-CONVERSION.md` | Layout and Tracks A-F; results are JSON with `.provenance.json` siblings (corpus, revisions, SHA-256, rustc). |
| `webfold-bench/bench/structured-h2h/src/main.rs`, `bench/wcxb/`, `bench/results/*.json` | Rust runner per track; WCXB word-F1 harness; result files dated by suffix. |
| `webfold-bench/governance/STANDARD.md` | Five DoD pillars: non-vacuous contracts, mutation controls (BASELINE GREEN -> MUTANT RED -> RESTORE GREEN), file size and fanout limits. |
| `spbench/webfold-structured/{run.sh,README.md}` | Runner entry; subcommands `document`, `calamine`; flags `--warmup --samples --iterations --out`. |
| `superdocuments-bench/README.md` | Only an `ocr/` track exists; says new conversion benchmarks go here. |
| `ptyktos-evals/registry.toml` | `[layers.<layer>.benches.<name>]` with `bench_cmd, dataset, metric, baseline, default_signal, thresholds_{pass,drift,degraded,fail}`. Relevant layers: `web_agent`, `web_format_translation`, `retrieval`, `rag`. |
| `hashtrinity-bench/README.md` | Says block-signature hash comparison (FNV-1a vs apeiron `mix2`, "webfold#1") belongs here. |
| `ptyktos-api/src/{cache,warmer}.rs` | HTTP-side object cache with `etag`, `expires_at`; arXiv warmer. No content-level change detection. |
| `difffold` (`src/intern.rs`, `src/diff.rs`, `src/mapping.rs`) | `Arena::mk(label:u32, kids)`, `diff`/`diff_checked`, `Correspondence` with `before_to_after`. Labels are `u32`, so any adapter needs a label table. |
