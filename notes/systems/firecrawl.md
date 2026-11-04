# Firecrawl documentation: change tracking and monitoring

Fetched 2026-11-03 (curl of .md versions):
- https://docs.firecrawl.dev/features/change-tracking.md
- https://docs.firecrawl.dev/features/monitoring.md
- https://docs.firecrawl.dev/features/monitoring-page.md
- https://docs.firecrawl.dev/features/monitoring-website.md
- https://docs.firecrawl.dev/features/monitoring-web-scale.md
FULL TEXT of change-tracking.md; monitoring.md read via targeted passages (about the first 150 lines in full plus greps on the rest); the three target pages read in their key sections. Not read: pricing details, rate limits, SDK pages. Docs snapshot of 2026-11-03.

## Mechanism
- Per-scrape diff primitive: "Every scrape with `changeTracking` enabled stores a snapshot and compares it against the previous snapshot for that URL. Snapshots are stored persistently and do not expire". `changeStatus` in {new, same, changed, removed}; also `visibility` in {visible, hidden} ("discoverable via links/sitemap" vs "URL works but is no longer linked"), `previousScrapeAt`.
- Compares markdown: "change tracking compares pages via their markdown content", so `markdown` format is mandatory. "The algorithm is resistant to whitespace and content order changes. Iframe source URLs are ignored to handle captcha/antibot randomization."
- Two diff modes: `git-diff` (line-level, text plus JSON AST) and `json`: "extracts specific fields from both the current and previous version of the page using a schema you define" and returns `{previous, current}` per field. JSON mode "uses LLM extraction and costs 5 credits per page". In monitors: "Even if no tracked field changed but the surrounding markdown did, JSON-mode monitors still report `same` unless you also enable git-diff".
- Identity of a "page": "Previous scrapes are matched on exact source URL, team ID, `markdown` format, and `tag`." Team-scoped: "Your first scrape of any URL returns `new`, even if other users have scraped it." Tags give separate histories per URL.
- Caveats in the docs: "Using different `includeTags`, `excludeTags`, or `onlyMainContent` settings across scrapes of the same URL produces unreliable comparisons." "Requests with `changeTracking` bypass the index cache. The `maxAge` parameter is ignored." "handle the `changeTracking` object potentially being absent (this can occur if the database lookup for the previous scrape times out)."
- Monitoring (scheduled): targets `scrape` (known URLs), `crawl` ("Every page discovered by a crawl"), `search` ("New results across the whole web"). "Each check records page-level results as `same`, `new`, `changed`, `removed`, or `error`." Minimum interval 5 minutes. "monitor-triggered scrapes default `maxAge` to `0`, so each check re-scrapes discovered pages fresh unless you set a different `maxAge`".
- Website monitor: `removed` is defined as "A page from the previous check was no longer discovered"; `error` is "The page could not be checked." Crawl bounded by `limit` and `maxDiscoveryDepth`, so a page can be "no longer discovered" because the limit/depth cut it off.
- Web-scale (search) monitor: "It's discovery rather than diffing." Dedup "is keyed on the canonical URL alone (title and snippet are deliberately not part of the fingerprint ...). Because the key is the URL, one real-world event reported across many article URLs alerts once per URL, not once per event."
- Goal and judge: optional plain-language `goal`; an LLM judge returns `meaningful`, `confidence`, `reason`, `meaningfulChanges` for changed pages; search results get `searchStatus` in {alert, already_seen, watching, ignored}; judge costs 1 credit per judged changed page.

## What is not guaranteed
- `removed` in the single-scrape change-tracking table is not defined in the page I read (what HTTP condition produces it). In crawl monitors it means "not discovered", which conflates deletion, de-linking, crawl limit, and robots exclusion; `visibility: hidden` partly addresses de-linking. `error` is separate, which is good, but a login wall served as HTTP 200 would be scraped as a (different) page and appear as `changed`.
- No entity correspondence: identity = exact URL string. A moved or redirected page is `removed` + `new`; a redesign that keeps the URL is `changed`. Search dedup is URL-only, with the event-vs-URL gap stated by the docs themselves.
- Content change is on extracted markdown (and optionally LLM-extracted fields), not on HTML or rendered interaction state. The JSON mode's LLM extraction can itself vary run to run; the docs do not give a determinism or stability guarantee.
- No dependency invalidation.

## Lessons
- Firecrawl is the clearest vendor example of the four-way separation inside one product: discovery (search/crawl targets), freshness (`maxAge`, default 0 in monitors), content change (`changeStatus` + diff), and failure (`error`). The weak rows are correspondence (URL equality) and removal (absence-in-crawl).
- "removed" is an inference from a crawl, not an observation; our model should record removal only as an observed 404/410 (or explicit tombstone content), and otherwise "not observed in run R under limits L".
