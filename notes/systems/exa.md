# Exa documentation: freshness, Monitors, Websets

Fetched 2026-11-03 via curl of the .md versions of the docs (docs.exa.ai redirects to exa.ai/docs):
- https://exa.ai/docs/contents/quickstart.md (section "Content freshness")
- https://exa.ai/docs/reference/get-contents.md (OpenAPI schema)
- https://exa.ai/docs/admin/faqs.md
- https://exa.ai/docs/monitors/quickstart.md and https://exa.ai/docs/reference/monitors/create-a-monitor.md
- https://exa.ai/docs/websets/api/monitors/create-a-monitor.md
- https://exa.ai/llms.txt (index)
FULL TEXT of each page listed (documentation, not papers). Not read: Websets quickstart, search ranking docs, pricing. Docs change; this is a snapshot of 2026-11-03.

## Freshness of observation
- Current parameter is `maxAgeHours` (the old `livecrawl` string is deprecated). Table: "Omit: Use cached content when available and fetch the page when needed. Positive integer: Use cached content if it is newer than this many hours, otherwise fetch the page. 0: Always fetch fresh content. -1: Only use cached content." Schema: integer from -1 to 720.
- "Most requests should omit this field. Set it when stale page content would be unusable, such as for prices, availability, or frequently updated pages."
- Fresh fetch is bounded: `livecrawlTimeout` default 10000 ms, max 90000.
- Per-URL report: `statuses[]` with `status` in {success, error}, `source` in {cached, crawled}, and on error an `error.tag` and `httpStatusCode`. "Check `statuses` for the success or failure of every URL." So acquisition failure is reported separately from content.
- I found NO per-result "observed at / crawled at" timestamp in the get-contents result schema (only `publishedDate`: "An estimate of the creation date, from parsing HTML content"). `source: cached` does not tell the caller how old the cache was.
- Index freshness (FAQ): "Exa discovers and refreshes pages continuously, with timing that varies by source and how often a page changes." No refresh interval guarantee. Crawler: "respects the Robots Exclusion Protocol ... does not attempt to bypass logins, paywalls, or CAPTCHAs." (so a login wall is an acquisition failure on their side, but the docs I read do not give an error tag for it.)
- `snapshotAsOf`: "Return the newest stored version of each page as of this instant ... Historical requests are served from stored versions only and never fetch the live page." So Exa exposes an as-of read over stored versions, but I found no diff or version-id API over them.

## Discovery
- Search finds pages. Monitors API: "Each monitor runs Exa searches on a recurring schedule and delivers results to a webhook endpoint." "On each run, Exa executes the configured search, filters by time, removes results or findings the monitor has already returned, and sends the new output to your webhook." Create-a-monitor: "drops results that match what earlier runs already returned, so your webhook receives only new developments."
- Schedule: minimum interval 1 hour (`1h`, `6h`, `1d`, `7d`); "each run may be delayed by up to 30 minutes"; "Monitor runs do not overlap. If the next scheduled run starts while the previous one is still running, Exa cancels the previous run."
- Output: `output.results` plus an LLM-synthesised `output.content` (text or JSON per `outputSchema`) with `output.grounding` for sources. Run statuses: pending, running, completed, failed (with `failReason`), cancelled.
- Websets monitors: run a `cron` search; behaviour `append` (default) or `override`; run types `search` or `refresh`. Websets items carry enrichment results; I did not read how `refresh` decides an item changed, so I make no claim.

## What is NOT guaranteed (by the docs I read)
- Monitors dedupe on "what earlier runs already returned" with no stated key (URL? content?) and no statement that a changed page re-fires. It is discovery of new results, not change detection on known pages.
- No guarantee that a result is observed after any given time unless the caller sets `maxAgeHours` on contents; a Monitor's search `contents` can carry `maxAgeHours` per the schema text I saw, but the quickstart does not say what default applies.
- No removal/deletion semantics at all in Monitors; no entity-correspondence notion beyond Websets' "entity" types (company, person, article, paper, custom) used for search targeting.

## Lessons
- Exa cleanly separates DISCOVERY (search/monitor) from FRESHNESS OF OBSERVATION (`maxAgeHours`, `statuses.source`). This validates the paper's separation but note freshness is a REQUEST-time knob with a per-URL success/cached/crawled report and no timestamp; our observation record must carry its own `observed_at` and `acquisition outcome`.
- `snapshotAsOf` shows a vendor treats "state as of t" as a first-class read; our VersionId should be the key for it.
