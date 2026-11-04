# TechRadar: OpenAI reportedly building a GitHub alternative

URL fetched 2026-11-03: https://www.techradar.com/pro/openai-reportedly-building-a-github-alternative-after-saying-microsoft-owned-platform-is-not-yet-meeting-our-expectations (page title: "OpenAI builds its own internal GitHub alternative after repeated outages leave engineers struggling with AI-powered development workflows"). Metadata datePublished 2026-03-11. FULL TEXT of the article (curl, ~11 KB). It ends "Via Tom's Hardware", i.e. it is a secondary report of a report. A web search also surfaced news aggregators attributing the original to The Information; the TechRadar article itself I read does NOT name The Information (another TechRadar piece does, via search snippet only, not fetched).

## What it claims
- "OpenAI is reportedly developing an internal code repository platform after frequent outages on GitHub disrupted coding operations for its engineers."
- Motive: GitHub's migration to Azure; "An early February 2026 four-hour outage was traced to an Azure problem, and a separate week-long outage was linked to a configuration change, which GitHub publicly acknowledged as 'not yet meeting our expectations.'" Also cites a GitProtect report: "58% year-over-year increase in incidents during 2025, with 17 classified as major".
- "Employees familiar with the project said the platform could eventually be offered commercially, potentially bundled with Codex coding agents, although it may remain exclusive to OpenAI."
- "OpenAI has not publicly confirmed the project." "The platform remains in early development and could take months before any operational rollout."
- Context sentence: "Developing internal code repositories is a common practice among large technology firms, with Google operating Piper and Meta using Sapling, but none have been commercialized."

## What it does NOT claim
- Nothing about the design: no mention of diffs, changesets, content addressing, derived data, or incremental computation. It mentions Ultra Ethernet and "vibe coding" laptops as speculation ("may use").
- No performance numbers for the planned system. The only numbers are GitHub incident statistics.
- Not confirmed by OpenAI; sourced to unnamed "employees familiar".
- Predates Anthropic's Scion post (2026-10-13) by seven months, so it cannot be used as a response to or corroboration of Scion.

## Lesson
Paper Sec 2.4's wording ("unconfirmed by OpenAI and is evidence of pressure on developer platforms, not of a new diff method") is accurate. The evidence is of reliability pressure (outages), which is itself an acquisition-failure analogue: an unavailable upstream is not an empty or deleted repository. Weak evidence; keep it to one clause or drop it.
