# arXiv:2604.12696 (checked: it exists)

URL fetched 2026-11-03: https://arxiv.org/abs/2604.12696 (abstract page; HTTP 200). ABSTRACT ONLY. I did not download or read the 43-page PDF.

## Facts
- Title: "Longest Common Extension of a Dynamic String in Parallel Constant Time". Author: Daniel Albert (single author). Subject: cs.DS. "Submitted on 14 Apr 2026". Comments: "43 pages, 8 figures, to be published in 37th Annual Symposium on Combinatorial Pattern Matching (CPM 2026)".
- Abstract claims: a dynamic LCE algorithm "maintains a data structure that allows efficient LCE queries on a string that can change via character insertions and deletions." "A dynamic parallel constant-time algorithm is presented that can maintain LCE queries on a common CRCW PRAM with O(n^epsilon) work, for any epsilon > 0." It maintains "a string synchronizing sets hierarchy" used for substring equality, then LCE. "To achieve constant runtime, the algorithm allows parts of its information to become outdated by up to log n log* n updates. It answers queries by combining this slightly outdated information with a list of the recent changes." Applications: maintaining Dyck-language membership and maintaining squares, both "with O(n^epsilon) work".

## Check against paper.md
- Sec 3 (line ~226) says: "constant parallel time with O(n^e) work on a CRCW PRAM (a recent dynamic-string result) is not constant sequential work." CONFIRMED as a description of the abstract. The paper's use is as a cautionary example, which is appropriate.
- What it is NOT: a diff, edit-distance, or tree-differencing result. LCE queries are exact-match extension lengths on one maintained string. It says nothing about edit distance, alignment, or provenance.
- Detail worth keeping: it deliberately lets the structure go stale by up to log n log* n updates and patches queries with a list of recent changes. That is the same idea as keeping a frontier of unprocessed deltas in front of a lazily maintained summary (paper Sec 6.5), but it is a PRAM-model constant-time trade-off, not evidence for our cost claims.
- Because only the abstract was read, I cannot say what the sequential cost or the model details are.
