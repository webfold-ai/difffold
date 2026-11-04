# Ukkonen 1985, "Algorithms for approximate string matching"

- URLs tried: https://www.sciencedirect.com/science/article/pii/S0019995885800462 (HTTP 403 via curl and WebFetch, bot wall); the ScienceDirect PDF link (403); dl.acm.org mirror (403). Metadata only from Crossref: Information and Control 64(1-3):100-118, DOI 10.1016/S0019-9958(85)80046-2 (Crossref record has no abstract).
- Read: NOT READ. Neither the full text nor the abstract was reachable. Everything below is a SECONDARY SUMMARY from texts I did read in full: Myers 1999 (JACM, Gerstein-lab copy) and the Marco-Sola WFA paper. Do not cite Ukkonen's results from this note as read.
- What the secondary sources say it contains:
  - Myers 1999, Sec 1: "...this was refined to O(kn) expected time by Ukkonen [1985]..." and "The algorithm achieves its efficiency by computing only the region or zone of the underlying dynamic programming matrix that has entries less than or equal to k." (the "Ukkonen zone"/cutoff).
  - Myers 1999, Lemma 1 is attributed "[MASEK AND PATERSON 1980; UKKONEN 1985]": adjacent entries of the unit-cost edit-distance DP matrix differ by -1, 0 or +1.
  - A web-search snippet (third party, unverified) gives O(s*min(m,n)) time and O(min(m,n,s)) space for edit distance s.
- Problem (per secondary): k-differences / edit distance with unit costs; computing only cells with value <= threshold, doubling the threshold when the result exceeds it.
- Relevance (honest): our threshold solver (prune when F + h > tau, double tau) is the same idea as the cutoff-with-doubling family. I cannot say from reading what Ukkonen's exact bounds or proof of the cutoff are. A paper should cite it as "cutoff DP in the style of Ukkonen" only after someone obtains the text.
- Does NOT transfer: the +-1 adjacent-difference lemma (basis of Myers 1999 bit vectors and of the O(s) band width) fails when indel costs are subtree sizes and pair costs are recursive distances. The zone bound "cells with value <= k are within k diagonals of the main one" fails for the same reason. Our h(i,j)=|R_a(i)-R_b(j)| is a size-weighted analogue of Ukkonen's diagonal-distance bound, not the same lemma.
