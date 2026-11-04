# Myers 1999, "A fast bit-vector algorithm for approximate string matching based on dynamic programming"

- URL fetched: https://www.gersteinlab.org/courses/452/09-spring/pdf/Myers.pdf (curl; course-page copy of J. ACM 46(3):395-415, pdftotext gave ~780 lines, abstract through references). The ACM page itself returned 403.
- Read: full text of the copy, but the proofs of the block-based/zone sections (Sec 5-6) only skimmed. Sec 1-3 read.
- Problem: find all text positions where a query of length m matches with <= k differences (unit-cost edit distance, Sellers' column DP C[i,j]).
- Main result: bit-vector encoding of the vertical deltas of the DP column gives O(nm/w) time independent of k; blocked in the Ukkonen zone it gives O(kn/w) expected time for large m. Assumes unit costs and word size w.
- Quotes:
  - Abstract: "...requires only O(nm/w) time by virtue of computing a bit representation of the relocatable dynamic programming matrix for the problem. Thus, the algorithm's performance is independent of k..."
  - Sec 2: "LEMMA 1. [MASEK AND PATERSON 1980; UKKONEN 1985]. For all i, j: Dv[i, j], Dh[i, j] in {-1, 0, 1}."
  - Sec 1: "The algorithm achieves its efficiency by computing only the region or zone of the underlying dynamic programming matrix that has entries less than or equal to k."
- Does NOT transfer: everything rests on Lemma 1 (deltas in {-1,0,1}), so a column is 2 bits per cell. Our deltas are bounded only by subtree sizes and by recursive tree distances, and match/mismatch is not a character equality but a recursive cost, so there is no bit-parallel Eq mask. Not applicable to the tree aligner except possibly to the unit-weight special case (all children leaves), where it is irrelevant for runtime because those lists are short.
