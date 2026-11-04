# Marco-Sola et al. 2021, "Fast gap-affine pairwise alignment using the wavefront algorithm" (Bioinformatics 37(4):456-463)

- URL fetched: https://www.ebi.ac.uk/europepmc/webservices/rest/PMC8355039/fullTextXML (Europe PMC open-access full-text XML, converted to text; PMC web page itself hit a captcha).
- Read: FULL TEXT of the main article (about 46k characters); supplementary material not read.
- Problem: global gap-affine alignment, penalties (x mismatch, o gap open, e gap extension); DP matrices I, D, M.
- Main result: exact algorithm, O(ns) time (n length, s optimal score) and O(s^2) memory, by iterating scores and keeping "furthest-reaching" points per diagonal. Assumes small integer penalties and sequence similarity (small s).
- Quotes:
  - Abstract: "...the WFA runs in time O(ns), proportional to the read length n and the alignment score s, using O(s2) memory."
  - Sec 2.2: "Restricted to the edit distance, the so-called diagonal-transition algorithms exploited the fact that DP diagonals have monotonically increasing scores. In particular, Myers' O(nd) algorithm ... Our algorithm extends these ideas to the gap-affine model."
  - Sec 2.2: "...each new wavefront grows to span over one more diagonal on each end ... Hence, the algorithm requires O(s2) memory to store all wavefronts."
- Does NOT transfer: (1) the wavefront grows by exactly one diagonal per score unit, which holds because gap penalty (o+e, or e) is a small constant; ours are subtree sizes, so one score step can jump many diagonals and wavefronts are sparse, not dense. (2) The free "extend" along matching characters is a snake; ours exists only for id-equal children. (3) The O(ns) bound counts character comparisons O(1) each; ours are recursive dist calls. The score-ordered expansion is, however, the same idea as best-first search (Dijkstra) on the edit graph, which is what src/frontier.rs implements.
