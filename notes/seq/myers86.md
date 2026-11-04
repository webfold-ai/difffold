# Myers 1986, "An O(ND) difference algorithm and its variations"

- URL fetched: http://www.xmailserver.org/diff2.pdf (curl, 15-page PDF, pdftotext). Author-hosted copy of the Algorithmica 1(2) paper.
- Read: FULL TEXT (sections 1-4b, references skimmed; the "suffix tree" variation, section 4c, and the expected-case proof in 4a only skimmed).
- Problem: sequences A (len N), B (len M); edit graph on grid (x,y), horizontal/vertical unit-cost edges, diagonal free edge at match points a_x = b_y. LCS <=> shortest edit script (insert/delete only), D = 2(N-L).
- Main result: greedy furthest-reaching D-path algorithm, O((N+M)D) worst-case time; O(N + D^2) expected time under a random model; linear-space refinement by the middle snake, still O((N+M)D) time, O(D) working storage (O(N+M) with inputs). Assumes unit-cost indels, free matches, match test is O(1) equality.
- Quotes:
  - Sec 1: "Unlike others it employs the 'greedy' design paradigm and exposes the relationship of the longest common subsequence problem to the single-source shortest path problem."
  - Lemma 1: "A D-path must end on diagonal k in {-D, -D+2, ... D-2, D}."
  - Sec 4b: "As in the linear space algorithm of Hirschberg [7], a divide-and-conquer strategy is employed. ... The idea for doing so is to simultaneously run the basic algorithm in both the forward and reverse directions until furthest reaching forward and reverse paths starting at opposing corners 'overlap'."
  - Sec 4b: "Unfortunately, the input sequences A and B must be kept in memory, implying that a total of O(M+N) space is needed."
- Does NOT transfer to weighted top-down tree alignment:
  - The O(ND) bound needs unit-cost horizontal/vertical steps so that a D-path lies within D diagonals of the main one. Our delete/insert costs are subtree sizes (arbitrary positive integers) and a diagonal step costs dist(x,y), a recursive quantity; a cost-s path can move many diagonals in one step, so the "furthest reaching on diagonal k with cost d" table loses its O(D) width and its parity lemma.
  - Free diagonals (snakes) exist for us only for id-equal children (cost 0 by I1). That is a genuine snake analogue, but pair costs between unequal children are not 0/1 so the other diagonal moves are not unit mismatches.
  - Middle snake (Lemma 3) uses the parity/overlap argument on unit costs. With weights a split by cost ~D/2 need not hit a vertex at a clean cost boundary (same issue BiWFA handles with its p-wavefront window).
  - What does transfer: the shortest-path-in-a-DAG view, A*/Dijkstra over the edit graph, and the divide-and-conquer shape (Hirschberg) if the forward and reverse costs F, B of every cell are available without recursion order problems (see frontier experiment, question b).
