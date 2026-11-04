# Marco-Sola, Eizenga, Guarracino, Paten, Garrison, Moreto 2023, "Optimal gap-affine alignment in O(s) space" (BiWFA, Bioinformatics 39(2):btad074)

- URL fetched: https://www.ebi.ac.uk/europepmc/webservices/rest/PMC9940620/fullTextXML (Europe PMC open-access full text, converted to text).
- Read: FULL TEXT of the main article (about 39k characters); the correctness proof of Sec 2.4 skimmed, supplement not read.
- Problem: gap-affine global alignment in less memory than WFA's O(s^2).
- Main result: run WFA forward and reverse alternately, keep only the last p wavefronts of each (p = window set by the penalties), detect an overlap giving a breakpoint on an optimal alignment at score about s/2, recurse on both halves. O(ns) time, O(s) memory excluding inputs. Assumes bounded integer penalties.
- Quotes:
  - Abstract: "...the first gap-affine algorithm capable of computing optimal alignments in O(s) memory while retaining WFA's time complexity of O(ns)."
  - Sec 2.3: "In general, two prefixes of the optimal alignment that differ by one character can have scores that differ by as much as p. Accordingly, we will demand a weaker notion of balance. If sf and sr are the forward and reverse scores, respectively, we will aim to have |sf-sr| <= p."
  - Sec 2.6: "...each forward and reverse search only needs to store the last p wavefronts. Thus, the memory use is proportional to the optimal alignment score, O(s), excluding the storage of the input sequences."
- Does NOT transfer: the O(s) memory depends on wavefront width O(s) and a constant window p. For us, weights are unbounded subtree sizes, so p is as large as the largest subtree (the window covers a whole row). The meet-in-the-middle itself (forward cost + reverse cost over the same cell) does transfer in principle; the small window does not. Also BiWFA's memory excludes the input; ours needs the memo of recursive pair costs, which is not reducible by this technique (measured in results/frontier).
