# GumTree, RefactoringMiner: mapping accuracy on OmniDiff's ground truth

Pinned: GumTree commit f0e38db (core 4.2.0-SNAPSHOT), 17 matchers, JDT Java generator; RefactoringMiner 3.1.6
(`diffAtFileContents` on a one-file project). DiffBenchmark was cloned and built but its experiments were NOT run.

Method: each tool's node mapping is converted by byte range onto the scorer's tree-sitter preorder numbering
(`tools/gumtree_eval/gt2map`) and scored by `score_accuracy` against the hand-authored `human_mapping.json`.
Two scorings exist. `raw` scores every tree-sitter node, so a JDT-based tool is charged for nodes its own tree
does not contain (pair recall about 0.48, perfect fixtures 0%). `scoped` scores only the nodes the tool itself
represents. The table uses `scoped`, which is lenient to the JDT tools and not to difffold or OmniDiff, which
are scored on all tree-sitter nodes. Treat the comparison as indicative, not like for like.

200 small Java fixtures (before-files median 4 KB, max 19 KB; all runs ok, no timeouts), micro-averaged:

| tool | perfect fixtures | near-perfect | pair F1 | changed-span F1 | median match time |
|---|---|---|---|---|---|
| OmniDiff | 83.0% | 93.5% | 0.999 | 0.986 | n/a here |
| RefactoringMiner 3.1.6 | 80.5% | 94.0% | 0.998 | 0.975 | 40.5 ms |
| GumTree gumtree-hybrid-id (best) | 73.5% | 92.0% | 0.997 | 0.967 | 0.4 ms |
| GumTree gumtree-simple (default) | 70.5% | 90.5% | 0.997 | 0.961 | 0.3 ms |
| difffold general TED | 59.0% | 85.0% | 0.996 | 0.968 | see TED lane |
| difffold top-down | 48.0% | 70.0% | 0.990 | 0.890 | see Selkow lane |

Over all 450 or so Java fixtures GumTree matchers scored 72.8% to 74.3% perfect for the ten best matchers
(`gumtree-classic-theta` 74.3%), 54.6% for `longestCommonSequence`, 32.3% for `xy`; the fixture count differs
per matcher (452 to 483) because some fixtures fail on the JDT parse. Files: `results/accuracy/gumtree/`.

Reading: the established tools are ahead of difffold on correspondence quality for Java. The general-TED
mapping is competitive in changed-span F1 with GumTree (0.968 against 0.961 to 0.967) but not in perfect
fixtures, where moves and reorders matter. GumTree is also far faster per match (sub-millisecond), though that
excludes parsing; difffold's timing is in the TED lane.
