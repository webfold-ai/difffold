## Fixtures scored: 998 (unscorable: 763)

### All scorable fixtures

Micro (sums over fixtures):

| lang | tool | fixtures | node-corr. accuracy | pair P | pair R | pair F1 | span P | span R | span F1 | perfect | near-perfect | strict perfect |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| c | difffold | 88 | 0.997 | 0.998 | 0.998 | 0.998 | 0.632 | 0.937 | 0.755 | 65.9% | 89.8% | 65.9% |
| c | omnidiff | 88 | 0.998 | 0.999 | 0.999 | 0.999 | 0.854 | 0.918 | 0.885 | 79.5% | 97.7% | 77.3% |
| go | difffold | 79 | 0.996 | 0.998 | 0.998 | 0.998 | 0.846 | 0.997 | 0.915 | 63.3% | 84.8% | 63.3% |
| go | omnidiff | 79 | 0.999 | 1.000 | 1.000 | 1.000 | 0.952 | 0.981 | 0.966 | 78.5% | 96.2% | 78.5% |
| java | difffold | 515 | 0.996 | 0.998 | 0.997 | 0.998 | 0.709 | 0.983 | 0.824 | 48.2% | 86.0% | 48.0% |
| java | omnidiff | 515 | 0.999 | 1.000 | 1.000 | 1.000 | 0.971 | 0.985 | 0.978 | 83.9% | 97.3% | 80.4% |
| javascript | difffold | 50 | 0.997 | 0.999 | 0.998 | 0.999 | 0.688 | 0.991 | 0.812 | 64.0% | 72.0% | 62.0% |
| javascript | omnidiff | 50 | 0.999 | 1.000 | 1.000 | 1.000 | 0.942 | 1.000 | 0.970 | 84.0% | 92.0% | 82.0% |
| python | difffold | 71 | 0.995 | 0.998 | 0.998 | 0.998 | 0.809 | 0.947 | 0.873 | 71.8% | 88.7% | 71.8% |
| python | omnidiff | 71 | 1.000 | 1.000 | 1.000 | 1.000 | 0.983 | 0.996 | 0.990 | 84.5% | 98.6% | 84.5% |
| rust | difffold | 111 | 0.995 | 0.998 | 0.997 | 0.998 | 0.760 | 0.989 | 0.860 | 55.9% | 81.1% | 55.9% |
| rust | omnidiff | 111 | 0.999 | 1.000 | 1.000 | 1.000 | 0.977 | 0.991 | 0.984 | 73.9% | 91.9% | 73.9% |
| tsx | difffold | 41 | 0.995 | 0.998 | 0.997 | 0.998 | 0.715 | 0.986 | 0.829 | 68.3% | 82.9% | 68.3% |
| tsx | omnidiff | 41 | 0.999 | 1.000 | 0.999 | 1.000 | 0.943 | 1.000 | 0.970 | 73.2% | 92.7% | 73.2% |
| typescript | difffold | 43 | 0.999 | 1.000 | 0.999 | 0.999 | 0.876 | 1.000 | 0.934 | 88.4% | 93.0% | 88.4% |
| typescript | omnidiff | 43 | 1.000 | 1.000 | 1.000 | 1.000 | 0.995 | 1.000 | 0.997 | 95.3% | 100.0% | 93.0% |
| ALL | difffold | 998 | 0.996 | 0.998 | 0.997 | 0.998 | 0.741 | 0.980 | 0.844 | 56.8% | 85.4% | 56.6% |
| ALL | omnidiff | 998 | 0.999 | 1.000 | 1.000 | 1.000 | 0.962 | 0.984 | 0.973 | 82.1% | 96.4% | 79.9% |

Macro (mean of per-fixture values):

| lang | tool | accuracy | pair P | pair R | pair F1 | span P | span R | span F1 |
|---|---|---|---|---|---|---|---|---|
| c | difffold | 0.978 | 0.967 | 0.970 | 0.967 | 0.867 | 0.980 | 0.896 |
| c | omnidiff | 0.993 | 0.991 | 0.987 | 0.988 | 0.968 | 0.984 | 0.972 |
| go | difffold | 0.984 | 0.990 | 0.985 | 0.987 | 0.884 | 0.994 | 0.911 |
| go | omnidiff | 0.996 | 0.999 | 0.999 | 0.999 | 0.978 | 0.992 | 0.981 |
| java | difffold | 0.986 | 0.993 | 0.991 | 0.992 | 0.838 | 0.984 | 0.872 |
| java | omnidiff | 0.998 | 0.999 | 0.999 | 0.999 | 0.987 | 0.992 | 0.989 |
| javascript | difffold | 0.934 | 0.962 | 0.954 | 0.955 | 0.865 | 0.996 | 0.895 |
| javascript | omnidiff | 0.991 | 0.997 | 0.994 | 0.996 | 0.972 | 1.000 | 0.982 |
| python | difffold | 0.983 | 0.989 | 0.986 | 0.987 | 0.895 | 0.994 | 0.916 |
| python | omnidiff | 0.999 | 1.000 | 1.000 | 1.000 | 0.983 | 0.992 | 0.986 |
| rust | difffold | 0.967 | 0.981 | 0.973 | 0.976 | 0.861 | 0.984 | 0.888 |
| rust | omnidiff | 0.992 | 0.997 | 0.995 | 0.996 | 0.988 | 0.997 | 0.992 |
| tsx | difffold | 0.983 | 0.990 | 0.988 | 0.989 | 0.871 | 0.999 | 0.898 |
| tsx | omnidiff | 0.983 | 0.986 | 0.984 | 0.985 | 0.968 | 1.000 | 0.975 |
| typescript | difffold | 0.982 | 0.982 | 0.977 | 0.979 | 0.952 | 1.000 | 0.963 |
| typescript | omnidiff | 0.999 | 1.000 | 0.999 | 0.999 | 0.991 | 1.000 | 0.994 |
| ALL | difffold | 0.980 | 0.987 | 0.984 | 0.985 | 0.859 | 0.987 | 0.888 |
| ALL | omnidiff | 0.996 | 0.998 | 0.997 | 0.997 | 0.983 | 0.993 | 0.986 |

### Excluding wholesale-rewrite fixtures

Micro (sums over fixtures):

| lang | tool | fixtures | node-corr. accuracy | pair P | pair R | pair F1 | span P | span R | span F1 | perfect | near-perfect | strict perfect |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| c | difffold | 86 | 0.997 | 0.999 | 0.998 | 0.998 | 0.614 | 0.940 | 0.743 | 67.4% | 90.7% | 67.4% |
| c | omnidiff | 86 | 0.998 | 0.999 | 0.999 | 0.999 | 0.848 | 0.928 | 0.886 | 81.4% | 98.8% | 79.1% |
| go | difffold | 79 | 0.996 | 0.998 | 0.998 | 0.998 | 0.846 | 0.997 | 0.915 | 63.3% | 84.8% | 63.3% |
| go | omnidiff | 79 | 0.999 | 1.000 | 1.000 | 1.000 | 0.952 | 0.981 | 0.966 | 78.5% | 96.2% | 78.5% |
| java | difffold | 514 | 0.996 | 0.998 | 0.997 | 0.998 | 0.702 | 0.982 | 0.819 | 48.1% | 86.0% | 47.9% |
| java | omnidiff | 514 | 0.999 | 1.000 | 1.000 | 1.000 | 0.970 | 0.985 | 0.977 | 83.9% | 97.3% | 80.4% |
| javascript | difffold | 50 | 0.997 | 0.999 | 0.998 | 0.999 | 0.688 | 0.991 | 0.812 | 64.0% | 72.0% | 62.0% |
| javascript | omnidiff | 50 | 0.999 | 1.000 | 1.000 | 1.000 | 0.942 | 1.000 | 0.970 | 84.0% | 92.0% | 82.0% |
| python | difffold | 71 | 0.995 | 0.998 | 0.998 | 0.998 | 0.809 | 0.947 | 0.873 | 71.8% | 88.7% | 71.8% |
| python | omnidiff | 71 | 1.000 | 1.000 | 1.000 | 1.000 | 0.983 | 0.996 | 0.990 | 84.5% | 98.6% | 84.5% |
| rust | difffold | 110 | 0.995 | 0.998 | 0.997 | 0.997 | 0.759 | 0.990 | 0.859 | 56.4% | 80.9% | 56.4% |
| rust | omnidiff | 110 | 0.999 | 1.000 | 1.000 | 1.000 | 0.977 | 0.991 | 0.984 | 74.5% | 91.8% | 74.5% |
| tsx | difffold | 41 | 0.995 | 0.998 | 0.997 | 0.998 | 0.715 | 0.986 | 0.829 | 68.3% | 82.9% | 68.3% |
| tsx | omnidiff | 41 | 0.999 | 1.000 | 0.999 | 1.000 | 0.943 | 1.000 | 0.970 | 73.2% | 92.7% | 73.2% |
| typescript | difffold | 43 | 0.999 | 1.000 | 0.999 | 0.999 | 0.876 | 1.000 | 0.934 | 88.4% | 93.0% | 88.4% |
| typescript | omnidiff | 43 | 1.000 | 1.000 | 1.000 | 1.000 | 0.995 | 1.000 | 0.997 | 95.3% | 100.0% | 93.0% |
| ALL | difffold | 994 | 0.996 | 0.999 | 0.997 | 0.998 | 0.737 | 0.980 | 0.841 | 56.9% | 85.4% | 56.7% |
| ALL | omnidiff | 994 | 0.999 | 1.000 | 1.000 | 1.000 | 0.962 | 0.984 | 0.973 | 82.3% | 96.5% | 80.1% |

Macro (mean of per-fixture values):

| lang | tool | accuracy | pair P | pair R | pair F1 | span P | span R | span F1 |
|---|---|---|---|---|---|---|---|---|
| c | difffold | 0.986 | 0.987 | 0.983 | 0.985 | 0.865 | 0.981 | 0.894 |
| c | omnidiff | 0.997 | 0.999 | 0.998 | 0.998 | 0.968 | 0.986 | 0.973 |
| go | difffold | 0.984 | 0.990 | 0.985 | 0.987 | 0.884 | 0.994 | 0.911 |
| go | omnidiff | 0.996 | 0.999 | 0.999 | 0.999 | 0.978 | 0.992 | 0.981 |
| java | difffold | 0.986 | 0.993 | 0.991 | 0.992 | 0.838 | 0.984 | 0.871 |
| java | omnidiff | 0.998 | 0.999 | 0.999 | 0.999 | 0.987 | 0.992 | 0.989 |
| javascript | difffold | 0.934 | 0.962 | 0.954 | 0.955 | 0.865 | 0.996 | 0.895 |
| javascript | omnidiff | 0.991 | 0.997 | 0.994 | 0.996 | 0.972 | 1.000 | 0.982 |
| python | difffold | 0.983 | 0.989 | 0.986 | 0.987 | 0.895 | 0.994 | 0.916 |
| python | omnidiff | 0.999 | 1.000 | 1.000 | 1.000 | 0.983 | 0.992 | 0.986 |
| rust | difffold | 0.967 | 0.980 | 0.972 | 0.976 | 0.860 | 0.984 | 0.887 |
| rust | omnidiff | 0.992 | 0.997 | 0.995 | 0.996 | 0.988 | 0.997 | 0.992 |
| tsx | difffold | 0.983 | 0.990 | 0.988 | 0.989 | 0.871 | 0.999 | 0.898 |
| tsx | omnidiff | 0.983 | 0.986 | 0.984 | 0.985 | 0.968 | 1.000 | 0.975 |
| typescript | difffold | 0.982 | 0.982 | 0.977 | 0.979 | 0.952 | 1.000 | 0.963 |
| typescript | omnidiff | 0.999 | 1.000 | 0.999 | 0.999 | 0.991 | 1.000 | 0.994 |
| ALL | difffold | 0.981 | 0.988 | 0.985 | 0.986 | 0.858 | 0.987 | 0.888 |
| ALL | omnidiff | 0.996 | 0.998 | 0.998 | 0.998 | 0.983 | 0.993 | 0.986 |

### Unscorable fixtures by reason (full list: unscorable.csv)

| reason | fixtures |
|---|---|
| ground truth | 3 |
| ground truth has no pairs | 2 |
| language not parsed here: .BUILD | 1 |
| language not parsed here: .R | 1 |
| language not parsed here: .bash | 1 |
| language not parsed here: .cc | 8 |
| language not parsed here: .cpp | 71 |
| language not parsed here: .cs | 81 |
| language not parsed here: .css | 38 |
| language not parsed here: .cxx | 7 |
| language not parsed here: .hpp | 6 |
| language not parsed here: .html | 57 |
| language not parsed here: .hxx | 3 |
| language not parsed here: .json | 52 |
| language not parsed here: .kt | 58 |
| language not parsed here: .lua | 40 |
| language not parsed here: .php | 46 |
| language not parsed here: .r | 3 |
| language not parsed here: .rb | 43 |
| language not parsed here: .scala | 20 |
| language not parsed here: .scss | 6 |
| language not parsed here: .sh | 54 |
| language not parsed here: .sql | 12 |
| language not parsed here: .swift | 41 |
| language not parsed here: .vim | 33 |
| language not parsed here: .xml | 39 |
| language not parsed here: .yaml | 9 |
| language not parsed here: .yml | 28 |

### Ground-truth composition and the top-down ceiling

| lang | fixtures | GT pairs | identical pairs | changed pairs | GT deleted nodes | GT inserted nodes | cross-parent move roots | wrap/unwrap roots | reorder pairs | top-down ceiling (pair recall) | fixtures at ceiling 100% |
|---|---|---|---|---|---|---|---|---|---|---|---|
| c | 88 | 674563 | 673505 | 1058 | 1134 | 2041 | 10 | 118 | 43 | 0.998 | 68.2% |
| go | 79 | 474619 | 473668 | 951 | 956 | 5710 | 10 | 119 | 6 | 0.998 | 69.6% |
| java | 515 | 2376713 | 2371527 | 5186 | 4390 | 18728 | 71 | 634 | 36 | 0.997 | 55.0% |
| javascript | 50 | 205978 | 205668 | 310 | 334 | 882 | 1 | 50 | 2 | 0.998 | 66.0% |
| python | 71 | 179961 | 179002 | 959 | 996 | 2675 | 4 | 60 | 1 | 0.998 | 71.8% |
| rust | 111 | 850907 | 849242 | 1665 | 4372 | 10418 | 28 | 244 | 15 | 0.997 | 62.2% |
| tsx | 41 | 117757 | 117215 | 542 | 241 | 1031 | 0 | 65 | 5 | 0.997 | 68.3% |
| typescript | 43 | 168501 | 168295 | 206 | 46 | 1333 | 3 | 11 | 0 | 0.999 | 88.4% |
| ALL | 998 | 5048999 | 5038122 | 10877 | 12469 | 42818 | 127 | 1301 | 108 | 0.998 | 61.8% |

### Failures by root-cause class (decisions: pair, delete, insert and group-member checks)

Fixture-level attribution: a fixture flagged wholesale rewrite counts all its decisions there; otherwise a failed decision is charged to the class of its root cause (see definitions).

| class | fixtures containing | decisions | difffold fails | omnidiff fails | difffold acc | omnidiff acc | gap (fails) | share of gap | perfect fixtures difffold | perfect fixtures omnidiff |
|---|---|---|---|---|---|---|---|---|---|---|
| local_edit | 278 | 559 | 33 | 46 | 0.941 | 0.918 | -13 | 0.0% | 72.7% | 80.9% |
| sibling_ins_del | 659 | 42186 | 2688 | 1185 | 0.936 | 0.972 | 1503 | 9.9% | 57.4% | 77.8% |
| repeated_children | 230 | 3413 | 1292 | 910 | 0.621 | 0.733 | 382 | 2.5% | 32.6% | 57.0% |
| reorder | 38 | 1044 | 1009 | 99 | 0.034 | 0.905 | 910 | 6.0% | 0.0% | 55.3% |
| cross_parent_move | 56 | 1101 | 896 | 210 | 0.186 | 0.809 | 686 | 4.5% | 0.0% | 17.9% |
| wrap_unwrap | 333 | 20845 | 12491 | 1112 | 0.401 | 0.947 | 11379 | 75.2% | 0.3% | 58.9% |
| wholesale_rewrite | 4 | 3983 | 190 | 128 | 0.952 | 0.968 | 62 | 0.4% | 25.0% | 25.0% |
| context | 994 | 5033129 | 1238 | 1006 | 1.000 | 1.000 | 232 | 1.5% | 56.9% | 82.3% |

Fixtures containing any wrap/unwrap: 334/998 (33.5%); any cross-parent move: 57/998 (5.7%); any reorder: 38/998 (3.8%).
Fixtures where difffold has more visible mismatches than OmniDiff: 387/998 (38.8%); of those, 302 contain a wrap/unwrap.

Primary cause of the gap in the fixtures where difffold is worse (class with the largest excess of failed decisions):

| class | fixtures | excess failed decisions |
|---|---|---|
| context | 16 | 219 |
| cross_parent_move | 13 | 385 |
| reorder | 17 | 848 |
| repeated_children | 14 | 83 |
| sibling_ins_del | 51 | 766 |
| wholesale_rewrite | 2 | 88 |
| wrap_unwrap | 274 | 10812 |

Fixtures where OmniDiff is perfect and difffold is not: 258 (25.9% of all). Classes present in them:

- local_edit: 28
- sibling_ins_del: 139
- repeated_children: 58
- reorder: 21
- cross_parent_move: 10
- wrap_unwrap: 195
- wholesale_rewrite: 0
- context: 258
- none of move, wrap/unwrap, reorder, repeated, rewrite: 33

### 10 worst fixtures for difffold (visible mismatches minus OmniDiff's)

| fixture | lang | difffold vis. mismatches | omnidiff | decisions | difffold excess fails by cause |
|---|---|---|---|---|---|
| handmade/rust-next-font-imports-generator | rust | 726 | 0 | 2397 | context:+5 reorder:+2 wrap_unwrap:+1077 |
| full/java-pdftk-java-pdftk-real-change-all-across-the-file | java | 861 | 233 | 4937 | context:+99 cross_parent_move:+26 local_edit:-5 reorder:+396 repeated_children:+7 sibling_ins_del:+76 wrap_unwrap:+373 |
| defects4j/java-defects4j-chart-25-statisticalbarrenderer | java | 476 | 18 | 3200 | cross_parent_move:+20 wrap_unwrap:+624 |
| full/python-aboutcode-org-license-expression-excellent-test-case | python | 243 | 7 | 13686 | context:+74 cross_parent_move:+4 reorder:+4 repeated_children:+15 sibling_ins_del:+187 wrap_unwrap:+38 |
| defects4j/java-defects4j-closure-137-makedeclarednamesunique | java | 325 | 115 | 3630 | context:+27 cross_parent_move:+1 sibling_ins_del:+61 wrap_unwrap:+246 |
| defects4j/java-defects4j-chart-21-defaultboxandwhiskercategorydataset | java | 182 | 0 | 3131 | context:-1 wrap_unwrap:+272 |
| full/c-sched-ext-scx-many-many-moves-some-deletes-some-adds | c | 180 | 3 | 2590 | context:+103 local_edit:-1 reorder:+122 sibling_ins_del:+16 |
| stratified/go-jesseduffield-lazygit-many-multi-maps-very-difficult | go | 231 | 55 | 717 | repeated_children:+30 sibling_ins_del:+24 wrap_unwrap:+186 |
| handmade/rust-turbopack-module-rule | rust | 214 | 43 | 2134 | cross_parent_move:+111 sibling_ins_del:+6 wrap_unwrap:+176 |
| small/rust-rustdesk-rustdesk-large-file-40k-normal-feature-work | rust | 162 | 2 | 46183 | repeated_children:+49 sibling_ins_del:+18 wrap_unwrap:+198 |

### Calibration of this scorer against OmniDiff's own checker

On 998 fixtures with a native result: OmniDiff native visible mismatches total 3251, this scorer's 3251; zero/non-zero agreement 100.0%. The scorer ignores operation kinds (Identical vs Update) and the subtree-closure step of groups; the native checker enforces both.
