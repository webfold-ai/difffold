## Fixtures scored: 505 (unscorable: 382)

### All scorable fixtures

Micro (sums over fixtures):

| lang | tool | fixtures | node-corr. accuracy | pair P | pair R | pair F1 | span P | span R | span F1 | perfect | near-perfect | strict perfect |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| c | difffold | 37 | 0.999 | 1.000 | 1.000 | 1.000 | 0.966 | 0.937 | 0.951 | 70.3% | 97.3% | 67.6% |
| c | omnidiff | 37 | 0.999 | 1.000 | 1.000 | 1.000 | 0.867 | 0.970 | 0.916 | 75.7% | 100.0% | 70.3% |
| go | difffold | 35 | 0.998 | 0.999 | 1.000 | 0.999 | 0.987 | 0.989 | 0.988 | 60.0% | 97.1% | 60.0% |
| go | omnidiff | 35 | 0.998 | 0.999 | 0.999 | 0.999 | 0.872 | 0.994 | 0.929 | 65.7% | 91.4% | 65.7% |
| java | difffold | 267 | 0.998 | 0.999 | 1.000 | 0.999 | 0.971 | 0.944 | 0.957 | 78.3% | 93.3% | 74.2% |
| java | omnidiff | 267 | 0.999 | 1.000 | 1.000 | 1.000 | 0.966 | 0.985 | 0.975 | 84.3% | 96.6% | 81.3% |
| javascript | difffold | 23 | 1.000 | 1.000 | 1.000 | 1.000 | 0.972 | 0.986 | 0.979 | 78.3% | 87.0% | 78.3% |
| javascript | omnidiff | 23 | 1.000 | 1.000 | 1.000 | 1.000 | 0.946 | 1.000 | 0.972 | 82.6% | 95.7% | 82.6% |
| python | difffold | 38 | 0.997 | 0.999 | 1.000 | 0.999 | 0.992 | 0.929 | 0.959 | 86.8% | 94.7% | 84.2% |
| python | omnidiff | 38 | 1.000 | 1.000 | 1.000 | 1.000 | 0.998 | 0.998 | 0.998 | 89.5% | 100.0% | 89.5% |
| rust | difffold | 55 | 0.998 | 0.999 | 0.999 | 0.999 | 0.983 | 0.963 | 0.973 | 60.0% | 81.8% | 60.0% |
| rust | omnidiff | 55 | 0.999 | 1.000 | 0.999 | 1.000 | 0.971 | 0.991 | 0.981 | 67.3% | 87.3% | 67.3% |
| tsx | difffold | 20 | 0.999 | 1.000 | 1.000 | 1.000 | 0.965 | 0.980 | 0.973 | 80.0% | 90.0% | 80.0% |
| tsx | omnidiff | 20 | 0.999 | 1.000 | 1.000 | 1.000 | 0.948 | 1.000 | 0.973 | 75.0% | 95.0% | 75.0% |
| typescript | difffold | 30 | 0.999 | 0.999 | 0.999 | 0.999 | 0.987 | 0.987 | 0.987 | 86.7% | 93.3% | 86.7% |
| typescript | omnidiff | 30 | 1.000 | 1.000 | 1.000 | 1.000 | 0.993 | 1.000 | 0.997 | 93.3% | 100.0% | 90.0% |
| ALL | difffold | 505 | 0.998 | 0.999 | 1.000 | 0.999 | 0.978 | 0.954 | 0.966 | 75.6% | 92.3% | 73.1% |
| ALL | omnidiff | 505 | 0.999 | 1.000 | 1.000 | 1.000 | 0.960 | 0.989 | 0.974 | 81.0% | 95.8% | 78.8% |

Macro (mean of per-fixture values):

| lang | tool | accuracy | pair P | pair R | pair F1 | span P | span R | span F1 |
|---|---|---|---|---|---|---|---|---|
| c | difffold | 0.997 | 1.000 | 0.984 | 0.989 | 0.985 | 0.986 | 0.983 |
| c | omnidiff | 0.999 | 1.000 | 0.986 | 0.991 | 0.964 | 0.992 | 0.972 |
| go | difffold | 0.991 | 0.995 | 0.994 | 0.995 | 0.991 | 0.992 | 0.991 |
| go | omnidiff | 0.992 | 0.997 | 0.997 | 0.997 | 0.963 | 0.995 | 0.971 |
| java | difffold | 0.996 | 0.998 | 0.999 | 0.998 | 0.994 | 0.991 | 0.992 |
| java | omnidiff | 0.998 | 0.999 | 0.999 | 0.999 | 0.989 | 0.995 | 0.992 |
| javascript | difffold | 0.992 | 0.994 | 0.991 | 0.992 | 0.984 | 0.993 | 0.988 |
| javascript | omnidiff | 0.996 | 1.000 | 0.995 | 0.997 | 0.981 | 1.000 | 0.989 |
| python | difffold | 0.997 | 0.998 | 0.998 | 0.998 | 0.993 | 0.995 | 0.994 |
| python | omnidiff | 1.000 | 1.000 | 1.000 | 1.000 | 0.995 | 1.000 | 0.997 |
| rust | difffold | 0.988 | 0.995 | 0.997 | 0.996 | 0.983 | 0.989 | 0.985 |
| rust | omnidiff | 0.991 | 0.998 | 0.996 | 0.997 | 0.982 | 0.994 | 0.988 |
| tsx | difffold | 0.997 | 0.999 | 0.998 | 0.999 | 0.997 | 0.998 | 0.997 |
| tsx | omnidiff | 0.998 | 0.999 | 0.999 | 0.999 | 0.979 | 1.000 | 0.988 |
| typescript | difffold | 0.990 | 0.992 | 0.988 | 0.990 | 0.983 | 0.994 | 0.987 |
| typescript | omnidiff | 0.999 | 1.000 | 0.999 | 0.999 | 0.987 | 1.000 | 0.992 |
| ALL | difffold | 0.994 | 0.997 | 0.996 | 0.996 | 0.991 | 0.991 | 0.990 |
| ALL | omnidiff | 0.997 | 0.999 | 0.998 | 0.998 | 0.984 | 0.996 | 0.988 |

### Excluding wholesale-rewrite fixtures

Micro (sums over fixtures):

| lang | tool | fixtures | node-corr. accuracy | pair P | pair R | pair F1 | span P | span R | span F1 | perfect | near-perfect | strict perfect |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| c | difffold | 36 | 0.999 | 1.000 | 1.000 | 1.000 | 0.964 | 0.934 | 0.949 | 72.2% | 97.2% | 69.4% |
| c | omnidiff | 36 | 0.999 | 1.000 | 1.000 | 1.000 | 0.863 | 0.969 | 0.913 | 77.8% | 100.0% | 72.2% |
| go | difffold | 35 | 0.998 | 0.999 | 1.000 | 0.999 | 0.987 | 0.989 | 0.988 | 60.0% | 97.1% | 60.0% |
| go | omnidiff | 35 | 0.998 | 0.999 | 0.999 | 0.999 | 0.872 | 0.994 | 0.929 | 65.7% | 91.4% | 65.7% |
| java | difffold | 266 | 0.998 | 0.999 | 1.000 | 0.999 | 0.969 | 0.941 | 0.955 | 78.2% | 93.2% | 74.4% |
| java | omnidiff | 266 | 0.999 | 1.000 | 1.000 | 1.000 | 0.964 | 0.984 | 0.974 | 84.2% | 96.6% | 81.2% |
| javascript | difffold | 23 | 1.000 | 1.000 | 1.000 | 1.000 | 0.972 | 0.986 | 0.979 | 78.3% | 87.0% | 78.3% |
| javascript | omnidiff | 23 | 1.000 | 1.000 | 1.000 | 1.000 | 0.946 | 1.000 | 0.972 | 82.6% | 95.7% | 82.6% |
| python | difffold | 38 | 0.997 | 0.999 | 1.000 | 0.999 | 0.992 | 0.929 | 0.959 | 86.8% | 94.7% | 84.2% |
| python | omnidiff | 38 | 1.000 | 1.000 | 1.000 | 1.000 | 0.998 | 0.998 | 0.998 | 89.5% | 100.0% | 89.5% |
| rust | difffold | 55 | 0.998 | 0.999 | 0.999 | 0.999 | 0.983 | 0.963 | 0.973 | 60.0% | 81.8% | 60.0% |
| rust | omnidiff | 55 | 0.999 | 1.000 | 0.999 | 1.000 | 0.971 | 0.991 | 0.981 | 67.3% | 87.3% | 67.3% |
| tsx | difffold | 20 | 0.999 | 1.000 | 1.000 | 1.000 | 0.965 | 0.980 | 0.973 | 80.0% | 90.0% | 80.0% |
| tsx | omnidiff | 20 | 0.999 | 1.000 | 1.000 | 1.000 | 0.948 | 1.000 | 0.973 | 75.0% | 95.0% | 75.0% |
| typescript | difffold | 30 | 0.999 | 0.999 | 0.999 | 0.999 | 0.987 | 0.987 | 0.987 | 86.7% | 93.3% | 86.7% |
| typescript | omnidiff | 30 | 1.000 | 1.000 | 1.000 | 1.000 | 0.993 | 1.000 | 0.997 | 93.3% | 100.0% | 90.0% |
| ALL | difffold | 503 | 0.998 | 0.999 | 1.000 | 0.999 | 0.977 | 0.953 | 0.965 | 75.7% | 92.2% | 73.4% |
| ALL | omnidiff | 503 | 0.999 | 1.000 | 1.000 | 1.000 | 0.958 | 0.989 | 0.973 | 81.1% | 95.8% | 78.9% |

Macro (mean of per-fixture values):

| lang | tool | accuracy | pair P | pair R | pair F1 | span P | span R | span F1 |
|---|---|---|---|---|---|---|---|---|
| c | difffold | 0.997 | 1.000 | 0.997 | 0.998 | 0.985 | 0.985 | 0.983 |
| c | omnidiff | 0.999 | 1.000 | 0.999 | 1.000 | 0.963 | 0.992 | 0.971 |
| go | difffold | 0.991 | 0.995 | 0.994 | 0.995 | 0.991 | 0.992 | 0.991 |
| go | omnidiff | 0.992 | 0.997 | 0.997 | 0.997 | 0.963 | 0.995 | 0.971 |
| java | difffold | 0.996 | 0.998 | 0.999 | 0.998 | 0.994 | 0.991 | 0.992 |
| java | omnidiff | 0.998 | 0.999 | 0.999 | 0.999 | 0.989 | 0.995 | 0.992 |
| javascript | difffold | 0.992 | 0.994 | 0.991 | 0.992 | 0.984 | 0.993 | 0.988 |
| javascript | omnidiff | 0.996 | 1.000 | 0.995 | 0.997 | 0.981 | 1.000 | 0.989 |
| python | difffold | 0.997 | 0.998 | 0.998 | 0.998 | 0.993 | 0.995 | 0.994 |
| python | omnidiff | 1.000 | 1.000 | 1.000 | 1.000 | 0.995 | 1.000 | 0.997 |
| rust | difffold | 0.988 | 0.995 | 0.997 | 0.996 | 0.983 | 0.989 | 0.985 |
| rust | omnidiff | 0.991 | 0.998 | 0.996 | 0.997 | 0.982 | 0.994 | 0.988 |
| tsx | difffold | 0.997 | 0.999 | 0.998 | 0.999 | 0.997 | 0.998 | 0.997 |
| tsx | omnidiff | 0.998 | 0.999 | 0.999 | 0.999 | 0.979 | 1.000 | 0.988 |
| typescript | difffold | 0.990 | 0.992 | 0.988 | 0.990 | 0.983 | 0.994 | 0.987 |
| typescript | omnidiff | 0.999 | 1.000 | 0.999 | 0.999 | 0.987 | 1.000 | 0.992 |
| ALL | difffold | 0.994 | 0.997 | 0.997 | 0.997 | 0.991 | 0.991 | 0.990 |
| ALL | omnidiff | 0.997 | 0.999 | 0.999 | 0.999 | 0.984 | 0.996 | 0.988 |

### Unscorable fixtures by reason (full list: unscorable.csv)

| reason | fixtures |
|---|---|
| ground truth | 2 |
| language not parsed here: .BUILD | 1 |
| language not parsed here: .cc | 5 |
| language not parsed here: .cpp | 26 |
| language not parsed here: .cs | 37 |
| language not parsed here: .css | 14 |
| language not parsed here: .cxx | 4 |
| language not parsed here: .hpp | 1 |
| language not parsed here: .html | 32 |
| language not parsed here: .hxx | 2 |
| language not parsed here: .json | 29 |
| language not parsed here: .kt | 27 |
| language not parsed here: .lua | 14 |
| language not parsed here: .php | 26 |
| language not parsed here: .r | 2 |
| language not parsed here: .rb | 19 |
| language not parsed here: .scala | 12 |
| language not parsed here: .scss | 4 |
| language not parsed here: .sh | 32 |
| language not parsed here: .sql | 8 |
| language not parsed here: .swift | 21 |
| language not parsed here: .vim | 20 |
| language not parsed here: .xml | 21 |
| language not parsed here: .yaml | 5 |
| language not parsed here: .yml | 18 |

### Ground-truth composition and the top-down ceiling

| lang | fixtures | GT pairs | identical pairs | changed pairs | GT deleted nodes | GT inserted nodes | cross-parent move roots | wrap/unwrap roots | reorder pairs | top-down ceiling (pair recall) | fixtures at ceiling 100% |
|---|---|---|---|---|---|---|---|---|---|---|---|
| c | 37 | 314521 | 314110 | 411 | 153 | 501 | 8 | 55 | 8 | 0.999 | 54.1% |
| go | 35 | 221727 | 221294 | 433 | 664 | 1483 | 1 | 82 | 5 | 0.997 | 62.9% |
| java | 267 | 1182218 | 1179314 | 2904 | 2244 | 10936 | 40 | 365 | 27 | 0.997 | 55.4% |
| javascript | 23 | 155183 | 155056 | 127 | 120 | 727 | 1 | 29 | 0 | 0.998 | 69.6% |
| python | 38 | 65551 | 65094 | 457 | 553 | 1446 | 1 | 27 | 0 | 0.997 | 76.3% |
| rust | 55 | 443049 | 442121 | 928 | 2053 | 6562 | 19 | 169 | 7 | 0.997 | 54.5% |
| tsx | 20 | 91435 | 91108 | 327 | 157 | 753 | 0 | 40 | 2 | 0.998 | 75.0% |
| typescript | 30 | 34074 | 33926 | 148 | 38 | 1054 | 3 | 11 | 0 | 0.996 | 83.3% |
| ALL | 505 | 2507758 | 2502023 | 5735 | 5982 | 23462 | 73 | 778 | 49 | 0.997 | 60.4% |

### Failures by root-cause class (decisions: pair, delete, insert and group-member checks)

Fixture-level attribution: a fixture flagged wholesale rewrite counts all its decisions there; otherwise a failed decision is charged to the class of its root cause (see definitions).

| class | fixtures containing | decisions | difffold fails | omnidiff fails | difffold acc | omnidiff acc | gap (fails) | share of gap | perfect fixtures difffold | perfect fixtures omnidiff |
|---|---|---|---|---|---|---|---|---|---|---|
| local_edit | 126 | 239 | 20 | 27 | 0.916 | 0.887 | -7 | 0.0% | 77.0% | 79.4% |
| sibling_ins_del | 344 | 22229 | 1386 | 520 | 0.938 | 0.977 | 866 | 55.4% | 73.3% | 76.7% |
| repeated_children | 112 | 1643 | 576 | 333 | 0.649 | 0.797 | 243 | 15.5% | 49.1% | 54.5% |
| reorder | 20 | 662 | 138 | 72 | 0.792 | 0.891 | 66 | 4.2% | 30.0% | 50.0% |
| cross_parent_move | 31 | 772 | 112 | 134 | 0.855 | 0.826 | -22 | 0.0% | 22.6% | 16.1% |
| wrap_unwrap | 176 | 11755 | 1253 | 704 | 0.893 | 0.940 | 549 | 35.1% | 48.3% | 59.1% |
| wholesale_rewrite | 2 | 861 | 3 | 1 | 0.997 | 0.999 | 2 | 0.1% | 50.0% | 50.0% |
| context | 503 | 2500191 | 320 | 454 | 1.000 | 1.000 | -134 | 0.0% | 75.7% | 81.1% |

### Pair recall by root-cause class (ground-truth pairs only)

| class | ground-truth pairs | difffold pairs correct | omnidiff pairs correct | difffold recall | omnidiff recall |
|---|---|---|---|---|---|
| local_edit | 239 | 219 | 212 | 0.916 | 0.887 |
| sibling_ins_del | 0 | 0 | 0 | 0.000 | 0.000 |
| repeated_children | 0 | 0 | 0 | 0.000 | 0.000 |
| reorder | 662 | 524 | 590 | 0.792 | 0.891 |
| cross_parent_move | 772 | 660 | 638 | 0.855 | 0.826 |
| wrap_unwrap | 5801 | 5195 | 5392 | 0.896 | 0.929 |
| wholesale_rewrite | 93 | 90 | 92 | 0.968 | 0.989 |
| context | 2500191 | 2499871 | 2499737 | 1.000 | 1.000 |

Fixtures containing any wrap/unwrap: 177/505 (35.0%); any cross-parent move: 32/505 (6.3%); any reorder: 20/505 (4.0%).
Fixtures where difffold has more visible mismatches than OmniDiff: 78/505 (15.4%); of those, 61 contain a wrap/unwrap.

Primary cause of the gap in the fixtures where difffold is worse (class with the largest excess of failed decisions):

| class | fixtures | excess failed decisions |
|---|---|---|
| context | 14 | 51 |
| cross_parent_move | 2 | 45 |
| reorder | 2 | 9 |
| repeated_children | 4 | 171 |
| sibling_ins_del | 20 | 617 |
| wrap_unwrap | 36 | 519 |

Fixtures where OmniDiff is perfect and difffold is not: 43 (8.5% of all). Classes present in them:

- local_edit: 8
- sibling_ins_del: 27
- repeated_children: 13
- reorder: 4
- cross_parent_move: 3
- wrap_unwrap: 32
- wholesale_rewrite: 0
- context: 43
- none of move, wrap/unwrap, reorder, repeated, rewrite: 5

### 10 worst fixtures for difffold (visible mismatches minus OmniDiff's)

| fixture | lang | difffold vis. mismatches | omnidiff | decisions | difffold excess fails by cause |
|---|---|---|---|---|---|
| full/java-pdftk-java-pdftk-real-change-all-across-the-file | java | 398 | 233 | 4938 | context:-11 cross_parent_move:+17 local_edit:-5 reorder:+83 repeated_children:+2 sibling_ins_del:+59 wrap_unwrap:+84 |
| defects4j/java-defects4j-closure-137-makedeclarednamesunique | java | 273 | 115 | 3630 | context:+11 cross_parent_move:-16 sibling_ins_del:+85 wrap_unwrap:+131 |
| small/rust-rustdesk-rustdesk-actual-logic-change-in-io-loop-medium-sized-file | rust | 163 | 5 | 23711 | context:-1 repeated_children:+107 sibling_ins_del:+81 wrap_unwrap:+53 |
| full/java-jakartaee-rest-real-logic-change-of-a-significant-chunck | java | 180 | 50 | 997 | context:+2 sibling_ins_del:+187 |
| full/rust-tiffany352-rink-rs-real-change | rust | 131 | 28 | 4554 | context:+8 local_edit:+1 repeated_children:+1 sibling_ins_del:+114 wrap_unwrap:+4 |
| small/python-django-django-update-unit-tests-actual-logic-change | python | 98 | 4 | 4461 | repeated_children:+3 sibling_ins_del:+123 |
| small/rust-rustdesk-rustdesk-large-file-40k-normal-feature-work | rust | 75 | 2 | 46177 | context:+1 repeated_children:+53 sibling_ins_del:+43 wrap_unwrap:+15 |
| stratified/go-jesseduffield-lazygit-many-multi-maps-very-difficult | go | 124 | 55 | 712 | context:+1 repeated_children:+25 sibling_ins_del:+5 wrap_unwrap:+56 |
| small/rust-vercel-nextjs-refactoring-would-require-mulitmap-mapping | rust | 42 | 8 | 8965 | cross_parent_move:+41 repeated_children:-1 sibling_ins_del:-2 wrap_unwrap:+4 |
| handmade/rust-turbopack-module-rule | rust | 76 | 43 | 2134 | repeated_children:+1 sibling_ins_del:+6 wrap_unwrap:+38 |

### Calibration of this scorer against OmniDiff's own checker

On 505 fixtures with a native result: OmniDiff native visible mismatches total 1544, this scorer's 1544; zero/non-zero agreement 100.0%. The scorer ignores operation kinds (Identical vs Update) and the subtree-closure step of groups; the native checker enforces both.
