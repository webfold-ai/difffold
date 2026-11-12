## Fixtures scored: 998 (unscorable: 763)

### All scorable fixtures

Micro (sums over fixtures):

| lang | tool | fixtures | node-corr. accuracy | pair P | pair R | pair F1 | span P | span R | span F1 | perfect | near-perfect | strict perfect |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| c | difffold | 88 | 0.998 | 0.999 | 0.999 | 0.999 | 0.915 | 0.870 | 0.892 | 75.0% | 93.2% | 73.9% |
| c | omnidiff | 88 | 0.998 | 0.999 | 0.999 | 0.999 | 0.854 | 0.918 | 0.885 | 79.5% | 97.7% | 77.3% |
| go | difffold | 79 | 0.999 | 1.000 | 1.000 | 1.000 | 0.995 | 0.983 | 0.989 | 73.4% | 98.7% | 73.4% |
| go | omnidiff | 79 | 0.999 | 1.000 | 1.000 | 1.000 | 0.952 | 0.981 | 0.966 | 78.5% | 96.2% | 78.5% |
| java | difffold | 515 | 0.999 | 0.999 | 1.000 | 1.000 | 0.975 | 0.956 | 0.965 | 75.9% | 93.8% | 71.7% |
| java | omnidiff | 515 | 0.999 | 1.000 | 1.000 | 1.000 | 0.971 | 0.985 | 0.978 | 83.9% | 97.3% | 80.4% |
| javascript | difffold | 50 | 0.999 | 1.000 | 1.000 | 1.000 | 0.947 | 0.985 | 0.965 | 72.0% | 82.0% | 72.0% |
| javascript | omnidiff | 50 | 0.999 | 1.000 | 1.000 | 1.000 | 0.942 | 1.000 | 0.970 | 84.0% | 92.0% | 82.0% |
| python | difffold | 71 | 0.998 | 0.999 | 1.000 | 0.999 | 0.975 | 0.928 | 0.951 | 80.3% | 91.5% | 78.9% |
| python | omnidiff | 71 | 1.000 | 1.000 | 1.000 | 1.000 | 0.983 | 0.996 | 0.990 | 84.5% | 98.6% | 84.5% |
| rust | difffold | 111 | 0.998 | 0.999 | 0.999 | 0.999 | 0.980 | 0.969 | 0.974 | 66.7% | 87.4% | 64.9% |
| rust | omnidiff | 111 | 0.999 | 1.000 | 1.000 | 1.000 | 0.977 | 0.991 | 0.984 | 73.9% | 91.9% | 73.9% |
| tsx | difffold | 41 | 0.999 | 1.000 | 0.999 | 1.000 | 0.975 | 0.981 | 0.978 | 73.2% | 87.8% | 73.2% |
| tsx | omnidiff | 41 | 0.999 | 1.000 | 0.999 | 1.000 | 0.943 | 1.000 | 0.970 | 73.2% | 92.7% | 73.2% |
| typescript | difffold | 43 | 1.000 | 1.000 | 1.000 | 1.000 | 0.989 | 0.989 | 0.989 | 90.7% | 95.3% | 90.7% |
| typescript | omnidiff | 43 | 1.000 | 1.000 | 1.000 | 1.000 | 0.995 | 1.000 | 0.997 | 95.3% | 100.0% | 93.0% |
| ALL | difffold | 998 | 0.999 | 0.999 | 1.000 | 1.000 | 0.974 | 0.956 | 0.965 | 75.3% | 92.5% | 72.6% |
| ALL | omnidiff | 998 | 0.999 | 1.000 | 1.000 | 1.000 | 0.962 | 0.984 | 0.973 | 82.1% | 96.4% | 79.9% |

Macro (mean of per-fixture values):

| lang | tool | accuracy | pair P | pair R | pair F1 | span P | span R | span F1 |
|---|---|---|---|---|---|---|---|---|
| c | difffold | 0.988 | 0.981 | 0.977 | 0.978 | 0.981 | 0.970 | 0.973 |
| c | omnidiff | 0.993 | 0.991 | 0.987 | 0.988 | 0.968 | 0.984 | 0.972 |
| go | difffold | 0.996 | 0.998 | 0.997 | 0.997 | 0.992 | 0.990 | 0.991 |
| go | omnidiff | 0.996 | 0.999 | 0.999 | 0.999 | 0.978 | 0.992 | 0.981 |
| java | difffold | 0.996 | 0.997 | 0.999 | 0.998 | 0.987 | 0.990 | 0.987 |
| java | omnidiff | 0.998 | 0.999 | 0.999 | 0.999 | 0.987 | 0.992 | 0.989 |
| javascript | difffold | 0.984 | 0.991 | 0.991 | 0.991 | 0.953 | 0.995 | 0.965 |
| javascript | omnidiff | 0.991 | 0.997 | 0.994 | 0.996 | 0.972 | 1.000 | 0.982 |
| python | difffold | 0.997 | 0.998 | 0.998 | 0.998 | 0.987 | 0.990 | 0.986 |
| python | omnidiff | 0.999 | 1.000 | 1.000 | 1.000 | 0.983 | 0.992 | 0.986 |
| rust | difffold | 0.990 | 0.995 | 0.994 | 0.995 | 0.982 | 0.989 | 0.984 |
| rust | omnidiff | 0.992 | 0.997 | 0.995 | 0.996 | 0.988 | 0.997 | 0.992 |
| tsx | difffold | 0.986 | 0.990 | 0.989 | 0.989 | 0.998 | 0.995 | 0.997 |
| tsx | omnidiff | 0.983 | 0.986 | 0.984 | 0.985 | 0.968 | 1.000 | 0.975 |
| typescript | difffold | 0.993 | 0.994 | 0.992 | 0.993 | 0.988 | 0.996 | 0.991 |
| typescript | omnidiff | 0.999 | 1.000 | 0.999 | 0.999 | 0.991 | 1.000 | 0.994 |
| ALL | difffold | 0.993 | 0.995 | 0.995 | 0.995 | 0.985 | 0.989 | 0.985 |
| ALL | omnidiff | 0.996 | 0.998 | 0.997 | 0.997 | 0.983 | 0.993 | 0.986 |

### Excluding wholesale-rewrite fixtures

Micro (sums over fixtures):

| lang | tool | fixtures | node-corr. accuracy | pair P | pair R | pair F1 | span P | span R | span F1 | perfect | near-perfect | strict perfect |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| c | difffold | 86 | 0.999 | 0.999 | 0.999 | 0.999 | 0.912 | 0.875 | 0.893 | 76.7% | 94.2% | 75.6% |
| c | omnidiff | 86 | 0.998 | 0.999 | 0.999 | 0.999 | 0.848 | 0.928 | 0.886 | 81.4% | 98.8% | 79.1% |
| go | difffold | 79 | 0.999 | 1.000 | 1.000 | 1.000 | 0.995 | 0.983 | 0.989 | 73.4% | 98.7% | 73.4% |
| go | omnidiff | 79 | 0.999 | 1.000 | 1.000 | 1.000 | 0.952 | 0.981 | 0.966 | 78.5% | 96.2% | 78.5% |
| java | difffold | 514 | 0.999 | 0.999 | 1.000 | 1.000 | 0.974 | 0.954 | 0.964 | 75.9% | 93.8% | 71.8% |
| java | omnidiff | 514 | 0.999 | 1.000 | 1.000 | 1.000 | 0.970 | 0.985 | 0.977 | 83.9% | 97.3% | 80.4% |
| javascript | difffold | 50 | 0.999 | 1.000 | 1.000 | 1.000 | 0.947 | 0.985 | 0.965 | 72.0% | 82.0% | 72.0% |
| javascript | omnidiff | 50 | 0.999 | 1.000 | 1.000 | 1.000 | 0.942 | 1.000 | 0.970 | 84.0% | 92.0% | 82.0% |
| python | difffold | 71 | 0.998 | 0.999 | 1.000 | 0.999 | 0.975 | 0.928 | 0.951 | 80.3% | 91.5% | 78.9% |
| python | omnidiff | 71 | 1.000 | 1.000 | 1.000 | 1.000 | 0.983 | 0.996 | 0.990 | 84.5% | 98.6% | 84.5% |
| rust | difffold | 110 | 0.998 | 0.999 | 0.999 | 0.999 | 0.980 | 0.969 | 0.975 | 67.3% | 87.3% | 65.5% |
| rust | omnidiff | 110 | 0.999 | 1.000 | 1.000 | 1.000 | 0.977 | 0.991 | 0.984 | 74.5% | 91.8% | 74.5% |
| tsx | difffold | 41 | 0.999 | 1.000 | 0.999 | 1.000 | 0.975 | 0.981 | 0.978 | 73.2% | 87.8% | 73.2% |
| tsx | omnidiff | 41 | 0.999 | 1.000 | 0.999 | 1.000 | 0.943 | 1.000 | 0.970 | 73.2% | 92.7% | 73.2% |
| typescript | difffold | 43 | 1.000 | 1.000 | 1.000 | 1.000 | 0.989 | 0.989 | 0.989 | 90.7% | 95.3% | 90.7% |
| typescript | omnidiff | 43 | 1.000 | 1.000 | 1.000 | 1.000 | 0.995 | 1.000 | 0.997 | 95.3% | 100.0% | 93.0% |
| ALL | difffold | 994 | 0.999 | 0.999 | 1.000 | 1.000 | 0.974 | 0.956 | 0.965 | 75.5% | 92.6% | 72.9% |
| ALL | omnidiff | 994 | 0.999 | 1.000 | 1.000 | 1.000 | 0.962 | 0.984 | 0.973 | 82.3% | 96.5% | 80.1% |

Macro (mean of per-fixture values):

| lang | tool | accuracy | pair P | pair R | pair F1 | span P | span R | span F1 |
|---|---|---|---|---|---|---|---|---|
| c | difffold | 0.992 | 0.991 | 0.990 | 0.991 | 0.981 | 0.971 | 0.974 |
| c | omnidiff | 0.997 | 0.999 | 0.998 | 0.998 | 0.968 | 0.986 | 0.973 |
| go | difffold | 0.996 | 0.998 | 0.997 | 0.997 | 0.992 | 0.990 | 0.991 |
| go | omnidiff | 0.996 | 0.999 | 0.999 | 0.999 | 0.978 | 0.992 | 0.981 |
| java | difffold | 0.996 | 0.997 | 0.999 | 0.998 | 0.987 | 0.990 | 0.987 |
| java | omnidiff | 0.998 | 0.999 | 0.999 | 0.999 | 0.987 | 0.992 | 0.989 |
| javascript | difffold | 0.984 | 0.991 | 0.991 | 0.991 | 0.953 | 0.995 | 0.965 |
| javascript | omnidiff | 0.991 | 0.997 | 0.994 | 0.996 | 0.972 | 1.000 | 0.982 |
| python | difffold | 0.997 | 0.998 | 0.998 | 0.998 | 0.987 | 0.990 | 0.986 |
| python | omnidiff | 0.999 | 1.000 | 1.000 | 1.000 | 0.983 | 0.992 | 0.986 |
| rust | difffold | 0.990 | 0.995 | 0.994 | 0.994 | 0.982 | 0.989 | 0.984 |
| rust | omnidiff | 0.992 | 0.997 | 0.995 | 0.996 | 0.988 | 0.997 | 0.992 |
| tsx | difffold | 0.986 | 0.990 | 0.989 | 0.989 | 0.998 | 0.995 | 0.997 |
| tsx | omnidiff | 0.983 | 0.986 | 0.984 | 0.985 | 0.968 | 1.000 | 0.975 |
| typescript | difffold | 0.993 | 0.994 | 0.992 | 0.993 | 0.988 | 0.996 | 0.991 |
| typescript | omnidiff | 0.999 | 1.000 | 0.999 | 0.999 | 0.991 | 1.000 | 0.994 |
| ALL | difffold | 0.994 | 0.996 | 0.996 | 0.996 | 0.985 | 0.989 | 0.985 |
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
| local_edit | 278 | 559 | 44 | 46 | 0.921 | 0.918 | -2 | 0.0% | 77.0% | 80.9% |
| sibling_ins_del | 659 | 42186 | 2447 | 1185 | 0.942 | 0.972 | 1262 | 58.1% | 71.9% | 77.8% |
| repeated_children | 230 | 3375 | 1083 | 875 | 0.679 | 0.741 | 208 | 9.6% | 51.3% | 57.0% |
| reorder | 38 | 1044 | 175 | 99 | 0.832 | 0.905 | 76 | 3.5% | 34.2% | 55.3% |
| cross_parent_move | 56 | 1101 | 154 | 210 | 0.860 | 0.809 | -56 | 0.0% | 23.2% | 17.9% |
| wrap_unwrap | 333 | 20845 | 2035 | 1112 | 0.902 | 0.947 | 923 | 42.5% | 48.6% | 58.9% |
| wholesale_rewrite | 4 | 3983 | 124 | 128 | 0.969 | 0.968 | -4 | 0.0% | 25.0% | 25.0% |
| context | 994 | 5033129 | 772 | 1006 | 1.000 | 1.000 | -234 | 0.0% | 75.5% | 82.3% |

Fixtures containing any wrap/unwrap: 334/998 (33.5%); any cross-parent move: 57/998 (5.7%); any reorder: 38/998 (3.8%).
Fixtures where difffold has more visible mismatches than OmniDiff: 164/998 (16.4%); of those, 114 contain a wrap/unwrap.

Primary cause of the gap in the fixtures where difffold is worse (class with the largest excess of failed decisions):

| class | fixtures | excess failed decisions |
|---|---|---|
| context | 31 | 143 |
| cross_parent_move | 4 | 52 |
| local_edit | 1 | 1 |
| reorder | 4 | 28 |
| repeated_children | 8 | 188 |
| sibling_ins_del | 51 | 1060 |
| wholesale_rewrite | 1 | 20 |
| wrap_unwrap | 64 | 938 |

Fixtures where OmniDiff is perfect and difffold is not: 94 (9.4% of all). Classes present in them:

- local_edit: 18
- sibling_ins_del: 61
- repeated_children: 25
- reorder: 9
- cross_parent_move: 5
- wrap_unwrap: 56
- wholesale_rewrite: 0
- context: 94
- none of move, wrap/unwrap, reorder, repeated, rewrite: 20

### 10 worst fixtures for difffold (visible mismatches minus OmniDiff's)

| fixture | lang | difffold vis. mismatches | omnidiff | decisions | difffold excess fails by cause |
|---|---|---|---|---|---|
| full/java-pdftk-java-pdftk-real-change-all-across-the-file | java | 398 | 233 | 4938 | context:-11 cross_parent_move:+17 local_edit:-5 reorder:+83 repeated_children:+2 sibling_ins_del:+59 wrap_unwrap:+84 |
| defects4j/java-defects4j-closure-137-makedeclarednamesunique | java | 273 | 115 | 3630 | context:+11 cross_parent_move:-16 sibling_ins_del:+85 wrap_unwrap:+131 |
| small/rust-rustdesk-rustdesk-actual-logic-change-in-io-loop-medium-sized-file | rust | 163 | 5 | 23711 | context:-1 repeated_children:+107 sibling_ins_del:+81 wrap_unwrap:+53 |
| full/java-jakartaee-rest-real-logic-change-of-a-significant-chunck | java | 180 | 50 | 997 | context:+2 sibling_ins_del:+187 |
| stratified/c-postgres-postgres-preprocessor-heavy-change | c | 116 | 0 | 362 | sibling_ins_del:+12 wrap_unwrap:+159 |
| full/python-aboutcode-org-license-expression-excellent-test-case | python | 111 | 7 | 13686 | context:+2 repeated_children:+15 sibling_ins_del:+102 wrap_unwrap:+5 |
| full/rust-tiffany352-rink-rs-real-change | rust | 131 | 28 | 4554 | context:+8 local_edit:+1 repeated_children:+1 sibling_ins_del:+114 wrap_unwrap:+4 |
| small/python-django-django-update-unit-tests-actual-logic-change | python | 98 | 4 | 4461 | repeated_children:+3 sibling_ins_del:+123 |
| small/rust-rustdesk-rustdesk-large-file-40k-normal-feature-work | rust | 75 | 2 | 46177 | context:+1 repeated_children:+53 sibling_ins_del:+43 wrap_unwrap:+15 |
| stratified/go-jesseduffield-lazygit-many-multi-maps-very-difficult | go | 124 | 55 | 712 | context:+1 repeated_children:+25 sibling_ins_del:+5 wrap_unwrap:+56 |

### Calibration of this scorer against OmniDiff's own checker

On 998 fixtures with a native result: OmniDiff native visible mismatches total 3251, this scorer's 3251; zero/non-zero agreement 100.0%. The scorer ignores operation kinds (Identical vs Update) and the subtree-closure step of groups; the native checker enforces both.
