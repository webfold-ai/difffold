## Fixtures scored: 493 (unscorable: 381)

### All scorable fixtures

Micro (sums over fixtures):

| lang | tool | fixtures | node-corr. accuracy | pair P | pair R | pair F1 | span P | span R | span F1 | perfect | near-perfect | strict perfect |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| c | difffold | 51 | 0.997 | 0.999 | 0.999 | 0.999 | 0.899 | 0.848 | 0.873 | 78.4% | 90.2% | 78.4% |
| c | omnidiff | 51 | 0.997 | 0.999 | 0.999 | 0.999 | 0.849 | 0.901 | 0.874 | 82.4% | 96.1% | 82.4% |
| go | difffold | 44 | 0.999 | 1.000 | 1.000 | 1.000 | 0.998 | 0.980 | 0.989 | 84.1% | 100.0% | 84.1% |
| go | omnidiff | 44 | 0.999 | 1.000 | 1.000 | 1.000 | 0.996 | 0.975 | 0.985 | 88.6% | 100.0% | 88.6% |
| java | difffold | 248 | 0.999 | 1.000 | 1.000 | 1.000 | 0.980 | 0.972 | 0.976 | 73.4% | 94.4% | 69.0% |
| java | omnidiff | 248 | 0.999 | 1.000 | 1.000 | 1.000 | 0.977 | 0.986 | 0.982 | 83.5% | 98.0% | 79.4% |
| javascript | difffold | 27 | 0.999 | 1.000 | 1.000 | 1.000 | 0.902 | 0.982 | 0.941 | 66.7% | 77.8% | 66.7% |
| javascript | omnidiff | 27 | 0.999 | 1.000 | 1.000 | 1.000 | 0.934 | 1.000 | 0.966 | 85.2% | 88.9% | 81.5% |
| python | difffold | 33 | 0.998 | 0.999 | 1.000 | 0.999 | 0.958 | 0.928 | 0.942 | 72.7% | 87.9% | 72.7% |
| python | omnidiff | 33 | 1.000 | 1.000 | 1.000 | 1.000 | 0.968 | 0.995 | 0.981 | 78.8% | 97.0% | 78.8% |
| rust | difffold | 56 | 0.999 | 1.000 | 0.999 | 0.999 | 0.975 | 0.978 | 0.976 | 73.2% | 92.9% | 69.6% |
| rust | omnidiff | 56 | 0.999 | 1.000 | 1.000 | 1.000 | 0.985 | 0.991 | 0.988 | 80.4% | 96.4% | 80.4% |
| tsx | difffold | 21 | 0.998 | 0.999 | 0.999 | 0.999 | 1.000 | 0.981 | 0.991 | 66.7% | 85.7% | 66.7% |
| tsx | omnidiff | 21 | 0.998 | 0.999 | 0.999 | 0.999 | 0.930 | 1.000 | 0.964 | 71.4% | 90.5% | 71.4% |
| typescript | difffold | 13 | 1.000 | 1.000 | 1.000 | 1.000 | 1.000 | 1.000 | 1.000 | 100.0% | 100.0% | 100.0% |
| typescript | omnidiff | 13 | 1.000 | 1.000 | 1.000 | 1.000 | 1.000 | 1.000 | 1.000 | 100.0% | 100.0% | 100.0% |
| ALL | difffold | 493 | 0.999 | 1.000 | 1.000 | 1.000 | 0.971 | 0.958 | 0.964 | 74.8% | 92.7% | 72.2% |
| ALL | omnidiff | 493 | 0.999 | 1.000 | 1.000 | 1.000 | 0.966 | 0.978 | 0.972 | 83.2% | 97.0% | 80.9% |

Macro (mean of per-fixture values):

| lang | tool | accuracy | pair P | pair R | pair F1 | span P | span R | span F1 |
|---|---|---|---|---|---|---|---|---|
| c | difffold | 0.981 | 0.968 | 0.971 | 0.969 | 0.978 | 0.958 | 0.966 |
| c | omnidiff | 0.989 | 0.984 | 0.987 | 0.985 | 0.971 | 0.978 | 0.973 |
| go | difffold | 1.000 | 1.000 | 1.000 | 1.000 | 0.994 | 0.988 | 0.991 |
| go | omnidiff | 1.000 | 1.000 | 1.000 | 1.000 | 0.991 | 0.989 | 0.989 |
| java | difffold | 0.996 | 0.997 | 0.999 | 0.998 | 0.980 | 0.990 | 0.982 |
| java | omnidiff | 0.998 | 1.000 | 1.000 | 1.000 | 0.984 | 0.990 | 0.986 |
| javascript | difffold | 0.978 | 0.989 | 0.991 | 0.990 | 0.926 | 0.996 | 0.944 |
| javascript | omnidiff | 0.986 | 0.995 | 0.993 | 0.994 | 0.965 | 1.000 | 0.975 |
| python | difffold | 0.995 | 0.997 | 0.998 | 0.998 | 0.980 | 0.984 | 0.978 |
| python | omnidiff | 0.999 | 1.000 | 0.999 | 0.999 | 0.969 | 0.984 | 0.974 |
| rust | difffold | 0.991 | 0.994 | 0.992 | 0.993 | 0.980 | 0.989 | 0.983 |
| rust | omnidiff | 0.993 | 0.996 | 0.995 | 0.995 | 0.995 | 0.999 | 0.997 |
| tsx | difffold | 0.975 | 0.981 | 0.980 | 0.981 | 1.000 | 0.993 | 0.996 |
| tsx | omnidiff | 0.969 | 0.974 | 0.969 | 0.971 | 0.958 | 1.000 | 0.962 |
| typescript | difffold | 1.000 | 1.000 | 1.000 | 1.000 | 1.000 | 1.000 | 1.000 |
| typescript | omnidiff | 1.000 | 1.000 | 1.000 | 1.000 | 1.000 | 1.000 | 1.000 |
| ALL | difffold | 0.992 | 0.993 | 0.994 | 0.994 | 0.979 | 0.986 | 0.980 |
| ALL | omnidiff | 0.995 | 0.996 | 0.996 | 0.996 | 0.982 | 0.990 | 0.984 |

### Excluding wholesale-rewrite fixtures

Micro (sums over fixtures):

| lang | tool | fixtures | node-corr. accuracy | pair P | pair R | pair F1 | span P | span R | span F1 | perfect | near-perfect | strict perfect |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| c | difffold | 50 | 0.998 | 0.999 | 0.999 | 0.999 | 0.894 | 0.854 | 0.874 | 80.0% | 92.0% | 80.0% |
| c | omnidiff | 50 | 0.998 | 0.999 | 0.999 | 0.999 | 0.842 | 0.913 | 0.876 | 84.0% | 98.0% | 84.0% |
| go | difffold | 44 | 0.999 | 1.000 | 1.000 | 1.000 | 0.998 | 0.980 | 0.989 | 84.1% | 100.0% | 84.1% |
| go | omnidiff | 44 | 0.999 | 1.000 | 1.000 | 1.000 | 0.996 | 0.975 | 0.985 | 88.6% | 100.0% | 88.6% |
| java | difffold | 248 | 0.999 | 1.000 | 1.000 | 1.000 | 0.980 | 0.972 | 0.976 | 73.4% | 94.4% | 69.0% |
| java | omnidiff | 248 | 0.999 | 1.000 | 1.000 | 1.000 | 0.977 | 0.986 | 0.982 | 83.5% | 98.0% | 79.4% |
| javascript | difffold | 27 | 0.999 | 1.000 | 1.000 | 1.000 | 0.902 | 0.982 | 0.941 | 66.7% | 77.8% | 66.7% |
| javascript | omnidiff | 27 | 0.999 | 1.000 | 1.000 | 1.000 | 0.934 | 1.000 | 0.966 | 85.2% | 88.9% | 81.5% |
| python | difffold | 33 | 0.998 | 0.999 | 1.000 | 0.999 | 0.958 | 0.928 | 0.942 | 72.7% | 87.9% | 72.7% |
| python | omnidiff | 33 | 1.000 | 1.000 | 1.000 | 1.000 | 0.968 | 0.995 | 0.981 | 78.8% | 97.0% | 78.8% |
| rust | difffold | 55 | 0.999 | 1.000 | 0.999 | 0.999 | 0.975 | 0.978 | 0.976 | 74.5% | 92.7% | 70.9% |
| rust | omnidiff | 55 | 0.999 | 1.000 | 1.000 | 1.000 | 0.985 | 0.991 | 0.988 | 81.8% | 96.4% | 81.8% |
| tsx | difffold | 21 | 0.998 | 0.999 | 0.999 | 0.999 | 1.000 | 0.981 | 0.991 | 66.7% | 85.7% | 66.7% |
| tsx | omnidiff | 21 | 0.998 | 0.999 | 0.999 | 0.999 | 0.930 | 1.000 | 0.964 | 71.4% | 90.5% | 71.4% |
| typescript | difffold | 13 | 1.000 | 1.000 | 1.000 | 1.000 | 1.000 | 1.000 | 1.000 | 100.0% | 100.0% | 100.0% |
| typescript | omnidiff | 13 | 1.000 | 1.000 | 1.000 | 1.000 | 1.000 | 1.000 | 1.000 | 100.0% | 100.0% | 100.0% |
| ALL | difffold | 491 | 0.999 | 1.000 | 1.000 | 1.000 | 0.971 | 0.959 | 0.965 | 75.2% | 92.9% | 72.5% |
| ALL | omnidiff | 491 | 0.999 | 1.000 | 1.000 | 1.000 | 0.966 | 0.980 | 0.973 | 83.5% | 97.1% | 81.3% |

Macro (mean of per-fixture values):

| lang | tool | accuracy | pair P | pair R | pair F1 | span P | span R | span F1 |
|---|---|---|---|---|---|---|---|---|
| c | difffold | 0.988 | 0.985 | 0.985 | 0.985 | 0.978 | 0.961 | 0.968 |
| c | omnidiff | 0.995 | 0.998 | 0.997 | 0.998 | 0.972 | 0.981 | 0.975 |
| go | difffold | 1.000 | 1.000 | 1.000 | 1.000 | 0.994 | 0.988 | 0.991 |
| go | omnidiff | 1.000 | 1.000 | 1.000 | 1.000 | 0.991 | 0.989 | 0.989 |
| java | difffold | 0.996 | 0.997 | 0.999 | 0.998 | 0.980 | 0.990 | 0.982 |
| java | omnidiff | 0.998 | 1.000 | 1.000 | 1.000 | 0.984 | 0.990 | 0.986 |
| javascript | difffold | 0.978 | 0.989 | 0.991 | 0.990 | 0.926 | 0.996 | 0.944 |
| javascript | omnidiff | 0.986 | 0.995 | 0.993 | 0.994 | 0.965 | 1.000 | 0.975 |
| python | difffold | 0.995 | 0.997 | 0.998 | 0.998 | 0.980 | 0.984 | 0.978 |
| python | omnidiff | 0.999 | 1.000 | 0.999 | 0.999 | 0.969 | 0.984 | 0.974 |
| rust | difffold | 0.991 | 0.994 | 0.992 | 0.993 | 0.980 | 0.989 | 0.983 |
| rust | omnidiff | 0.993 | 0.996 | 0.995 | 0.995 | 0.995 | 0.999 | 0.997 |
| tsx | difffold | 0.975 | 0.981 | 0.980 | 0.981 | 1.000 | 0.993 | 0.996 |
| tsx | omnidiff | 0.969 | 0.974 | 0.969 | 0.971 | 0.958 | 1.000 | 0.962 |
| typescript | difffold | 1.000 | 1.000 | 1.000 | 1.000 | 1.000 | 1.000 | 1.000 |
| typescript | omnidiff | 1.000 | 1.000 | 1.000 | 1.000 | 1.000 | 1.000 | 1.000 |
| ALL | difffold | 0.993 | 0.995 | 0.996 | 0.995 | 0.980 | 0.987 | 0.980 |
| ALL | omnidiff | 0.996 | 0.998 | 0.997 | 0.997 | 0.982 | 0.991 | 0.984 |

### Unscorable fixtures by reason (full list: unscorable.csv)

| reason | fixtures |
|---|---|
| ground truth | 1 |
| ground truth has no pairs | 2 |
| language not parsed here: .R | 1 |
| language not parsed here: .bash | 1 |
| language not parsed here: .cc | 3 |
| language not parsed here: .cpp | 45 |
| language not parsed here: .cs | 44 |
| language not parsed here: .css | 24 |
| language not parsed here: .cxx | 3 |
| language not parsed here: .hpp | 5 |
| language not parsed here: .html | 25 |
| language not parsed here: .hxx | 1 |
| language not parsed here: .json | 23 |
| language not parsed here: .kt | 31 |
| language not parsed here: .lua | 26 |
| language not parsed here: .php | 20 |
| language not parsed here: .r | 1 |
| language not parsed here: .rb | 24 |
| language not parsed here: .scala | 8 |
| language not parsed here: .scss | 2 |
| language not parsed here: .sh | 22 |
| language not parsed here: .sql | 4 |
| language not parsed here: .swift | 20 |
| language not parsed here: .vim | 13 |
| language not parsed here: .xml | 18 |
| language not parsed here: .yaml | 4 |
| language not parsed here: .yml | 10 |

### Ground-truth composition and the top-down ceiling

| lang | fixtures | GT pairs | identical pairs | changed pairs | GT deleted nodes | GT inserted nodes | cross-parent move roots | wrap/unwrap roots | reorder pairs | top-down ceiling (pair recall) | fixtures at ceiling 100% |
|---|---|---|---|---|---|---|---|---|---|---|---|
| c | 51 | 360042 | 359395 | 647 | 981 | 1540 | 2 | 63 | 35 | 0.998 | 78.4% |
| go | 44 | 252892 | 252374 | 518 | 292 | 4227 | 9 | 37 | 1 | 0.998 | 75.0% |
| java | 248 | 1194495 | 1192213 | 2282 | 2146 | 7792 | 31 | 269 | 9 | 0.998 | 54.4% |
| javascript | 27 | 50795 | 50612 | 183 | 214 | 155 | 0 | 21 | 2 | 0.998 | 63.0% |
| python | 33 | 114410 | 113908 | 502 | 443 | 1229 | 3 | 33 | 1 | 0.999 | 66.7% |
| rust | 56 | 407858 | 407121 | 737 | 2319 | 3856 | 9 | 75 | 8 | 0.996 | 69.6% |
| tsx | 21 | 26322 | 26107 | 215 | 84 | 278 | 0 | 25 | 3 | 0.991 | 61.9% |
| typescript | 13 | 134427 | 134369 | 58 | 8 | 279 | 0 | 0 | 0 | 1.000 | 100.0% |
| ALL | 493 | 2541241 | 2536099 | 5142 | 6487 | 19356 | 54 | 523 | 59 | 0.998 | 63.3% |

### Failures by root-cause class (decisions: pair, delete, insert and group-member checks)

Fixture-level attribution: a fixture flagged wholesale rewrite counts all its decisions there; otherwise a failed decision is charged to the class of its root cause (see definitions).

| class | fixtures containing | decisions | difffold fails | omnidiff fails | difffold acc | omnidiff acc | gap (fails) | share of gap | perfect fixtures difffold | perfect fixtures omnidiff |
|---|---|---|---|---|---|---|---|---|---|---|
| local_edit | 152 | 320 | 24 | 19 | 0.925 | 0.941 | 5 | 0.8% | 77.0% | 82.2% |
| sibling_ins_del | 315 | 19957 | 1061 | 665 | 0.947 | 0.967 | 396 | 64.9% | 70.5% | 79.0% |
| repeated_children | 118 | 1732 | 507 | 542 | 0.707 | 0.687 | -35 | 0.0% | 53.4% | 59.3% |
| reorder | 18 | 382 | 37 | 27 | 0.903 | 0.929 | 10 | 1.6% | 38.9% | 61.1% |
| cross_parent_move | 25 | 329 | 42 | 76 | 0.872 | 0.769 | -34 | 0.0% | 24.0% | 20.0% |
| wrap_unwrap | 157 | 9090 | 782 | 408 | 0.914 | 0.955 | 374 | 61.3% | 49.0% | 58.6% |
| wholesale_rewrite | 2 | 3122 | 121 | 127 | 0.961 | 0.959 | -6 | 0.0% | 0.0% | 0.0% |
| context | 491 | 2532938 | 452 | 552 | 1.000 | 1.000 | -100 | 0.0% | 75.2% | 83.5% |

### Pair recall by root-cause class (ground-truth pairs only)

| class | ground-truth pairs | difffold pairs correct | omnidiff pairs correct | difffold recall | omnidiff recall |
|---|---|---|---|---|---|
| local_edit | 320 | 296 | 301 | 0.925 | 0.941 |
| sibling_ins_del | 0 | 0 | 0 | 0.000 | 0.000 |
| repeated_children | 0 | 0 | 0 | 0.000 | 0.000 |
| reorder | 382 | 345 | 355 | 0.903 | 0.929 |
| cross_parent_move | 329 | 287 | 253 | 0.872 | 0.769 |
| wrap_unwrap | 4527 | 4116 | 4325 | 0.909 | 0.955 |
| wholesale_rewrite | 2745 | 2718 | 2699 | 0.990 | 0.983 |
| context | 2532938 | 2532486 | 2532386 | 1.000 | 1.000 |

Fixtures containing any wrap/unwrap: 157/493 (31.8%); any cross-parent move: 25/493 (5.1%); any reorder: 18/493 (3.7%).
Fixtures where difffold has more visible mismatches than OmniDiff: 86/493 (17.4%); of those, 53 contain a wrap/unwrap.

Primary cause of the gap in the fixtures where difffold is worse (class with the largest excess of failed decisions):

| class | fixtures | excess failed decisions |
|---|---|---|
| context | 17 | 92 |
| cross_parent_move | 2 | 7 |
| local_edit | 1 | 1 |
| reorder | 2 | 19 |
| repeated_children | 4 | 17 |
| sibling_ins_del | 31 | 443 |
| wholesale_rewrite | 1 | 20 |
| wrap_unwrap | 28 | 419 |

Fixtures where OmniDiff is perfect and difffold is not: 51 (10.3% of all). Classes present in them:

- local_edit: 10
- sibling_ins_del: 34
- repeated_children: 12
- reorder: 5
- cross_parent_move: 2
- wrap_unwrap: 24
- wholesale_rewrite: 0
- context: 51
- none of move, wrap/unwrap, reorder, repeated, rewrite: 15

### 10 worst fixtures for difffold (visible mismatches minus OmniDiff's)

| fixture | lang | difffold vis. mismatches | omnidiff | decisions | difffold excess fails by cause |
|---|---|---|---|---|---|
| stratified/c-postgres-postgres-preprocessor-heavy-change | c | 116 | 0 | 362 | sibling_ins_del:+12 wrap_unwrap:+159 |
| full/python-aboutcode-org-license-expression-excellent-test-case | python | 111 | 7 | 13686 | context:+2 repeated_children:+15 sibling_ins_del:+102 wrap_unwrap:+5 |
| stratified/rust-zed-industries-zed-a-lot-of-removed | rust | 66 | 2 | 687 | context:+2 sibling_ins_del:+2 wrap_unwrap:+88 |
| defects4j/java-defects4j-cli-1-commandline | java | 109 | 49 | 1155 | context:+1 sibling_ins_del:+78 wrap_unwrap:+1 |
| defects4j/java-defects4j-cli-15-writeablecommandlineimpl | java | 66 | 23 | 1959 | context:+15 local_edit:+1 sibling_ins_del:+10 wrap_unwrap:+36 |
| full/c-sched-ext-scx-many-many-moves-some-deletes-some-adds | c | 39 | 3 | 2590 | context:+15 local_edit:-1 reorder:+13 sibling_ins_del:+10 |
| defects4j/java-defects4j-closure-175-functioninjector | java | 69 | 37 | 4941 | sibling_ins_del:+34 wrap_unwrap:+4 |
| defects4j/java-defects4j-closure-134-typedscopecreator | java | 28 | 0 | 9325 | context:+19 wrap_unwrap:+20 |
| stratified/rust-rustdesk-rustdesk-complex-change-with-a-lot-of-add | rust | 46 | 20 | 15974 | context:+3 repeated_children:+1 sibling_ins_del:+17 wrap_unwrap:+17 |
| stratified/c-python-cpython-autogenerated-test-case | c | 56 | 33 | 100504 | repeated_children:+3 sibling_ins_del:+12 wrap_unwrap:+16 |

### Calibration of this scorer against OmniDiff's own checker

On 493 fixtures with a native result: OmniDiff native visible mismatches total 1707, this scorer's 1707; zero/non-zero agreement 100.0%. The scorer ignores operation kinds (Identical vs Update) and the subtree-closure step of groups; the native checker enforces both.
