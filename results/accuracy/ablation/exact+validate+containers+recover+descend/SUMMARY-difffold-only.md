# Accuracy against hand-authored ground truth (difffold only)

### All scorable fixtures

Micro (sums over fixtures):

| lang | tool | fixtures | node-corr. accuracy | pair P | pair R | pair F1 | span P | span R | span F1 | perfect | near-perfect | strict perfect |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| c | difffold | 88 | 0.998 | 0.999 | 0.999 | 0.999 | 0.912 | 0.870 | 0.890 | 73.9% | 93.2% | 73.9% |
| go | difffold | 79 | 0.999 | 1.000 | 1.000 | 1.000 | 0.993 | 0.983 | 0.988 | 73.4% | 97.5% | 73.4% |
| java | difffold | 515 | 0.999 | 0.999 | 1.000 | 1.000 | 0.970 | 0.957 | 0.963 | 74.6% | 94.0% | 70.5% |
| javascript | difffold | 50 | 0.999 | 1.000 | 1.000 | 1.000 | 0.947 | 0.985 | 0.965 | 72.0% | 82.0% | 72.0% |
| python | difffold | 71 | 0.998 | 0.999 | 1.000 | 0.999 | 0.976 | 0.929 | 0.952 | 81.7% | 91.5% | 80.3% |
| rust | difffold | 111 | 0.998 | 0.999 | 0.999 | 0.999 | 0.977 | 0.970 | 0.974 | 66.7% | 87.4% | 64.9% |
| tsx | difffold | 41 | 0.999 | 1.000 | 0.999 | 1.000 | 0.965 | 0.981 | 0.973 | 70.7% | 87.8% | 70.7% |
| typescript | difffold | 43 | 1.000 | 1.000 | 1.000 | 1.000 | 0.989 | 0.989 | 0.989 | 90.7% | 95.3% | 90.7% |
| ALL | difffold | 998 | 0.999 | 0.999 | 1.000 | 1.000 | 0.971 | 0.957 | 0.964 | 74.4% | 92.5% | 72.0% |

Macro (mean of per-fixture values):

| lang | tool | accuracy | pair P | pair R | pair F1 | span P | span R | span F1 |
|---|---|---|---|---|---|---|---|---|
| c | difffold | 0.988 | 0.981 | 0.976 | 0.978 | 0.979 | 0.970 | 0.972 |
| go | difffold | 0.996 | 0.997 | 0.997 | 0.997 | 0.990 | 0.991 | 0.990 |
| java | difffold | 0.996 | 0.997 | 0.999 | 0.998 | 0.981 | 0.991 | 0.983 |
| javascript | difffold | 0.984 | 0.991 | 0.991 | 0.991 | 0.953 | 0.995 | 0.965 |
| python | difffold | 0.997 | 0.998 | 0.998 | 0.998 | 0.987 | 0.992 | 0.988 |
| rust | difffold | 0.990 | 0.995 | 0.994 | 0.994 | 0.980 | 0.990 | 0.983 |
| tsx | difffold | 0.986 | 0.990 | 0.989 | 0.989 | 0.992 | 0.995 | 0.993 |
| typescript | difffold | 0.993 | 0.994 | 0.992 | 0.993 | 0.988 | 0.996 | 0.991 |
| ALL | difffold | 0.993 | 0.995 | 0.995 | 0.995 | 0.981 | 0.989 | 0.983 |

### Excluding wholesale-rewrite fixtures

Micro (sums over fixtures):

| lang | tool | fixtures | node-corr. accuracy | pair P | pair R | pair F1 | span P | span R | span F1 | perfect | near-perfect | strict perfect |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| c | difffold | 86 | 0.999 | 0.999 | 0.999 | 0.999 | 0.908 | 0.875 | 0.891 | 75.6% | 94.2% | 75.6% |
| go | difffold | 79 | 0.999 | 1.000 | 1.000 | 1.000 | 0.993 | 0.983 | 0.988 | 73.4% | 97.5% | 73.4% |
| java | difffold | 514 | 0.999 | 0.999 | 1.000 | 1.000 | 0.969 | 0.956 | 0.962 | 74.5% | 94.0% | 70.6% |
| javascript | difffold | 50 | 0.999 | 1.000 | 1.000 | 1.000 | 0.947 | 0.985 | 0.965 | 72.0% | 82.0% | 72.0% |
| python | difffold | 71 | 0.998 | 0.999 | 1.000 | 0.999 | 0.976 | 0.929 | 0.952 | 81.7% | 91.5% | 80.3% |
| rust | difffold | 110 | 0.998 | 0.999 | 0.999 | 0.999 | 0.977 | 0.970 | 0.974 | 67.3% | 87.3% | 65.5% |
| tsx | difffold | 41 | 0.999 | 1.000 | 0.999 | 1.000 | 0.965 | 0.981 | 0.973 | 70.7% | 87.8% | 70.7% |
| typescript | difffold | 43 | 1.000 | 1.000 | 1.000 | 1.000 | 0.989 | 0.989 | 0.989 | 90.7% | 95.3% | 90.7% |
| ALL | difffold | 994 | 0.999 | 0.999 | 1.000 | 1.000 | 0.970 | 0.957 | 0.964 | 74.6% | 92.6% | 72.3% |

Macro (mean of per-fixture values):

| lang | tool | accuracy | pair P | pair R | pair F1 | span P | span R | span F1 |
|---|---|---|---|---|---|---|---|---|
| c | difffold | 0.992 | 0.991 | 0.990 | 0.991 | 0.979 | 0.971 | 0.973 |
| go | difffold | 0.996 | 0.997 | 0.997 | 0.997 | 0.990 | 0.991 | 0.990 |
| java | difffold | 0.996 | 0.997 | 0.999 | 0.998 | 0.981 | 0.991 | 0.983 |
| javascript | difffold | 0.984 | 0.991 | 0.991 | 0.991 | 0.953 | 0.995 | 0.965 |
| python | difffold | 0.997 | 0.998 | 0.998 | 0.998 | 0.987 | 0.992 | 0.988 |
| rust | difffold | 0.990 | 0.995 | 0.994 | 0.994 | 0.980 | 0.990 | 0.983 |
| tsx | difffold | 0.986 | 0.990 | 0.989 | 0.989 | 0.992 | 0.995 | 0.993 |
| typescript | difffold | 0.993 | 0.994 | 0.992 | 0.993 | 0.988 | 0.996 | 0.991 |
| ALL | difffold | 0.994 | 0.996 | 0.996 | 0.996 | 0.981 | 0.990 | 0.983 |

Unscorable fixtures: 763

### Decisions by cause class (pair, delete and insert decisions; micro)

| class | decisions | fails | accuracy |
|---|---|---|---|
| local_edit | 559 | 39 | 0.930 |
| sibling_ins_del | 42186 | 2441 | 0.942 |
| repeated_children | 3441 | 1122 | 0.674 |
| reorder | 1044 | 180 | 0.828 |
| cross_parent_move | 1101 | 154 | 0.860 |
| wrap_unwrap | 20845 | 2062 | 0.901 |
| wholesale_rewrite | 3983 | 114 | 0.971 |
| context | 5033129 | 783 | 1.000 |
