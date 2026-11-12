# Accuracy against hand-authored ground truth (difffold only)

### All scorable fixtures

Micro (sums over fixtures):

| lang | tool | fixtures | node-corr. accuracy | pair P | pair R | pair F1 | span P | span R | span F1 | perfect | near-perfect | strict perfect |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| c | difffold | 88 | 0.998 | 0.999 | 0.999 | 0.999 | 0.915 | 0.870 | 0.892 | 75.0% | 93.2% | 73.9% |
| go | difffold | 79 | 0.999 | 1.000 | 1.000 | 1.000 | 0.995 | 0.983 | 0.989 | 73.4% | 98.7% | 73.4% |
| java | difffold | 515 | 0.999 | 0.999 | 1.000 | 1.000 | 0.975 | 0.956 | 0.965 | 75.9% | 93.8% | 71.7% |
| javascript | difffold | 50 | 0.999 | 1.000 | 1.000 | 1.000 | 0.947 | 0.985 | 0.965 | 72.0% | 82.0% | 72.0% |
| python | difffold | 71 | 0.998 | 0.999 | 1.000 | 0.999 | 0.975 | 0.928 | 0.951 | 80.3% | 91.5% | 78.9% |
| rust | difffold | 111 | 0.998 | 0.999 | 0.999 | 0.999 | 0.980 | 0.969 | 0.974 | 66.7% | 87.4% | 64.9% |
| tsx | difffold | 41 | 0.999 | 1.000 | 0.999 | 1.000 | 0.975 | 0.981 | 0.978 | 73.2% | 87.8% | 73.2% |
| typescript | difffold | 43 | 1.000 | 1.000 | 1.000 | 1.000 | 0.989 | 0.989 | 0.989 | 90.7% | 95.3% | 90.7% |
| ALL | difffold | 998 | 0.999 | 0.999 | 1.000 | 1.000 | 0.974 | 0.956 | 0.965 | 75.3% | 92.5% | 72.6% |

Macro (mean of per-fixture values):

| lang | tool | accuracy | pair P | pair R | pair F1 | span P | span R | span F1 |
|---|---|---|---|---|---|---|---|---|
| c | difffold | 0.988 | 0.981 | 0.977 | 0.978 | 0.981 | 0.970 | 0.973 |
| go | difffold | 0.996 | 0.998 | 0.997 | 0.997 | 0.992 | 0.990 | 0.991 |
| java | difffold | 0.996 | 0.997 | 0.999 | 0.998 | 0.987 | 0.990 | 0.987 |
| javascript | difffold | 0.984 | 0.991 | 0.991 | 0.991 | 0.953 | 0.995 | 0.965 |
| python | difffold | 0.997 | 0.998 | 0.998 | 0.998 | 0.987 | 0.990 | 0.986 |
| rust | difffold | 0.990 | 0.995 | 0.994 | 0.995 | 0.982 | 0.989 | 0.984 |
| tsx | difffold | 0.986 | 0.990 | 0.989 | 0.989 | 0.998 | 0.995 | 0.997 |
| typescript | difffold | 0.993 | 0.994 | 0.992 | 0.993 | 0.988 | 0.996 | 0.991 |
| ALL | difffold | 0.993 | 0.995 | 0.995 | 0.995 | 0.985 | 0.989 | 0.985 |

### Excluding wholesale-rewrite fixtures

Micro (sums over fixtures):

| lang | tool | fixtures | node-corr. accuracy | pair P | pair R | pair F1 | span P | span R | span F1 | perfect | near-perfect | strict perfect |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| c | difffold | 86 | 0.999 | 0.999 | 0.999 | 0.999 | 0.912 | 0.875 | 0.893 | 76.7% | 94.2% | 75.6% |
| go | difffold | 79 | 0.999 | 1.000 | 1.000 | 1.000 | 0.995 | 0.983 | 0.989 | 73.4% | 98.7% | 73.4% |
| java | difffold | 514 | 0.999 | 0.999 | 1.000 | 1.000 | 0.974 | 0.954 | 0.964 | 75.9% | 93.8% | 71.8% |
| javascript | difffold | 50 | 0.999 | 1.000 | 1.000 | 1.000 | 0.947 | 0.985 | 0.965 | 72.0% | 82.0% | 72.0% |
| python | difffold | 71 | 0.998 | 0.999 | 1.000 | 0.999 | 0.975 | 0.928 | 0.951 | 80.3% | 91.5% | 78.9% |
| rust | difffold | 110 | 0.998 | 0.999 | 0.999 | 0.999 | 0.980 | 0.969 | 0.975 | 67.3% | 87.3% | 65.5% |
| tsx | difffold | 41 | 0.999 | 1.000 | 0.999 | 1.000 | 0.975 | 0.981 | 0.978 | 73.2% | 87.8% | 73.2% |
| typescript | difffold | 43 | 1.000 | 1.000 | 1.000 | 1.000 | 0.989 | 0.989 | 0.989 | 90.7% | 95.3% | 90.7% |
| ALL | difffold | 994 | 0.999 | 0.999 | 1.000 | 1.000 | 0.974 | 0.956 | 0.965 | 75.5% | 92.6% | 72.9% |

Macro (mean of per-fixture values):

| lang | tool | accuracy | pair P | pair R | pair F1 | span P | span R | span F1 |
|---|---|---|---|---|---|---|---|---|
| c | difffold | 0.992 | 0.991 | 0.990 | 0.991 | 0.981 | 0.971 | 0.974 |
| go | difffold | 0.996 | 0.998 | 0.997 | 0.997 | 0.992 | 0.990 | 0.991 |
| java | difffold | 0.996 | 0.997 | 0.999 | 0.998 | 0.987 | 0.990 | 0.987 |
| javascript | difffold | 0.984 | 0.991 | 0.991 | 0.991 | 0.953 | 0.995 | 0.965 |
| python | difffold | 0.997 | 0.998 | 0.998 | 0.998 | 0.987 | 0.990 | 0.986 |
| rust | difffold | 0.990 | 0.995 | 0.994 | 0.994 | 0.982 | 0.989 | 0.984 |
| tsx | difffold | 0.986 | 0.990 | 0.989 | 0.989 | 0.998 | 0.995 | 0.997 |
| typescript | difffold | 0.993 | 0.994 | 0.992 | 0.993 | 0.988 | 0.996 | 0.991 |
| ALL | difffold | 0.994 | 0.996 | 0.996 | 0.996 | 0.985 | 0.989 | 0.985 |

Unscorable fixtures: 763

### Decisions by cause class (pair, delete and insert decisions; micro)

| class | decisions | fails | accuracy |
|---|---|---|---|
| local_edit | 559 | 44 | 0.921 |
| sibling_ins_del | 42186 | 2447 | 0.942 |
| repeated_children | 3439 | 1118 | 0.675 |
| reorder | 1044 | 175 | 0.832 |
| cross_parent_move | 1101 | 154 | 0.860 |
| wrap_unwrap | 20845 | 2035 | 0.902 |
| wholesale_rewrite | 3983 | 124 | 0.969 |
| context | 5033129 | 772 | 1.000 |
