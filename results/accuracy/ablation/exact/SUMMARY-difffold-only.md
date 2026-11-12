# Accuracy against hand-authored ground truth (difffold only)

### All scorable fixtures

Micro (sums over fixtures):

| lang | tool | fixtures | node-corr. accuracy | pair P | pair R | pair F1 | span P | span R | span F1 | perfect | near-perfect | strict perfect |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| c | difffold | 88 | 0.998 | 0.999 | 0.999 | 0.999 | 0.877 | 0.887 | 0.882 | 70.5% | 92.0% | 70.5% |
| go | difffold | 79 | 0.999 | 1.000 | 1.000 | 1.000 | 0.989 | 0.986 | 0.988 | 72.2% | 96.2% | 72.2% |
| java | difffold | 515 | 0.999 | 1.000 | 1.000 | 1.000 | 0.951 | 0.964 | 0.957 | 68.5% | 94.6% | 68.2% |
| javascript | difffold | 50 | 0.999 | 1.000 | 1.000 | 1.000 | 0.915 | 0.991 | 0.951 | 68.0% | 80.0% | 68.0% |
| python | difffold | 71 | 0.998 | 0.999 | 1.000 | 1.000 | 0.960 | 0.946 | 0.953 | 78.9% | 94.4% | 78.9% |
| rust | difffold | 111 | 0.998 | 0.999 | 0.999 | 0.999 | 0.957 | 0.977 | 0.967 | 60.4% | 85.6% | 60.4% |
| tsx | difffold | 41 | 0.999 | 1.000 | 0.999 | 1.000 | 0.925 | 0.986 | 0.954 | 70.7% | 87.8% | 70.7% |
| typescript | difffold | 43 | 1.000 | 1.000 | 1.000 | 1.000 | 0.984 | 1.000 | 0.992 | 90.7% | 95.3% | 90.7% |
| ALL | difffold | 998 | 0.999 | 1.000 | 0.999 | 1.000 | 0.952 | 0.965 | 0.958 | 69.8% | 92.5% | 69.6% |

Macro (mean of per-fixture values):

| lang | tool | accuracy | pair P | pair R | pair F1 | span P | span R | span F1 |
|---|---|---|---|---|---|---|---|---|
| c | difffold | 0.988 | 0.982 | 0.976 | 0.978 | 0.945 | 0.974 | 0.953 |
| go | difffold | 0.996 | 0.997 | 0.997 | 0.997 | 0.977 | 0.993 | 0.983 |
| java | difffold | 0.995 | 0.997 | 0.999 | 0.998 | 0.965 | 0.994 | 0.974 |
| javascript | difffold | 0.985 | 0.993 | 0.989 | 0.991 | 0.920 | 0.996 | 0.945 |
| python | difffold | 0.998 | 0.999 | 0.997 | 0.998 | 0.963 | 0.995 | 0.973 |
| rust | difffold | 0.989 | 0.995 | 0.993 | 0.994 | 0.952 | 0.991 | 0.965 |
| tsx | difffold | 0.985 | 0.990 | 0.988 | 0.989 | 0.950 | 0.999 | 0.961 |
| typescript | difffold | 0.994 | 0.995 | 0.992 | 0.993 | 0.987 | 1.000 | 0.992 |
| ALL | difffold | 0.993 | 0.995 | 0.995 | 0.995 | 0.961 | 0.992 | 0.971 |

### Excluding wholesale-rewrite fixtures

Micro (sums over fixtures):

| lang | tool | fixtures | node-corr. accuracy | pair P | pair R | pair F1 | span P | span R | span F1 | perfect | near-perfect | strict perfect |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| c | difffold | 86 | 0.999 | 0.999 | 0.999 | 0.999 | 0.871 | 0.893 | 0.882 | 72.1% | 93.0% | 72.1% |
| go | difffold | 79 | 0.999 | 1.000 | 1.000 | 1.000 | 0.989 | 0.986 | 0.988 | 72.2% | 96.2% | 72.2% |
| java | difffold | 514 | 0.999 | 1.000 | 1.000 | 1.000 | 0.949 | 0.963 | 0.956 | 68.5% | 94.6% | 68.1% |
| javascript | difffold | 50 | 0.999 | 1.000 | 1.000 | 1.000 | 0.915 | 0.991 | 0.951 | 68.0% | 80.0% | 68.0% |
| python | difffold | 71 | 0.998 | 0.999 | 1.000 | 1.000 | 0.960 | 0.946 | 0.953 | 78.9% | 94.4% | 78.9% |
| rust | difffold | 110 | 0.998 | 0.999 | 0.999 | 0.999 | 0.957 | 0.977 | 0.967 | 60.9% | 85.5% | 60.9% |
| tsx | difffold | 41 | 0.999 | 1.000 | 0.999 | 1.000 | 0.925 | 0.986 | 0.954 | 70.7% | 87.8% | 70.7% |
| typescript | difffold | 43 | 1.000 | 1.000 | 1.000 | 1.000 | 0.984 | 1.000 | 0.992 | 90.7% | 95.3% | 90.7% |
| ALL | difffold | 994 | 0.999 | 1.000 | 0.999 | 1.000 | 0.951 | 0.965 | 0.958 | 70.0% | 92.6% | 69.8% |

Macro (mean of per-fixture values):

| lang | tool | accuracy | pair P | pair R | pair F1 | span P | span R | span F1 |
|---|---|---|---|---|---|---|---|---|
| c | difffold | 0.992 | 0.991 | 0.990 | 0.990 | 0.945 | 0.975 | 0.954 |
| go | difffold | 0.996 | 0.997 | 0.997 | 0.997 | 0.977 | 0.993 | 0.983 |
| java | difffold | 0.995 | 0.997 | 0.999 | 0.998 | 0.965 | 0.994 | 0.974 |
| javascript | difffold | 0.985 | 0.993 | 0.989 | 0.991 | 0.920 | 0.996 | 0.945 |
| python | difffold | 0.998 | 0.999 | 0.997 | 0.998 | 0.963 | 0.995 | 0.973 |
| rust | difffold | 0.989 | 0.995 | 0.993 | 0.994 | 0.952 | 0.991 | 0.965 |
| tsx | difffold | 0.985 | 0.990 | 0.988 | 0.989 | 0.950 | 0.999 | 0.961 |
| typescript | difffold | 0.994 | 0.995 | 0.992 | 0.993 | 0.987 | 1.000 | 0.992 |
| ALL | difffold | 0.994 | 0.996 | 0.996 | 0.996 | 0.961 | 0.993 | 0.971 |

Unscorable fixtures: 763

### Decisions by cause class (pair, delete and insert decisions; micro)

| class | decisions | fails | accuracy |
|---|---|---|---|
| local_edit | 559 | 39 | 0.930 |
| sibling_ins_del | 42186 | 1975 | 0.953 |
| repeated_children | 3466 | 1111 | 0.679 |
| reorder | 1044 | 276 | 0.736 |
| cross_parent_move | 1101 | 203 | 0.816 |
| wrap_unwrap | 20845 | 2230 | 0.893 |
| wholesale_rewrite | 3983 | 106 | 0.973 |
| context | 5033129 | 702 | 1.000 |
