# Accuracy against hand-authored ground truth (difffold only)

### All scorable fixtures

Micro (sums over fixtures):

| lang | tool | fixtures | node-corr. accuracy | pair P | pair R | pair F1 | span P | span R | span F1 | perfect | near-perfect | strict perfect |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| c | difffold | 88 | 0.997 | 0.999 | 0.998 | 0.998 | 0.632 | 0.937 | 0.755 | 67.0% | 89.8% | 67.0% |
| go | difffold | 79 | 0.997 | 0.999 | 0.998 | 0.998 | 0.846 | 0.997 | 0.915 | 65.8% | 84.8% | 65.8% |
| java | difffold | 515 | 0.997 | 0.999 | 0.997 | 0.998 | 0.709 | 0.983 | 0.824 | 51.8% | 88.0% | 51.7% |
| javascript | difffold | 50 | 0.998 | 1.000 | 0.998 | 0.999 | 0.688 | 0.991 | 0.812 | 64.0% | 74.0% | 64.0% |
| python | difffold | 71 | 0.996 | 0.999 | 0.998 | 0.998 | 0.809 | 0.947 | 0.873 | 71.8% | 88.7% | 71.8% |
| rust | difffold | 111 | 0.996 | 0.999 | 0.997 | 0.998 | 0.760 | 0.989 | 0.860 | 56.8% | 82.0% | 56.8% |
| tsx | difffold | 41 | 0.996 | 0.999 | 0.997 | 0.998 | 0.715 | 0.986 | 0.829 | 68.3% | 85.4% | 68.3% |
| typescript | difffold | 43 | 0.999 | 1.000 | 0.999 | 1.000 | 0.876 | 1.000 | 0.934 | 88.4% | 93.0% | 88.4% |
| ALL | difffold | 998 | 0.997 | 0.999 | 0.997 | 0.998 | 0.741 | 0.980 | 0.844 | 59.1% | 86.7% | 59.0% |

Macro (mean of per-fixture values):

| lang | tool | accuracy | pair P | pair R | pair F1 | span P | span R | span F1 |
|---|---|---|---|---|---|---|---|---|
| c | difffold | 0.985 | 0.982 | 0.970 | 0.974 | 0.867 | 0.980 | 0.896 |
| go | difffold | 0.986 | 0.993 | 0.985 | 0.989 | 0.884 | 0.994 | 0.911 |
| java | difffold | 0.989 | 0.996 | 0.991 | 0.993 | 0.838 | 0.984 | 0.872 |
| javascript | difffold | 0.953 | 0.983 | 0.954 | 0.965 | 0.865 | 0.996 | 0.895 |
| python | difffold | 0.988 | 0.999 | 0.986 | 0.991 | 0.895 | 0.994 | 0.916 |
| rust | difffold | 0.973 | 0.989 | 0.973 | 0.980 | 0.861 | 0.984 | 0.888 |
| tsx | difffold | 0.987 | 0.996 | 0.988 | 0.992 | 0.871 | 0.999 | 0.898 |
| typescript | difffold | 0.986 | 0.992 | 0.977 | 0.983 | 0.952 | 1.000 | 0.963 |
| ALL | difffold | 0.984 | 0.993 | 0.984 | 0.988 | 0.859 | 0.987 | 0.888 |

### Excluding wholesale-rewrite fixtures

Micro (sums over fixtures):

| lang | tool | fixtures | node-corr. accuracy | pair P | pair R | pair F1 | span P | span R | span F1 | perfect | near-perfect | strict perfect |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| c | difffold | 86 | 0.997 | 0.999 | 0.998 | 0.999 | 0.614 | 0.940 | 0.743 | 68.6% | 90.7% | 68.6% |
| go | difffold | 79 | 0.997 | 0.999 | 0.998 | 0.998 | 0.846 | 0.997 | 0.915 | 65.8% | 84.8% | 65.8% |
| java | difffold | 514 | 0.997 | 0.999 | 0.997 | 0.998 | 0.702 | 0.982 | 0.819 | 51.8% | 87.9% | 51.6% |
| javascript | difffold | 50 | 0.998 | 1.000 | 0.998 | 0.999 | 0.688 | 0.991 | 0.812 | 64.0% | 74.0% | 64.0% |
| python | difffold | 71 | 0.996 | 0.999 | 0.998 | 0.998 | 0.809 | 0.947 | 0.873 | 71.8% | 88.7% | 71.8% |
| rust | difffold | 110 | 0.996 | 0.999 | 0.997 | 0.998 | 0.759 | 0.990 | 0.859 | 57.3% | 81.8% | 57.3% |
| tsx | difffold | 41 | 0.996 | 0.999 | 0.997 | 0.998 | 0.715 | 0.986 | 0.829 | 68.3% | 85.4% | 68.3% |
| typescript | difffold | 43 | 0.999 | 1.000 | 0.999 | 1.000 | 0.876 | 1.000 | 0.934 | 88.4% | 93.0% | 88.4% |
| ALL | difffold | 994 | 0.997 | 0.999 | 0.997 | 0.998 | 0.737 | 0.980 | 0.841 | 59.3% | 86.7% | 59.2% |

Macro (mean of per-fixture values):

| lang | tool | accuracy | pair P | pair R | pair F1 | span P | span R | span F1 |
|---|---|---|---|---|---|---|---|---|
| c | difffold | 0.988 | 0.991 | 0.983 | 0.986 | 0.865 | 0.981 | 0.894 |
| go | difffold | 0.986 | 0.993 | 0.985 | 0.989 | 0.884 | 0.994 | 0.911 |
| java | difffold | 0.989 | 0.996 | 0.991 | 0.993 | 0.838 | 0.984 | 0.871 |
| javascript | difffold | 0.953 | 0.983 | 0.954 | 0.965 | 0.865 | 0.996 | 0.895 |
| python | difffold | 0.988 | 0.999 | 0.986 | 0.991 | 0.895 | 0.994 | 0.916 |
| rust | difffold | 0.973 | 0.989 | 0.972 | 0.979 | 0.860 | 0.984 | 0.887 |
| tsx | difffold | 0.987 | 0.996 | 0.988 | 0.992 | 0.871 | 0.999 | 0.898 |
| typescript | difffold | 0.986 | 0.992 | 0.977 | 0.983 | 0.952 | 1.000 | 0.963 |
| ALL | difffold | 0.985 | 0.994 | 0.985 | 0.989 | 0.858 | 0.987 | 0.888 |

Unscorable fixtures: 763

### Decisions by cause class (pair, delete and insert decisions; micro)

| class | decisions | fails | accuracy |
|---|---|---|---|
| local_edit | 559 | 37 | 0.934 |
| sibling_ins_del | 42186 | 1679 | 0.960 |
| repeated_children | 3671 | 1334 | 0.637 |
| reorder | 1044 | 1009 | 0.034 |
| cross_parent_move | 1101 | 896 | 0.186 |
| wrap_unwrap | 20845 | 10576 | 0.493 |
| wholesale_rewrite | 3983 | 93 | 0.977 |
| context | 5033129 | 1244 | 1.000 |
