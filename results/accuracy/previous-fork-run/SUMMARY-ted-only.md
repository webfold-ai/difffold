# Accuracy against hand-authored ground truth (difffold general tree edit mapping, trees over 20000 nodes fall back to the top-down mapping)

### All scorable fixtures

Micro (sums over fixtures):

| lang | tool | fixtures | node-corr. accuracy | pair P | pair R | pair F1 | span P | span R | span F1 | perfect | near-perfect | strict perfect |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| c | difffold | 88 | 0.997 | 0.998 | 0.998 | 0.998 | 0.667 | 0.896 | 0.765 | 70.5% | 89.8% | 70.5% |
| go | difffold | 79 | 0.999 | 0.999 | 0.999 | 0.999 | 0.967 | 0.996 | 0.981 | 73.4% | 91.1% | 72.2% |
| java | difffold | 515 | 0.998 | 0.999 | 0.999 | 0.999 | 0.903 | 0.975 | 0.938 | 60.2% | 93.0% | 58.3% |
| javascript | difffold | 53 | 0.999 | 0.999 | 1.000 | 1.000 | 0.931 | 0.985 | 0.957 | 67.9% | 79.2% | 66.0% |
| python | difffold | 71 | 0.998 | 0.999 | 0.999 | 0.999 | 0.966 | 0.958 | 0.962 | 81.7% | 91.5% | 81.7% |
| rust | difffold | 111 | 0.997 | 0.999 | 0.999 | 0.999 | 0.925 | 0.975 | 0.950 | 60.4% | 84.7% | 58.6% |
| tsx | difffold | 41 | 0.997 | 0.999 | 0.998 | 0.999 | 0.864 | 0.986 | 0.921 | 68.3% | 85.4% | 68.3% |
| typescript | difffold | 43 | 1.000 | 1.000 | 1.000 | 1.000 | 0.995 | 0.995 | 0.995 | 90.7% | 97.7% | 90.7% |
| ALL | difffold | 1001 | 0.998 | 0.999 | 0.999 | 0.999 | 0.903 | 0.971 | 0.936 | 65.7% | 90.7% | 64.3% |

Macro (mean of per-fixture values):

| lang | tool | accuracy | pair P | pair R | pair F1 | span P | span R | span F1 |
|---|---|---|---|---|---|---|---|---|
| c | difffold | 0.975 | 0.965 | 0.970 | 0.966 | 0.905 | 0.974 | 0.921 |
| go | difffold | 0.993 | 0.996 | 0.996 | 0.996 | 0.956 | 0.992 | 0.965 |
| java | difffold | 0.993 | 0.995 | 0.998 | 0.996 | 0.952 | 0.986 | 0.959 |
| javascript | difffold | 0.970 | 0.977 | 0.989 | 0.983 | 0.964 | 0.992 | 0.973 |
| python | difffold | 0.994 | 0.995 | 0.999 | 0.997 | 0.975 | 0.995 | 0.977 |
| rust | difffold | 0.981 | 0.987 | 0.987 | 0.987 | 0.938 | 0.989 | 0.951 |
| tsx | difffold | 0.978 | 0.983 | 0.984 | 0.984 | 0.925 | 0.999 | 0.937 |
| typescript | difffold | 0.993 | 0.994 | 0.997 | 0.995 | 0.991 | 0.998 | 0.993 |
| ALL | difffold | 0.988 | 0.990 | 0.993 | 0.991 | 0.950 | 0.988 | 0.958 |

### Excluding wholesale-rewrite fixtures

Micro (sums over fixtures):

| lang | tool | fixtures | node-corr. accuracy | pair P | pair R | pair F1 | span P | span R | span F1 | perfect | near-perfect | strict perfect |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| c | difffold | 86 | 0.997 | 0.999 | 0.998 | 0.998 | 0.652 | 0.907 | 0.759 | 72.1% | 90.7% | 72.1% |
| go | difffold | 79 | 0.999 | 0.999 | 0.999 | 0.999 | 0.967 | 0.996 | 0.981 | 73.4% | 91.1% | 72.2% |
| java | difffold | 514 | 0.998 | 0.999 | 0.999 | 0.999 | 0.900 | 0.974 | 0.936 | 60.3% | 93.0% | 58.4% |
| javascript | difffold | 53 | 0.999 | 0.999 | 1.000 | 1.000 | 0.931 | 0.985 | 0.957 | 67.9% | 79.2% | 66.0% |
| python | difffold | 71 | 0.998 | 0.999 | 0.999 | 0.999 | 0.966 | 0.958 | 0.962 | 81.7% | 91.5% | 81.7% |
| rust | difffold | 110 | 0.997 | 0.999 | 0.999 | 0.999 | 0.925 | 0.975 | 0.950 | 60.9% | 84.5% | 59.1% |
| tsx | difffold | 41 | 0.997 | 0.999 | 0.998 | 0.999 | 0.864 | 0.986 | 0.921 | 68.3% | 85.4% | 68.3% |
| typescript | difffold | 43 | 1.000 | 1.000 | 1.000 | 1.000 | 0.995 | 0.995 | 0.995 | 90.7% | 97.7% | 90.7% |
| ALL | difffold | 997 | 0.998 | 0.999 | 0.999 | 0.999 | 0.902 | 0.972 | 0.936 | 66.0% | 90.8% | 64.6% |

Macro (mean of per-fixture values):

| lang | tool | accuracy | pair P | pair R | pair F1 | span P | span R | span F1 |
|---|---|---|---|---|---|---|---|---|
| c | difffold | 0.984 | 0.985 | 0.984 | 0.984 | 0.904 | 0.976 | 0.921 |
| go | difffold | 0.993 | 0.996 | 0.996 | 0.996 | 0.956 | 0.992 | 0.965 |
| java | difffold | 0.993 | 0.995 | 0.998 | 0.996 | 0.952 | 0.986 | 0.959 |
| javascript | difffold | 0.970 | 0.977 | 0.989 | 0.983 | 0.964 | 0.992 | 0.973 |
| python | difffold | 0.994 | 0.995 | 0.999 | 0.997 | 0.975 | 0.995 | 0.977 |
| rust | difffold | 0.980 | 0.987 | 0.987 | 0.987 | 0.938 | 0.989 | 0.951 |
| tsx | difffold | 0.978 | 0.983 | 0.984 | 0.984 | 0.925 | 0.999 | 0.937 |
| typescript | difffold | 0.993 | 0.994 | 0.997 | 0.995 | 0.991 | 0.998 | 0.993 |
| ALL | difffold | 0.989 | 0.992 | 0.994 | 0.993 | 0.950 | 0.988 | 0.958 |

Unscorable fixtures: 748
