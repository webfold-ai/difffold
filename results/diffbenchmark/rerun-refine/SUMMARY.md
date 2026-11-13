996 oracle files completed by all of RMD, GTG, GTS, DFT_TD, DFT_RF; percentile bootstrap over files, 10000 resamples, seed 1.

| tool | TP raw | FP | FN | precision (raw) | recall (raw) | F1 (raw) [95% interval] | perfect files |
|---|---|---|---|---|---|---|---|
| RMD | 596954 | 140 | 315 | 0.9998 | 0.9995 | 0.9996 [0.9995, 0.9997] | 881 (88.5%) |
| GTG | 593907 | 1139 | 3362 | 0.9981 | 0.9944 | 0.9962 [0.9958, 0.9966] | 209 (21.0%) |
| GTS | 596209 | 761 | 1060 | 0.9987 | 0.9982 | 0.9985 [0.9982, 0.9987] | 649 (65.2%) |
| DFT_TD | 595302 | 1686 | 1967 | 0.9972 | 0.9967 | 0.9969 [0.9963, 0.9975] | 449 (45.1%) |
| DFT_RF | 596565 | 987 | 704 | 0.9983 | 0.9988 | 0.9986 [0.9983, 0.9988] | 641 (64.4%) |

Paired F1 difference of DFT_RF to each other tool (same resamples):

| tool | difference | 95% interval |
|---|---|---|
| RMD | -0.00103 | [-0.00129, -0.00081] |
| GTG | +0.00236 | [+0.00209, +0.00265] |
| GTS | +0.00011 | [-0.00005, +0.00027] |
| DFT_TD | +0.00164 | [+0.00123, +0.00210] |
