710 oracle files completed by all of RMD, GTG, GTS, DFT_TD, DFT_RF; percentile bootstrap over files, 10000 resamples, seed 1.

| tool | TP raw | FP | FN | precision (raw) | recall (raw) | F1 (raw) [95% interval] | perfect files |
|---|---|---|---|---|---|---|---|
| RMD | 445056 | 104 | 182 | 0.9998 | 0.9996 | 0.9997 [0.9996, 0.9998] | 635 (89.4%) |
| GTG | 442826 | 722 | 2412 | 0.9984 | 0.9946 | 0.9965 [0.9960, 0.9969] | 142 (20.0%) |
| GTS | 444551 | 525 | 687 | 0.9988 | 0.9985 | 0.9986 [0.9983, 0.9989] | 474 (66.8%) |
| DFT_TD | 443793 | 1168 | 1445 | 0.9974 | 0.9968 | 0.9971 [0.9963, 0.9977] | 330 (46.5%) |
| DFT_RF | 444804 | 665 | 434 | 0.9985 | 0.9990 | 0.9988 [0.9984, 0.9990] | 479 (67.5%) |

Paired F1 difference of DFT_RF to each other tool (same resamples):

| tool | difference | 95% interval |
|---|---|---|
| RMD | -0.00091 | [-0.00123, -0.00066] |
| GTG | +0.00229 | [+0.00201, +0.00260] |
| GTS | +0.00013 | [-0.00004, +0.00030] |
| DFT_TD | +0.00170 | [+0.00124, +0.00223] |

