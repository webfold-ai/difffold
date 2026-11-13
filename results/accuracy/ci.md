Percentile bootstrap, 10000 resamples of 998 fixtures, seed 1. 95% interval.

| tool | micro pair F1 | micro changed-span F1 | perfect fixtures |
|---|---|---|---|
| difffold | 0.9995 [0.9993, 0.9997] | 0.9649 [0.9525, 0.9752] | 0.7525 [0.7265, 0.7786] |
| omnidiff | 0.9997 [0.9995, 0.9998] | 0.9729 [0.9625, 0.9815] | 0.8206 [0.7966, 0.8447] |
| difffold-baseline | 0.9980 [0.9973, 0.9985] | 0.8437 [0.7990, 0.8808] | 0.5681 [0.5381, 0.5982] |

Paired difference difffold minus omnidiff (same resamples):

| metric | difference |
|---|---|
| micro pair F1 | -0.0001 [-0.0003, -0.0000] |
| micro changed-span F1 | -0.0080 [-0.0175, +0.0013] |
| perfect fixtures | -0.0681 [-0.0892, -0.0471] |
