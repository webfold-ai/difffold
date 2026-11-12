Percentile bootstrap, 2000 resamples of 998 fixtures, seed 1. 95% interval.

| tool | micro pair F1 | micro changed-span F1 | perfect fixtures |
|---|---|---|---|
| difffold | 0.9995 [0.9993, 0.9997] | 0.9649 [0.9535, 0.9752] | 0.7525 [0.7265, 0.7796] |
| omnidiff | 0.9997 [0.9995, 0.9998] | 0.9729 [0.9629, 0.9819] | 0.8206 [0.7976, 0.8437] |
| difffold-baseline | 0.9980 [0.9973, 0.9985] | 0.8437 [0.7992, 0.8801] | 0.5681 [0.5391, 0.5982] |

Paired difference difffold minus omnidiff (same resamples):

| metric | difference |
|---|---|
| micro pair F1 | -0.0001 [-0.0003, -0.0000] |
| micro changed-span F1 | -0.0080 [-0.0170, +0.0010] |
| perfect fixtures | -0.0681 [-0.0892, -0.0481] |
