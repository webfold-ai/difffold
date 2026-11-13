Refinement counters summed over 998 fixtures (Options::FULL).

| counter | total | fixtures where it is non-zero | meaning |
|---|---:|---:|---|
| seed | 5171228 | 998 | top-down pairs kept (kind-changing pairs removed) |
| dropped | 2534 | 363 | top-down pairs dropped for changing kind |
| exact | 12385 | 283 | nodes paired by the exact-subtree phase |
| invalid | 259 | 96 | tentative pairs dropped by validate |
| containers | 212 | 59 | container pairs made |
| recovered | 325 | 53 | nodes paired by recover |
| descended | 694 | 176 | leaves paired by descend and retarget |
| orphans | 316 | 99 | leaf pairs dropped by the orphan rule |
