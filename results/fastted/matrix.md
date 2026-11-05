| regime | shape | nodes A/B | D | difffold ted | difffold ted_within (charged) | APTED (C++) | Touzet baseline ted() (TopDiff path) | Touzet baseline ted_k (charged) | Touzet KR-set ted() | Touzet KR-set ted_k (charged) | Touzet depth-pruning ted() | Touzet depth-pruning ted_k (charged) | X-TED CPU (1 thread) | X-TED CPU (4 threads) |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| mutation | balanced | 100 / 100 | 1 | 0.04 ms | 0.06 ms | 1.90 ms | 0.10 ms | 0.13 ms | 0.09 ms | 0.12 ms | 0.09 ms | 0.12 ms | 0.87 ms | 2.01 ms |
| mutation | balanced | 1000 / 1002 | 10 | 5.10 ms | 7.34 ms | 430.44 ms | 7.31 ms | 10.54 ms | 5.18 ms | 8.17 ms | 6.53 ms | 9.46 ms | 128.50 ms | 115.50 ms |
| mutation | balanced | 5000 / 4996 | 50 | 183.77 ms | 264.58 ms | 20882.42 ms | 347.12 ms | 289.05 ms | 201.28 ms | 266.36 ms | 364.59 ms | 306.90 ms | 7153.18 ms | 4779.23 ms |
| mutation | chain | 100 / 100 | 1 | 0.04 ms | 0.06 ms | 0.91 ms | 0.70 ms | 0.69 ms | 0.46 ms | 0.47 ms | 0.50 ms | 0.53 ms | 0.16 ms | 0.33 ms |
| mutation | chain | 1000 / 1000 | 8 | 0.70 ms | 1.22 ms | 146.30 ms | 1158.65 ms | 876.27 ms | 67.14 ms | above_tau (tool reported distance above tau) | 85.98 ms | 77.52 ms | 18.12 ms | 29.73 ms |
| mutation | chain | 5000 / 5003 | 34 | 20.57 ms | 40.36 ms | 7009.13 ms | n/a | n/a | 4836.94 ms | above_tau (tool reported distance above tau) | n/a | 9329.54 ms | 1425.65 ms | 956.62 ms |
| mutation | lcomb | 100 / 100 | 1 | 0.04 ms | 0.05 ms | 0.60 ms | 0.27 ms | 0.36 ms | 0.22 ms | 0.22 ms | 0.20 ms | 0.26 ms | 25.27 ms | 23.14 ms |
| mutation | lcomb | 1000 / 998 | 10 | 1.82 ms | 2.96 ms | 193.84 ms | 1370.27 ms | 624.99 ms | 46.41 ms | 54.43 ms | 111.28 ms | 76.77 ms | n/a | n/a |
| mutation | lcomb | 5000 / 5011 | 50 | 199.88 ms | 273.45 ms | 4061.32 ms | n/a | n/a | 1695.09 ms | above_tau (tool reported distance above tau) | n/a | n/a | n/a | n/a |
| mutation | rcomb | 100 / 100 | 1 | 0.03 ms | 0.15 ms | 0.75 ms | 0.34 ms | 0.39 ms | 0.38 ms | 0.42 ms | 0.32 ms | 0.44 ms | 0.41 ms | 3.41 ms |
| mutation | rcomb | 1000 / 999 | 10 | 2.24 ms | 364.12 ms | 76.77 ms | 1095.81 ms | 375.10 ms | 999.38 ms | above_tau (tool reported distance above tau) | 80.67 ms | 40.96 ms | 28.45 ms | 54.51 ms |
| mutation | rcomb | 5000 / 4996 | 50 | 100.49 ms | skipped (no completed timed run (killed or error)) | 4299.99 ms | n/a | n/a | n/a | n/a | n/a | 5377.21 ms | 1925.05 ms | 2121.44 ms |
| mutation | star | 100 / 99 | 1 | 0.06 ms | 0.11 ms | 0.65 ms | 0.04 ms | 0.10 ms | 0.06 ms | 0.12 ms | 0.05 ms | 0.11 ms | 0.49 ms | 4.05 ms |
| mutation | star | 1000 / 1000 | 10 | 8.01 ms | 11.70 ms | 66.08 ms | 2.79 ms | 9.06 ms | 5.46 ms | 9.69 ms | 3.33 ms | 9.42 ms | 63.57 ms | 78.13 ms |
| mutation | star | 5000 / 4997 | 49 | 226.58 ms | 303.85 ms | 4297.89 ms | 52.76 ms | 253.32 ms | 97.18 ms | 268.81 ms | 68.26 ms | 252.16 ms | 2171.86 ms | 2226.95 ms |
| real AST | java-ast | 77 / 77 | 1 | 0.03 ms | 0.06 ms | 1.41 ms | 0.07 ms | 0.10 ms | 0.07 ms | 0.11 ms | 0.08 ms | 0.10 ms | 0.68 ms | 1.68 ms |
| real AST | java-ast | 80 / 87 | 7 | 0.15 ms | 0.32 ms | 1.56 ms | 0.15 ms | 0.30 ms | 0.21 ms | 0.34 ms | 0.17 ms | 0.31 ms | 0.65 ms | 3.18 ms |
| real AST | java-ast | 655 / 701 | 46 | 11.90 ms | 25.97 ms | 125.60 ms | 5.85 ms | 17.69 ms | 6.44 ms | 17.90 ms | 6.44 ms | 18.15 ms | 52.92 ms | 47.60 ms |
| real AST | java-ast | 952 / 1053 | 102 | 91.75 ms | 145.87 ms | 292.61 ms | 18.55 ms | 109.89 ms | 19.32 ms | 111.11 ms | 21.60 ms | 111.36 ms | 124.80 ms | 104.75 ms |
| real AST | java-ast | 1070 / 1067 | 10 | 11.76 ms | 18.42 ms | 627.39 ms | 10.79 ms | 16.91 ms | 12.47 ms | 17.31 ms | 11.82 ms | 17.00 ms | 200.85 ms | 179.24 ms |
| real AST | java-ast | 1236 / 1248 | 25 | 22.56 ms | 36.98 ms | 634.02 ms | 14.26 ms | 33.63 ms | 16.79 ms | 34.07 ms | 18.54 ms | 34.91 ms | 251.46 ms | 193.93 ms |
| real AST | java-ast | 2763 / 3131 | 370 | 1037.97 ms | 1758.87 ms | 3754.04 ms | 1866.66 ms | 1324.97 ms | 1665.54 ms | 1403.15 ms | 1862.96 ms | 1391.84 ms | 1368.88 ms | 1042.79 ms |
| real AST | java-ast | 4590 / 4609 | 36 | 155.56 ms | 261.90 ms | 10588.73 ms | 93.12 ms | 219.29 ms | 96.09 ms | 219.40 ms | 112.24 ms | 219.57 ms | 3870.34 ms | 3190.79 ms |
| real AST | java-ast | 4613 / 4622 | 9 | 28.39 ms | 64.40 ms | n/a | 29.74 ms | 56.96 ms | 31.61 ms | 58.63 ms | 29.38 ms | 57.52 ms | 9317.60 ms | 3440.10 ms |
| real AST | java-ast | 5958 / 5982 | 24 | 70.98 ms | 165.46 ms | 17984.86 ms | 31.31 ms | 100.41 ms | 40.92 ms | 108.17 ms | 55.60 ms | 106.24 ms | 7498.26 ms | 5314.61 ms |
| unrelated | balanced | 100 / 100 | 123 | 1.07 ms | 1.63 ms | 1.63 ms | 6.23 ms | 4.30 ms | 3.02 ms | 2.48 ms | 7.04 ms | 4.79 ms | 0.99 ms | 48.15 ms |
| unrelated | balanced | 1000 / 1000 | 1202 | 446.49 ms | 597.50 ms | 497.93 ms | 2632.30 ms | 1222.23 ms | 1011.09 ms | 771.98 ms | 3213.73 ms | 1418.07 ms | 224.11 ms | 169.33 ms |
| unrelated | balanced | 5000 / 5000 | 6002 | 33119.37 ms | 52188.49 ms | skipped (a run exceeded 60 s) | n/a | n/a | n/a | n/a | n/a | n/a | n/a | 8043.05 ms |
| unrelated | chain | 100 / 100 | 186 | 0.30 ms | 0.58 ms | 1.48 ms | 154.17 ms | 171.43 ms | 11.23 ms | 1.86 ms | 163.27 ms | 102.76 ms | 0.31 ms | 0.83 ms |
| unrelated | chain | 1000 / 1000 | 1970 | 190.04 ms | 385.20 ms | 558.83 ms | n/a | n/a | 844.69 ms | 617.50 ms | n/a | n/a | 197.49 ms | 61.90 ms |
| unrelated | chain | 5000 / 5000 | 9962 | 7538.13 ms | 14314.86 ms | n/a | n/a | n/a | n/a | 11831.98 ms | n/a | n/a | 5716.87 ms | 1781.80 ms |
| unrelated | lcomb | 100 / 100 | 130 | 0.57 ms | 0.93 ms | 0.93 ms | 104.38 ms | 54.88 ms | 12.92 ms | 2.03 ms | 104.90 ms | 37.98 ms | 11.37 ms | 9.79 ms |
| unrelated | lcomb | 1000 / 1000 | 1377 | 192.84 ms | 342.12 ms | 241.29 ms | n/a | n/a | 422.35 ms | 350.75 ms | n/a | n/a | 6687.88 ms | 4153.10 ms |
| unrelated | lcomb | 5000 / 5000 | 6900 | 3581.53 ms | 6067.44 ms | 5028.71 ms | n/a | n/a | n/a | 8639.11 ms | n/a | n/a | n/a | n/a |
| unrelated | rcomb | 100 / 100 | 138 | 0.59 ms | 5.33 ms | 1.03 ms | 26.72 ms | 8.66 ms | 20.84 ms | 7.55 ms | 29.81 ms | 9.99 ms | 0.47 ms | 1.47 ms |
| unrelated | rcomb | 1000 / 1000 | 1391 | 109.73 ms | 7681.00 ms | 136.26 ms | n/a | n/a | n/a | 8139.88 ms | n/a | n/a | 60.47 ms | 61.36 ms |
| unrelated | rcomb | 5000 / 5000 | 6908 | 5309.85 ms | skipped (no completed timed run (killed or error)) | 7019.37 ms | n/a | n/a | n/a | n/a | n/a | n/a | 7147.88 ms | 2250.23 ms |
| unrelated | star | 100 / 100 | 128 | 0.63 ms | 1.05 ms | 1.02 ms | 7.41 ms | 2.51 ms | 11.49 ms | 1.67 ms | 10.48 ms | 2.00 ms | 0.67 ms | 1.20 ms |
| unrelated | star | 1000 / 1000 | 1237 | 264.29 ms | 407.35 ms | 221.67 ms | 1439.53 ms | 597.07 ms | 1256.53 ms | 635.41 ms | 1843.96 ms | 710.06 ms | 157.45 ms | 66.45 ms |
| unrelated | star | 5000 / 5000 | 6146 | 10022.43 ms | 16682.03 ms | n/a | n/a | n/a | n/a | n/a | n/a | n/a | 8707.28 ms | 3330.01 ms |
