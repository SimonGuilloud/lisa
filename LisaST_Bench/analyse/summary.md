# Benchmark results

11470 rows, 400 problems, configurations: e1a, e1b, e3-time_baseline, e3-time_bwdsubs-off, e3-time_cond-on, e3-time_demod-off, e3-time_fwdsubs-off, e3-time_gensimplify-on, e3-time_index-off, e3-time_sr-and-index-off, e3-time_sr-off, e4_orthologic-off, e4_orthologic-on, e5_sine-off, e5_sine-on

## A1 — strategies and the portfolio

| configuration | strategy | solved |
|---|---|---:|
| e1a | weight-greedy | 132 |
| e1a | equational | 129 |
| e1a | subsumption-light | 127 |
| e1a | occurrence | 122 |
| e1a | unary-redundancy | 118 |
| e1a | balanced | 114 |
| e1a | age-fair | 84 |
| e1a | first-negative | 77 |
| **e1a** | **portfolio** | **196** |

Portfolio solves 196; best single strategy weight-greedy solves 132, so the portfolio adds 64.

| e1b | weight-greedy | 127 |
| e1b | subsumption-light | 123 |
| e1b | equational | 122 |
| e1b | occurrence | 110 |
| e1b | unary-redundancy | 108 |
| e1b | balanced | 106 |
| e1b | first-negative | 76 |
| e1b | age-fair | 69 |
| **e1b** | **portfolio** | **192** |

Portfolio solves 192; best single strategy weight-greedy solves 127, so the portfolio adds 65.

## A2 — solved counts and where the time goes

Solved, and total time over every problem, charging an unsolved one the 180 s budget.

| configuration | solved | total time (s) | clausify | search | reconstruct | check |
|---|---:|---:|---:|---:|---:|---:|
| e1a | 196 | 38741 | 1602 | 11762 | 0 | 0 |
| e1b | 192 | 41484 | 2780 | 11196 | 118 | 7543 |
| e3-time_baseline | 112 | 54299 | 188 | 2295 | 9 | 687 |
| e3-time_bwdsubs-off | 111 | 54368 | 190 | 2181 | 9 | 689 |
| e3-time_cond-on | 104 | 56321 | 147 | 2309 | 8 | 577 |
| e3-time_demod-off | 97 | 56948 | 173 | 1792 | 7 | 615 |
| e3-time_fwdsubs-off | 59 | 62040 | 119 | 887 | 5 | 369 |
| e3-time_gensimplify-on | 99 | 56261 | 166 | 1270 | 8 | 638 |
| e3-time_index-off | 113 | 54410 | 178 | 2427 | 9 | 676 |
| e3-time_sr-and-index-off | 113 | 54754 | 187 | 2379 | 9 | 699 |
| e3-time_sr-off | 114 | 54387 | 190 | 2549 | 9 | 700 |
| e4_orthologic-off | 111 | 54846 | 181 | 2157 | 9 | 659 |
| e4_orthologic-on | 104 | 54486 | 147 | 1775 | 7 | 356 |
| e5_sine-off | 111 | 54479 | 180 | 2161 | 8 | 650 |
| e5_sine-on | 123 | 51832 | 185 | 1855 | 8 | 643 |

Phase columns are summed over that configuration's own refutations, so they say where its time goes, not what it would cost another configuration.

Time compared only where both solved, against `e1a`:

| configuration | both solved | e1a (s) | this (s) | ratio |
|---|---:|---:|---:|---:|
| e1b | 187 | 1701 | 3337 | 1.96x |
| e3-time_baseline | 110 | 534 | 2859 | 5.35x |
| e3-time_bwdsubs-off | 108 | 518 | 2659 | 5.13x |
| e3-time_cond-on | 102 | 465 | 2883 | 6.20x |
| e3-time_demod-off | 96 | 386 | 2428 | 6.29x |
| e3-time_fwdsubs-off | 58 | 154 | 1294 | 8.41x |
| e3-time_gensimplify-on | 97 | 348 | 2044 | 5.87x |
| e3-time_index-off | 110 | 534 | 2810 | 5.26x |
| e3-time_sr-and-index-off | 110 | 534 | 2791 | 5.22x |
| e3-time_sr-off | 111 | 537 | 2998 | 5.58x |
| e4_orthologic-off | 110 | 534 | 2853 | 5.34x |
| e4_orthologic-on | 103 | 490 | 2145 | 4.37x |
| e5_sine-off | 110 | 534 | 2849 | 5.33x |
| e5_sine-on | 122 | 627 | 2535 | 4.04x |

Solved inside the last tenth of the budget, and so able to move between runs:

| configuration | solved | near the boundary |
|---|---:|---:|
| e1a | 196 | 0 |
| e1b | 192 | 1 |
| e3-time_baseline | 112 | 1 |
| e3-time_bwdsubs-off | 111 | 1 |
| e3-time_cond-on | 104 | 2 |
| e3-time_demod-off | 97 | 0 |
| e3-time_fwdsubs-off | 59 | 0 |
| e3-time_gensimplify-on | 99 | 0 |
| e3-time_index-off | 113 | 2 |
| e3-time_sr-and-index-off | 113 | 2 |
| e3-time_sr-off | 114 | 0 |
| e4_orthologic-off | 111 | 0 |
| e4_orthologic-on | 104 | 0 |
| e5_sine-off | 111 | 0 |
| e5_sine-on | 123 | 0 |

## e3-time — against `e3-time_baseline`

| configuration | solved | change | attempted | both solved | time vs baseline |
|---|---:|---:|---:|---:|---:|
| e3-time_sr-off | 114 | +2 | 397 | 112 | 0.99x |
| e3-time_index-off | 113 | +1 | 397 | 112 | 0.98x |
| e3-time_sr-and-index-off | 113 | +1 | 399 | 112 | 0.98x |
| e3-time_baseline | 112 | — | 396 | 112 | — |
| e3-time_bwdsubs-off | 111 | -1 | 396 | 110 | 0.97x |
| e3-time_cond-on | 104 | -8 | 400 | 103 | 1.34x |
| e3-time_gensimplify-on | 99 | -13 | 400 | 97 | 1.03x |
| e3-time_demod-off | 97 | -15 | 399 | 97 | 1.04x |
| e3-time_fwdsubs-off | 59 | -53 | 396 | 59 | 1.34x |

`attempted` is how many rows arrived: a configuration with fewer has lost problems to killed workers, and part of its change is missing attempts rather than failures.

## e4 — against `e4_orthologic-off`

| configuration | solved | change | attempted | both solved | time vs baseline |
|---|---:|---:|---:|---:|---:|
| e4_orthologic-off | 111 | — | 399 | 111 | — |
| e4_orthologic-on | 104 | -7 | 394 | 101 | 1.04x |

`attempted` is how many rows arrived: a configuration with fewer has lost problems to killed workers, and part of its change is missing attempts rather than failures.

## e5 — against `e5_sine-off`

| configuration | solved | change | attempted | both solved | time vs baseline |
|---|---:|---:|---:|---:|---:|
| e5_sine-on | 123 | +12 | 396 | 110 | 0.80x |
| e5_sine-off | 111 | — | 397 | 111 | — |

`attempted` is how many rows arrived: a configuration with fewer has lost problems to killed workers, and part of its change is missing attempts rather than failures.

## A3 — does checking scale with proof size?

| against | n | slope of log(check) on log(size) | reading |
|---|---:|---:|---|
| proof_steps | 2212 | 0.71 | sub-linear: the cost per unit falls as proofs grow |
| raw_size | 2212 | 0.68 | sub-linear: the cost per unit falls as proofs grow |
| shared_size | 2212 | 0.77 | sub-linear: the cost per unit falls as proofs grow |

## T3, T4 — the trust claims

- refutations: 3115
- valid only via `Sorry` (T3): **0**
- rejected by the kernel (T4): **0**

