# Benchmark results

6327 rows, 400 problems, configurations: e1a, e1b

## A1 — strategies and the portfolio

| configuration | strategy | solved |
|---|---|---:|
| e1a | occurrence | 190 |
| e1a | weight-greedy | 185 |
| e1a | balanced | 183 |
| e1a | unary-redundancy | 180 |
| e1a | equational | 179 |
| e1a | subsumption-light | 175 |
| e1a | age-fair | 164 |
| e1a | first-negative | 148 |
| **e1a** | **portfolio** | **224** |

Portfolio solves 224; best single strategy occurrence solves 190, so the portfolio adds 34.

| e1b | equational | 175 |
| e1b | subsumption-light | 173 |
| e1b | balanced | 173 |
| e1b | occurrence | 173 |
| e1b | weight-greedy | 173 |
| e1b | unary-redundancy | 170 |
| e1b | age-fair | 155 |
| e1b | first-negative | 142 |
| **e1b** | **portfolio** | **214** |

Portfolio solves 214; best single strategy equational solves 175, so the portfolio adds 39.

## A2 — solved counts and where the time goes

Solved, and total time over every problem, charging an unsolved one the 180 s budget.

| configuration | solved | total time (s) | clausify | search | reconstruct | check |
|---|---:|---:|---:|---:|---:|---:|
| e1a | 224 | 33273 | 1236 | 10934 | 0 | 0 |
| e1b | 214 | 35941 | 2304 | 8879 | 184 | 7867 |

Phase columns are summed over that configuration's own refutations, so they say where its time goes, not what it would cost another configuration.

Time compared only where both solved, against `e1a`:

| configuration | both solved | e1a (s) | this (s) | ratio |
|---|---:|---:|---:|---:|
| e1b | 213 | 1347 | 2533 | 1.88x |

Solved inside the last tenth of the budget, and so able to move between runs:

| configuration | solved | near the boundary |
|---|---:|---:|
| e1a | 224 | 0 |
| e1b | 214 | 1 |

## A3 — does checking scale with proof size?

| against | n | slope of log(check) on log(size) | reading |
|---|---:|---:|---|
| proof_steps | 1334 | 0.88 | sub-linear: the cost per unit falls as proofs grow |
| raw_size | 1334 | 0.59 | sub-linear: the cost per unit falls as proofs grow |
| shared_size | 1334 | 0.67 | sub-linear: the cost per unit falls as proofs grow |

## T3, T4 — the trust claims

- refutations: 2738
- valid only via `Sorry` (T3): **0**
- rejected by the kernel (T4): **0**

