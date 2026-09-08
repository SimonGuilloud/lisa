# Benchmark results

795 rows, 399 problems, configurations: e2_deconstruct, e2_rewrite

## A2 — solved counts and where the time goes

Solved, and total time over every problem, charging an unsolved one the 180 s budget.

| configuration | solved | total time (s) | clausify | search | reconstruct | check |
|---|---:|---:|---:|---:|---:|---:|
| e2_deconstruct | 0 | 71640 | 0 | 0 | 0 | 0 |
| e2_rewrite | 0 | 71460 | 0 | 0 | 0 | 0 |

Phase columns are summed over that configuration's own refutations, so they say where its time goes, not what it would cost another configuration.

Time compared only where both solved, against `e2_deconstruct`:

| configuration | both solved | e2_deconstruct (s) | this (s) | ratio |
|---|---:|---:|---:|---:|

Solved inside the last tenth of the budget, and so able to move between runs:

| configuration | solved | near the boundary |
|---|---:|---:|
| e2_deconstruct | 0 | 0 |
| e2_rewrite | 0 | 0 |

## e2 — against `e2_deconstruct`

| configuration | solved | change | attempted | both solved | time vs baseline |
|---|---:|---:|---:|---:|---:|
| e2_deconstruct | 0 | — | 398 | 0 | — |
| e2_rewrite | 0 | +0 | 397 | 0 | — |

`attempted` is how many rows arrived: a configuration with fewer has lost problems to killed workers, and part of its change is missing attempts rather than failures.

## E2 — clausification variants

Over the 289 problems every variant clausified. `sharing` is raw size over shared size: how much the proof reuses.

| variant | clausify (s) | check (s) | proof steps | raw size | shared size | sharing |
|---|---:|---:|---:|---:|---:|---:|
| e2_deconstruct | 666.8 | 2783.6 | 11109291 | 2313678287 | 11864682 | 195.0x |
| e2_rewrite | 793.0 | 3624.1 | 11439749 | 3139858042 | 12257418 | 256.2x |

| variant | clausified | of problems seen |
|---|---:|---:|
| e2_deconstruct | 292 | 398 |
| e2_rewrite | 289 | 397 |

## T3, T4 — the trust claims

- refutations: 0
- valid only via `Sorry` (T3): **0**
- rejected by the kernel (T4): **0**

