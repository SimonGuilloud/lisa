
# GOALS (Arithmetic)

This file lists intended theorems/lemmas and a proof plan, inspired by Isabelle/HOL (mostly [Nat.thy]).

## Current status (Jan 2026)

We currently have an *axiomatic* interface for naturals in:
- [Nat.scala] (symbols `ℕ`, `0`, `S`, `+`, `*` + recursion equations + closure + induction axiom)
- [Syntax.scala] (small numeral embedding + infix `+`/`*`)
- [Examples.scala] (10 small theorems; no `sorry`)

The axioms are **temporary**: the goal is to derive them from the set-theoretic construction of `ℕ`.

## Step 1: Define `ℕ` as a set (set-theory)

Target: define `ℕ` as the *least inductive set* (von Neumann naturals / `ω`).

Planned milestones:
1. Define `inductive(X)` and `successor` are already available in set theory.
2. Define `ℕ` as the intersection of all inductive subsets of a fixed inductive set obtained from Infinity.
3. Prove:
	 - `0 ∈ ℕ`
	 - `n ∈ ℕ -> S(n) ∈ ℕ`
	 - minimality: `inductive(I) -> ℕ ⊆ I`
	 - induction principle for predicates on `ℕ`

If any missing set-theory lemmas are needed, add them to [Necessary.scala].

## Step 2: Define `+` and `*` by recursion (set-theory)

Target: define addition and multiplication as set-theoretic functions satisfying recursion equations.

Plan:
 - We now have two Isabelle/ZF-inspired prerequisites available in [Nat.scala]:
	- `natCases` (analogue of Isabelle/ZF `natE`).
	- `natMembershipWellFounded : wellFounded(membershipRelation(ℕ))(ℕ)` (analogue of Isabelle/ZF `wf_Memrel`, used to define `nat_rec` via `wfrec(Memrel(ℕ), ...)`).
- Next step (to unblock recursion definitions):
	- Either prove `wellOrder(ℕ)(membershipRelation(ℕ))` and reuse the existing well-ordered recursion theorem from set theory, or
	- Add a well-founded recursion theorem (Isabelle/ZF `wfrec`-style) in [Necessary.scala] and specialize it directly to `membershipRelation(ℕ)`.

Derive (API):
- `m + 0 = m`
- `m + S(n) = S(m + n)`
- `m * 0 = 0`
- `m * S(n) = m*n + m`
- closure: `m,n ∈ ℕ -> m+n ∈ ℕ` and `m*n ∈ ℕ`

## Step 3: Short-term theorem targets
From here, only use the API and do not rely on the particular set-theoretic encoding of naturals.
- `≤` on naturals (as subset / ordinal order) and its basic laws
- monotonicity and cancellation for `+` and `*` w.r.t. `≤`/`<`
- inequalities like `n < S(n)` and basic order arithmetic
- parity (even/odd) and simple lemmas
- exponentiation by recursion (`n^0 = 1`, `n^(S k) = n^k * n`)


## Step 4: Long-term theorem targets
Create new very ambitious goals from Isabelle/HOL.
- Every Number has a unique primte factorization (fundamental theorem of arithmetic)
- Euclid's theorem: There are infinitely many primes
- Bezout identity and gcd/lcm properties
- Chinese remainder theorem