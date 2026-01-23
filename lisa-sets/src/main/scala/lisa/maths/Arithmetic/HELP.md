# HELP: Arithmetic development in Lisa (agent pointers)

This file complements `INSTRUCTIONS.md`.
It intentionally avoids repeating: scope constraints, run commands, and `sorry` policy.

## Where things live (most relevant files)

- `lisa-sets/src/main/scala/lisa/Main.scala`: what `object ... extends lisa.Main` brings into scope
- `lisa-sets/src/main/scala/lisa/SetTheoryLibrary.scala`: set-theory surface API (membership/subset, bounded quantifiers)
- `lisa-sets/src/main/scala/lisa/maths/SetTheory/Base/Predef.scala`: recommended “import hub” for core ZF notations and theorems
- `lisa-sets/src/main/scala/lisa/maths/SetTheory/SetTheory.scala`: inductive sets + von Neumann successor (useful for defining $\mathbb{N}$)
- `lisa-sets/src/main/scala/lisa/maths/SetTheory/Ordinals/Ordinal.scala`: ordinal infrastructure (if naturals are treated as ordinals)
- `lisa-sets/src/main/scala/lisa/maths/SetTheory/Ordinals/TransfiniteInduction.scala`: transfinite induction on ordinals (useful to derive induction on $\omega$ / $\mathbb{N}$)
- `lisa-sets/src/main/scala/lisa/maths/SetTheory/Functions/Predef.scala`: functions toolkit (helpful when defining operations as set-theoretic functions)
- `lisa-sets/src/main/scala/lisa/maths/Quantifiers.scala`: proven quantifier facts and `∃!`

## Isabelle/ZF pointers (Use only to first define ℕ set-theoretically!)
The Isabelle/ZF reference library is vendored under `IsabelleZF/`. The most relevant files for defining naturals set-theoretically is:
- `IsabelleZF/Nat.thy`: definition of natural numbers.

## Isabelle/HOL pointers (what to read, what to extract)

The Isabelle/HOL reference library is vendored under `IsabelleHOL/`.
Use it as a *checklist of useful statements and lemma names*, not as code to copy.

### High-value Isabelle theories for “basic arithmetic”

Start with these files (paths relative to `IsabelleHOL/`):
- `Nat.thy`: natural numbers, induction/recursion principles, simplification lemmas for `Suc`, `+`, `*`, ordering
- `Int.thy`, `Rat.thy`, `Real.thy`: only once naturals are solid (they often reuse nat lemmas)
- `Parity.thy`: even/odd and parity lemmas
- `GCD.thy`: gcd/lcm-style facts (later stage)
- `Power.thy`, `Factorial.thy`, `Binomial.thy`: exponentiation, factorial, binomial coefficients (optional, later)
- `Orderings.thy`, `Order_Relation.thy`: order infrastructure used by arithmetic files
- `Presburger.thy`: a good source of “normal form” and linear arithmetic lemmas to consider later

If you need more advanced number theory, `IsabelleHOL/Number_Theory/` contains a curated collection (e.g. `Totient.thy`, `Quadratic_Reciprocity.thy`), but those should typically be “step 3” goals.

### How to use Isabelle effectively for this project

Suggested workflow for populating `GOALS.md` and planning your lemma API:
- Pick one Isabelle file (usually `Nat.thy`). Skim headings and collect lemma names by theme:
  - algebraic laws: associativity/commutativity, identities, distributivity
  - order laws: monotonicity, transitivity, antisymmetry, `Suc`-order interaction
  - induction-friendly rewrite lemmas for `Suc` and recursion equations
- For each candidate lemma, record in `GOALS.md`:
  - Isabelle file + lemma name
  - the informal statement (paraphrase)
  - the Lisa-side name you want (following `STYLE.md`)

### Translating Isabelle statements to Lisa set-theoretic naturals

The exact translation depends on how $\mathbb{N}$ is represented.
If you use the standard set-theoretic choice $\mathbb{N} := \omega$ (von Neumann naturals):
- Isabelle `0` corresponds to $\emptyset$
- Isabelle `Suc n` corresponds to `successor(n)` (i.e. $n \cup \{n\}$)
- Isabelle `m ≤ n` is typically the subset/ordinal order (often expressible as `m ⊆ n` or via the ordinal `<=` already developed)

Practical tip: when you state a theorem inspired by Isabelle, state it *using your arithmetic API*, not using the raw set encoding.

### Induction on numbers via induction on ordinals

If you define $\mathbb{N} := \omega$, you can often prove “nat induction” by applying the existing transfinite induction machinery to ordinals and then restricting the result to elements of $\omega$.
Concretely: prove your property for $0$ and show it is preserved by `successor`; then use ordinal/transfinite induction to conclude it holds for all $n \in \omega$.


