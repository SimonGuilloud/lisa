
# PROGRESS (Arithmetic)

## 2026-01-21

- Created initial Arithmetic scaffold files: [Predef.scala], [Nat.scala], [Syntax.scala], [Examples.scala].
- Added an initial axiomatic API for natural numbers (`ℕ`, `0`, `S`, `+`, `*`) plus closure and an induction axiom in [Nat.scala].
- Added numeral/syntax helpers in [Syntax.scala].
- Added 10 small example theorems (no `sorry`) in [Examples.scala].
- Wrote a concrete roadmap in [GOALS.md] for replacing axioms by set-theoretic constructions and for the lemma checklist.

- Step 1 progress: defined `ℕ` set-theoretically as the intersection of all inductive subsets of a chosen inductive set `I = ε(i, inductive(i))`.
- Proved `zeroInℕ : ⊢ 0 ∈ ℕ` from the definition.
- Proved `ℕInductive : ⊢ inductive(ℕ)` from the definition.
- Proved `succClosed : ⊢ ∀n. n ∈ ℕ -> S(n) ∈ ℕ` as a corollary of `ℕInductive`.
- Proved `induction : ⊢ (P(0) ∧ (∀n. n∈ℕ -> (P(n) -> P(S(n))))) -> (∀n. n∈ℕ -> P(n))` from the minimality characterization of `ℕ`.
- Proved `succSubsetℕ : (n ⊆ ℕ, n ∈ ℕ) ⊢ S(n) ⊆ ℕ`.
- Proved `ℕTransitive : ⊢ transitiveSet(ℕ)` by applying the derived induction theorem to the predicate `n ⊆ ℕ`.
- Proved `natCases : n∈ℕ ⊢ (n=0) ∨ (∃m∈ℕ. n=S(m))` (Isabelle/ZF `natE`-style elimination / cases lemma).
- Proved `natElementsTransitive : n∈ℕ ⊢ transitiveSet(n)` (needed to reason about membership chains inside naturals).
- Proved `natMembershipWellFounded : ⊢ wellFounded(membershipRelation(ℕ))(ℕ)` (Isabelle/ZF `wf_Memrel` analogue; a key prerequisite for defining `nat_rec` via well-founded recursion / `wfrec(Memrel(ℕ), ...)`).
- Validated by running `sbtn "runMain lisa.maths.Arithmetic.Examples"` successfully.

## 2026-01-22

- Added an Arithmetic-local lemma `Necessary.restrictionApp` (restriction evaluation without relying on unfinished upstream `Restriction.domain`).
- Added an Arithmetic-local lemma `Necessary.restrictionApp` (restriction evaluation without relying on unfinished upstream `Restriction.domain`).
- Proved `Nat.natWellOrder : ⊢ wellOrder(ℕ)(membershipRelation(ℕ))` and validated it by running `runMain lisa.maths.Arithmetic.Nat`.

## 2026-01-23

- Added an Arithmetic-local recursion operator `Necessary.recursiveFunctionOn` (picks a witness that is a `functionOn(A)` and satisfies the recursion equation).
- Redefined `Nat.add`/`Nat.mul` as recursion-defined functions via `Necessary.recursiveFunctionOn` (kept `addRec`/`mulRec` as aliases).
- Replaced the 6 arithmetic API axioms (`addZero/addSucc/mulZero/mulSucc/addClosed/mulClosed`) by theorems with temporary `sorry` proofs.
- Validated by running `runMain lisa.maths.Arithmetic.Nat` and `runMain lisa.maths.Arithmetic.Examples` successfully.

- Fixed `Necessary.recursiveFunctionOnSpec` (avoids brittle `Congruence`/`Substitute` behavior under predicate application).
- Fixed `Nat.add`/`Nat.mul` definition registration (removed incorrect `addSymbol` calls that erased stored definitions).
- Proved `Nat.addZero` and `Nat.mulZero` without `sorry` and validated by running `sbt --client -no-colors "lisa-sets/runMain lisa.maths.Arithmetic.Nat"`.

## 2026-01-24

- Replaced the Scala-level successor wrapper `S` by a Lisa definition `Succ : ℕ → ℕ` in [Nat.scala] and migrated all arithmetic files to use `Succ` ([Syntax.scala], [Examples.scala], [NatAlgebra.scala], [NatDerived.scala]).
- Completed the [NatDerived.scala] port to `Succ`, including a recursion-defined `double` and theorems `doubleZero` and `doubleSucc`.
- Validated by running `sbt --client -no-colors "lisa-sets/runMain lisa.maths.Arithmetic.Nat"` and `sbt --client -no-colors "lisa-sets/runMain lisa.maths.Arithmetic.NatDerived"` successfully.

- Replaced `Nat.zero` by a Lisa definition `zero = DEF(∅)` and fixed downstream proofs that depended on `0` being syntactically `∅`.
- Added `NatAlgebra.addAssoc` (addition associativity; Isabelle/HOL [Nat.thy] `add_assoc`-style lemma).
- Validated by running `sbt --client -no-colors "lisa-sets/runMain lisa.maths.Arithmetic.Nat"` and `sbt --client -no-colors "lisa-sets/runMain lisa.maths.Arithmetic.NatAlgebra"` successfully.

- Extended [NatAlgebra.scala] with more Isabelle/HOL [Nat.thy]-style basic lemmas: `addOneRight`, `mulZeroLeft`, `mulOneRight`, `mulOneLeft`.
- Validated by running `sbt --client -no-colors "lisa-sets/runMain lisa.maths.Arithmetic.NatAlgebra"` successfully.

## 2026-01-25

- Added [NatOrder.scala]: a basic order API for naturals-as-von-Neumann-ordinals using `⊆` (as `<=`) and `∈` (as `<`).
- Proved and validated core order facts: transitivity/antisymmetry for `⊆`, trichotomy by membership, `m ⊆ n ⇔ (m ∈ n ∨ m = n)`, totality of `⊆`, and successor/order bridge lemmas (`m ∈ Succ(n) ⇔ m ⊆ n`, `m ∈ n ⇔ Succ(m) ⊆ n`, `Succ(m) ⊆ Succ(n) ⇔ m ⊆ n`).
- Added direction/cancellation-style corollaries for easier reuse (e.g. `m ⊆ n ∧ m ≠ n ⟹ m ∈ n`, monotonicity of `Succ` w.r.t. `⊆`).
- Validated by running `sbt --client -no-colors "runMain lisa.maths.Arithmetic.NatOrder"` successfully.

- Standardized theorem statement style across Arithmetic: prefer free variables and assumptions on the left of the sequent (instead of implications / outer quantifiers), while keeping the same API content.
- Added Isabelle/HOL [Nat.thy]-style semiring lemmas to [NatAlgebra.scala]: `mulDistribLeft` (`a*(b+c)=a*b+a*c`) and `mulAssoc`.
- Validated by running `sbt --client -no-colors "lisa-sets/runMain lisa.maths.Arithmetic.Nat"`, `...NatAlgebra`, `...NatDerived`, and `...Examples` successfully.

- Added Isabelle/HOL [Nat.thy]-style successor/zero disequality lemmas to [Nat.scala]: `succNeZero`, `zeroNeSucc`, `succNeSelf`, `selfNeSucc`.
- Added basic right-zero/recursion-equation convenience lemmas and proved the zero characterizations `addEqZeroIff` (`add_is_0`) and `mulEqZeroIff` (`mult_is_0`) in [NatAlgebra.scala].

- Extended [NatAlgebra.scala] with further [Nat.thy]-style facts derived from `add_is_0` / `mult_is_0`: projections (`addEqZeroLeft/right`), nonzero corollaries (`addNeZeroLeft/right`, `mulNeZero`, `mulNeZeroBoth`), nonzero iff characterizations (`addNeZeroIff`, `mulNeZeroIff`), and the major characterization `mulEqSelfIff` (`mult_eq_self`).
- Validated by running `sbt --client -no-colors "lisa-sets/runMain lisa.maths.Arithmetic.NatAlgebra"` successfully.

- Extended [NatAlgebra.scala] with more Isabelle/HOL [Nat.thy]-style algebraic characterizations and commutation lemmas:
	- `addEqSelfIff` (`m+n=m ↔ n=0`) and `addEqSelfIffLeft` (`m+n=n ↔ m=0`).
	- `addLeftComm` and `mulLeftComm` (left-commutativity).
	- `mulEqSelfRightIff` (`m*n=n ↔ n=0 ∨ m=1`) via commutativity.
	- Corollaries of `mult_is_0`: `mulEqZeroRightFromLeftNeZero` and `mulEqZeroLeftFromRightNeZero`.
	- `addEqOneIff` (`m+n=1` characterization).
- Validated by running `sbt --client -no-colors "lisa-sets/runMain lisa.maths.Arithmetic.NatAlgebra"` successfully.

- Added [NatOrderAlgebra.scala]: interaction lemmas between nat order (`⊆`/`∈`) and arithmetic.
	- Addition monotonicity (`addMonoRight`, `addMonoLeft`, `addMonoBoth`) and cancellation for `⊆` (`addLeCancelRight`, `addLeCancelLeft`).
	- Strict addition monotonicity for `∈` (`addLtMonoRight`, `addLtMonoLeft`).
	- Multiplication monotonicity for `⊆` (`mulMonoRight`, `mulMonoLeft`).
	- Validated by running `sbt --client -no-colors "lisa-sets/runMain lisa.maths.Arithmetic.NatOrderAlgebra"` successfully.

- Proved `NatPower.powMulDistrib` (Isabelle/HOL [Power.thy] `power_mult_distrib`) and validated by running `sbt --client -no-colors "lisa-sets/runMain lisa.maths.Arithmetic.NatPower"`.

- Extended [NatPower.scala] with additional power lemmas (including parity-power equivalences `evenPowIff` / `oddPowIff` and small-power expansions) and validated by running `sbt --client -no-colors "lisa-sets/runMain lisa.maths.Arithmetic.NatPower"`.
