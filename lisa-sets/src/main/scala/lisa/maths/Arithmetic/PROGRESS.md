
# PROGRESS (Arithmetic)

## 2026-01-21

- Created initial Arithmetic scaffold files: `Predef.scala`, `Nat.scala`, `Syntax.scala`, `Examples.scala`.
- Added an initial axiomatic API for natural numbers (`ℕ`, `0`, `S`, `+`, `*`) plus closure and an induction axiom in `Nat.scala`.
- Added numeral/syntax helpers in `Syntax.scala`.
- Added 10 small example theorems (no `sorry`) in `Examples.scala`.
- Wrote a concrete roadmap in `GOALS.md` for replacing axioms by set-theoretic constructions and for the lemma checklist.

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
- Proved `Nat.natWellOrder : ⊢ wellOrder(ℕ)(membershipRelation(ℕ))` and validated it by running `runMain lisa.maths.Arithmetic.Nat`.

## 2026-01-23

- Added an Arithmetic-local recursion operator `Necessary.recursiveFunctionOn` (picks a witness that is a `functionOn(A)` and satisfies the recursion equation).
- Redefined `Nat.add`/`Nat.mul` as recursion-defined functions via `Necessary.recursiveFunctionOn` (kept `addRec`/`mulRec` as aliases).
- Replaced the 6 arithmetic API axioms (`addZero/addSucc/mulZero/mulSucc/addClosed/mulClosed`) by theorems with temporary `sorry` proofs.
- Validated by running `runMain lisa.maths.Arithmetic.Nat` and `runMain lisa.maths.Arithmetic.Examples` successfully.

- Fixed `Necessary.recursiveFunctionOnSpec` (avoids brittle `Congruence`/`Substitute` behavior under predicate application).
- Fixed `Nat.add`/`Nat.mul` definition registration (removed incorrect `addSymbol` calls that erased stored definitions).
- Proved `Nat.addZero` and `Nat.mulZero` without `sorry` and validated by running `sbt --client -no-colors "lisa-sets/runMain lisa.maths.Arithmetic.Nat"`.

