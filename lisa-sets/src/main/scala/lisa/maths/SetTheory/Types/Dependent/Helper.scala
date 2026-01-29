package lisa.maths.SetTheory.Types.Dependent

import Symbols.*
import lisa.maths.SetTheory.Base.Predef.{*, given}
import lisa.maths.SetTheory.Cardinal.Predef.{*}
import lisa.maths.SetTheory.Functions.Predef.*
import lisa.maths.Quantifiers.*

/**
 * This file defines some useful helper theorem used in the typing rules
 */
object Helper extends lisa.Main:
  /**
   * Unfolds the Set Comprehension definition of the Pi type.
   *
   * Proves: e1 ∈ {f ∈ S | P(f)} <=> e1 ∈ S ∧ P(e1)
   */
  val piExpansion = Lemma(
    e1 ∈ {
      f ∈ 𝒫(T1 × ⋃({ T2(a) | a ∈ T1 })) |
        (∀(x ∈ T1, ∃!(y, (x, y) ∈ f))) /\ (∀(a, ∀(b, (a, b) ∈ f ==> (b ∈ T2(a)))))
    } <=> e1 ∈ 𝒫(T1 × ⋃({ T2(a) | a ∈ T1 })) /\
      (∀(x ∈ T1, ∃!(y, (x, y) ∈ e1))) /\ (∀(a, ∀(b, (a, b) ∈ e1 ==> (b ∈ T2(a)))))
  ) {
    have(thesis) by Comprehension.apply
  }

  /**
   * Predicate Logic Lemma: Distributes a universal implication (∀)
   * over an existential conjunction (∃).
   *
   * Proves: (∀x. P(x) => Q(x), ∃x. P(x) ∧ H(x)) |- ∃x. Q(x) ∧ H(x)
   */
  val existPartialApply = Theorem(
    (∀(x, P(x) ==> Q(x)), ∃(x, P(x) /\ H(x))) |- ∃(x, Q(x) /\ H(x))
  ) {
    assume(∀(x, P(x) ==> Q(x)))
    val premise = thenHave(P(x) ==> Q(x)) by InstantiateForall(x)
    val goal = have(P(x) /\ H(x) |- Q(x) /\ H(x)) subproof {
      assume(P(x) /\ H(x))
      have(thesis) by Tautology.from(premise)
    }
    thenHave(P(x) /\ H(x) |- ∃(x, Q(x) /\ H(x))) by RightExists
    thenHave(thesis) by LeftExists
  }

  /**
   * One-Point Rule for a function F:
   * If there exists an x such that P(F(x)) holds and F(x) equals y,
   * then P(y) must hold.
   *
   * Proves: ∃x. (P(F(x)) ∧ y = F(x)) ==> P(y)
   */
  val onePointFunctionRule = Theorem(
    ∃(x, P(F(x)) /\ (y === F(x))) ==> P(y)
  ) {
    have((P(F(x)), y === F(x)) |- P(y)) by Congruence
    thenHave(P(F(x)) /\ (y === F(x)) |- P(y)) by Restate
    thenHave(∃(x, P(F(x)) /\ (y === F(x))) |- P(y)) by LeftExists
    thenHave(thesis) by Restate
  }

  /**
   * Transitivity of Equality (Sequent form).
   *
   * Proves: (x = y ∧ y = z) |- x = z
   */
  val equalTransitivity = Theorem(
    ((x === y) /\ (y === z)) |- (x === z)
  ) {
    assume(x === y)
    assume(y === z)
    have(x === z) by Congruence
    thenHave(thesis) by Restate
  }

  /**
   * Transitivity of Equality (Implication form).
   * This is friendlier for use with Tautology.from.
   *
   * Proves: (x = y ∧ y = z) ==> x = z
   */
  val equalTransitivityApplication = Theorem(
    ((x === y) /\ (y === z)) ==> (x === z)
  ) {
    have(thesis) by Tautology.from(equalTransitivity)
  }

  /**
   * Substitution rule (Congruence) in implication form.
   *
   * Proves: (P(x) ∧ y = x) ==> P(y)
   */
  val localSubstitute = Theorem(
    (P(x) /\ (y === x)) ==> P(y)
  ) {
    have((P(x), y === x) |- P(y)) by Congruence
    thenHave(P(x) /\ (y === x) |- P(y)) by Restate
    thenHave(thesis) by Restate
  }

  /**
   * Theorem --- Universe Family Union Closure.
   *
   * Given an index set A ∈ U, and a family of sets T2(x) where each T2(x) ∈ U,
   * the union of this family ⋃ { T2(x) | x ∈ A } is also in U.
   */
  val universeFamilyUnionClosure = Theorem(
    (isUniverse(U), A ∈ U, ∀(x, x ∈ A ==> T2(x) ∈ U)) |- ⋃({ T2(x) | x ∈ A }) ∈ U
  ) {
    assumeAll
    val stmt = have(∀(x, x ∈ A ==> T2(x) ∈ U)) by Hypothesis
    val G = { (x, T2(x)) | x ∈ A }
    val relationProp = have(relationBetween(G)(A)(U)) subproof {
      have(z ∈ G ==> z ∈ (A × U)) subproof {
        assume(z ∈ G)
        have((x ∈ A /\ ((x, T2(x)) === z)) |- z ∈ (A × U)) subproof {
          assume(x ∈ A)
          assume((x, T2(x)) === z)
          val eqFormula = have((x, T2(x)) === z) by Hypothesis
          have(T2(x) ∈ U) by InstantiateForall(x)(stmt)
          thenHave((x, T2(x)) ∈ (A × U)) by Tautology.fromLastStep(CartesianProduct.membershipSufficientCondition of (y := T2(x), B := U))
          thenHave(thesis) by Substitute(eqFormula)
        }
        thenHave(∃(x, x ∈ A /\ ((x, T2(x)) === z)) |- z ∈ (A × U)) by LeftExists
        thenHave(thesis) by Tautology.fromLastStep(Replacement.membership of (y := z, F := λ(x, (x, T2(x)))))
      }
      thenHave(∀(z, z ∈ G ==> z ∈ (A × U))) by RightForall
      thenHave(G ⊆ (A × U)) by Tautology.fromLastStep(subsetAxiom of (x := G, y := (A × U)))
      thenHave(thesis) by Substitute(relationBetween.definition of (R := G, X := A, Y := U))
    }
    have(a ∈ A ==> ∃!(y, (a, y) ∈ G)) subproof {
      assume(a ∈ A)
      val existence = have((a, T2(a)) ∈ G) subproof {
        have(a ∈ A /\ ((a, T2(a)) === (a, T2(a)))) by Tautology
        thenHave(∃(x, x ∈ A /\ ((x, T2(x)) === (a, T2(a))))) by RightExists
        thenHave(thesis) by Tautology.fromLastStep(
          Replacement.membership of (y := (a, T2(a)), F := λ(x, (x, T2(x))))
        )
      }
      have((a, y) ∈ G ==> (y === T2(a))) subproof {
        assume((a, y) ∈ G)
        have((x ∈ A /\ ((a, y) === (x, T2(x)))) ==> (y === T2(a))) subproof {
          assume((x ∈ A /\ ((a, y) === (x, T2(x)))))
          val both = have((a === x) /\ (y === T2(x))) by Tautology.from(Pair.extensionality of (b := y, c := x, d := T2(x)))
          val s1 = have(x === a) by Tautology.from(both)
          have(y === T2(x)) by Tautology.from(both)
          thenHave(y === T2(a)) by Substitute(s1)
          thenHave(thesis) by Restate
        }
        thenHave(∀(x, (x ∈ A /\ ((a, y) === (x, T2(x)))) ==> (y === T2(a)))) by RightForall
        thenHave(thesis) by Tautology.fromLastStep(
          existentialImplicationDistribution of (z := x, P := λ(x, (x ∈ A /\ ((a, y) === (x, T2(x))))), Q := λ(x, y === T2(a))),
          Replacement.membership of (y := (a, y), F := λ(x, (x, T2(x)))),
          closedFormulaExistential of (p := (y === T2(a)))
        )
      }
      val uniqueness = thenHave(∀(y, (a, y) ∈ G ==> (y === T2(a)))) by RightForall
      have((a, T2(a)) ∈ G /\ ∀(y, (a, y) ∈ G ==> (y === T2(a)))) by Tautology.from(existence, uniqueness)
      thenHave(∃(z, (a, z) ∈ G /\ ∀(y, (a, y) ∈ G ==> (y === z)))) by RightExists
      thenHave(∃!(z, (a, z) ∈ G)) by Substitute(∃!.definition of (P := λ(z, (a, z) ∈ G)))
      thenHave(thesis) by Restate
    }
    thenHave(∀(a, a ∈ A ==> ∃!(y, (a, y) ∈ G))) by RightForall
    val functionalProp = thenHave(∀(x, x ∈ A ==> ∃!(y, (x, y) ∈ G))) by Restate
    val rangeEq = have(range(G) === { T2(x) | x ∈ A }) subproof {
      have(y ∈ range(G) <=> y ∈ { T2(x) | x ∈ A }) subproof {
        val rhs = { T2(x) | x ∈ A }
        val `==>` = have(y ∈ range(G) ==> y ∈ rhs) subproof {
          assume(y ∈ range(G))
          thenHave(y ∈ { snd(z) | z ∈ G }) by Substitute(range.definition of (R := G))
          val s = thenHave(∃(z ∈ G, snd(z) === y)) by Tautology.fromLastStep(Replacement.membership of (F := λ(x, snd(x)), A := G, x := z))
          have((z ∈ G /\ (snd(z) === y)) |- y ∈ rhs) subproof {
            assume(z ∈ G /\ (snd(z) === y))
            val inners = have(∃(x ∈ A, (x, T2(x)) === z)) by Tautology.from(Replacement.membership of (F := λ(x, (x, T2(x))), y := z))
            have((x ∈ A /\ ((x, T2(x)) === z)) |- y ∈ rhs) subproof {
              assume(x ∈ A /\ ((x, T2(x)) === z))
              val pairEq = have((x, T2(x)) === z) by Tautology
              have(snd(z) === y) by Tautology
              thenHave(snd(x, T2(x)) === y) by Substitute(pairEq)
              val yEq = thenHave(y === T2(x)) by Tautology.fromLastStep(
                Pair.pairSnd of (y := T2(x)),
                equalTransitivityApplication of (x := y, y := snd(x, T2(x)), z := T2(x))
              )
              have(x ∈ A /\ (T2(x) === T2(x))) by Tautology
              thenHave(∃(a ∈ A, T2(a) === T2(x))) by RightExists
              thenHave(T2(x) ∈ rhs) by Tautology.fromLastStep(Replacement.membership of (y := T2(x), F := λ(a, T2(a))))
              thenHave(thesis) by Substitute(yEq)
            }
            thenHave(∃(x ∈ A, (x, T2(x)) === z) |- y ∈ rhs) by LeftExists
            thenHave(thesis) by Tautology.fromLastStep(inners)
          }
          thenHave(∃(z ∈ G, snd(z) === y) |- y ∈ rhs) by LeftExists
          thenHave(thesis) by Tautology.fromLastStep(s)
        }
        val `<==` = have(y ∈ rhs ==> y ∈ range(G)) subproof {
          assume(y ∈ rhs)
          have((a ∈ A /\ (y === T2(a))) ==> y ∈ range(G)) subproof {
            assume(a ∈ A /\ (y === T2(a)))
            val yEq = have(y === T2(a)) by Tautology
            have(a ∈ A /\ ((a, y) === (a, y))) by Tautology
            thenHave(a ∈ A /\ ((a, y) === (a, T2(a)))) by Substitute(yEq)
            thenHave(∃(z ∈ A, (a, y) === (z, T2(z)))) by RightExists
            thenHave((a, y) ∈ G /\ (snd(a, y) === y)) by Tautology.fromLastStep(
              Replacement.membership of (y := (a, y), F := λ(z, (z, T2(z)))),
              Pair.pairSnd of (x := a)
            )
            thenHave(∃(z ∈ G, snd(z) === y)) by RightExists
            thenHave(y ∈ { snd(z) | z ∈ G }) by Tautology.fromLastStep(Replacement.membership of (A := G, F := snd))
            thenHave(y ∈ range(G)) by Substitute(range.definition of (R := G))
            thenHave(thesis) by Restate
          }
          thenHave(∀(a, (a ∈ A /\ (y === T2(a))) ==> y ∈ range(G))) by RightForall
          thenHave(thesis) by Tautology.fromLastStep(
            existentialImplicationDistribution of (z := a, P := λ(a, (a ∈ A /\ (y === T2(a)))), Q := λ(a, y ∈ range(G))),
            Replacement.membership of (F := T2),
            closedFormulaExistential of (p := y ∈ range(G))
          )
        }
        have(thesis) by Tautology.from(`==>`, `<==`)
      }
      thenHave(thesis) by Extensionality
    }
    have(relationBetween(G)(A)(U) /\ ∀(x, x ∈ A ==> ∃!(y, (x, y) ∈ G))) by Tautology.from(relationProp, functionalProp)
    thenHave(functionBetween(G)(A)(U)) by Substitute(functionBetween.definition of (f := G, B := U))
    thenHave(range(G) ∈ U) by Tautology.fromLastStep(universeReplacementClosure of (f := G))
    thenHave({ T2(x) | x ∈ A } ∈ U) by Substitute(rangeEq)
    thenHave(thesis) by Tautology.fromLastStep(universeUnionClosure of (x := { T2(x) | x ∈ A }))
  }

  /**
   * Theorem --- Universe Closure under Dependent Product (Pi Types).
   *
   * If the domain `T1` is in `U`, and for every element `x` in `T1`, the codomain type
   * `T2(x)` is also in `U`, then the set of all dependent functions `Π(x:T1).T2(x)`
   * is an element of `U`.
   */
  val universePiClosure = Theorem(
    (isUniverse(U), T1 ∈ U, ∀(x, x ∈ T1 ==> T2(x) ∈ U)) |-
      Pi(T1)(T2) ∈ U
  ) {
    assumeAll
    val boundSet = 𝒫(T1 × ⋃({ T2(x) | x ∈ T1 }))
    val piSet = {
      f ∈ boundSet |
        (∀(x ∈ T1, ∃!(y, (x, y) ∈ f))) /\
        (∀(a, ∀(b, (a, b) ∈ f ==> (b ∈ T2(a)))))
    }
    have(piSet ∈ U) by Tautology.from(
      universeFamilyUnionClosure of (A := T1),
      universeProductClosure of (A := T1, B := ⋃({ T2(x) | x ∈ T1 })),
      universePowerSetClosure of (x := T1 × ⋃({ T2(x) | x ∈ T1 })),
      Comprehension.subset of (
        x := f,
        y := boundSet,
        φ := λ(
          f,
          (∀(x ∈ T1, ∃!(y, (x, y) ∈ f))) /\
            (∀(a, ∀(b, (a, b) ∈ f ==> (b ∈ T2(a)))))
        )
      ),
      universeSubsetClosure of (A := boundSet, B := piSet)
    )
    thenHave(thesis) by Substitute(Pi.definition)
  }

  /**
   * Theorem --- If A is a subset of B, then the union of A and B is B.
   *
   * (A ⊆ B) |- (A ∪ B) === B
   */
  val unionAbsorb = Theorem(
    (A ⊆ B) |- (A ∪ B) === B
  ) {
    assume(A ⊆ B)
    val forward = have((A ∪ B) ⊆ B) by Tautology.from(
      Union.leftUnionSubset of (x := A, y := B, z := B),
      Subset.reflexivity of (x := B)
    )
    val backward = have(B ⊆ (A ∪ B)) by Tautology.from(
      Union.rightSubset of (x := A, y := B)
    )
    have(thesis) by Tautology.from(
      forward,
      backward,
      Subset.antisymmetry of (x := (A ∪ B), y := B)
    )
  }

  /**
   * Theorem --- If A is a subset of B, and B equals to C, then the union of A and B is C.
   *
   * (A ⊆ B, B === C) |- (A ∪ B) === C
   */
  val unionAbsorbVariant = Theorem(
    (A ⊆ C, B === C) |- (A ∪ B) === C
  ) {
    assumeAll
    have((A ∪ C) === C) by Tautology.from(unionAbsorb of (B := C))
    thenHave(thesis) by Congruence
  }

  /**
   * Theorem --- unionEqual
   */
  val unionEqual = Theorem(
    (A === C, B === C) |- (A ∪ B) === C
  ) {
    assumeAll
    have(A ⊆ A) by Tautology.from(Subset.reflexivity of (x := A))
    thenHave(A ⊆ C) by Congruence
    thenHave(thesis) by Tautology.fromLastStep(unionAbsorbVariant)
  }

  /**
   * Theorem --- set A is subset of its universe
   *
   * A ⊆ universeOf(A)
   */
  val subsetOfUniverse = Theorem(
    A ⊆ universeOf(A)
  ) {
    have(thesis) by Tautology.from(
      universeOfIsUniverse of (x := A),
      universeTransitivity of (x := A, U := universeOf(A))
    )
  }

  /**
   * Theorem --- If U1 U2 are universes, and U1 ⊆ U2(hiearchy) then Π(x :: T1, T2(x)) ∈ U2
   *
   * one direction case in TForm theorem
   */

  val universeHierarchyPiClosureLeft = Theorem(
    (
      isUniverse(U1),
      isUniverse(U2),
      U1 ⊆ U2,
      T1 ∈ U1,
      ∀(x, (x ∈ T1) ==> (T2(x) ∈ U2))
    ) |- Π(x :: T1, T2(x)) ∈ U2
  ) {
    assumeAll
    val piTerm = Π(x :: T1, T2(x))
    have(thesis) by Tautology.from(
      universePiClosure of (U := U2),
      Subset.membership of (x := U1, y := U2, z := T1)
    )
  }

  /**
   * Theorem --- If U1 U2 are universes, and U2 ⊆ U1(hiearchy) then Π(x :: T1, T2(x)) ∈ U1
   *
   * the one direction case in TForm theorem
   */
  val universeHierarchyPiClosureRight = Theorem(
    (
      isUniverse(U1),
      isUniverse(U2),
      U2 ⊆ U1,
      T1 ∈ U1,
      ∀(x, (x ∈ T1) ==> (T2(x) ∈ U2))
    ) |- Π(x :: T1, T2(x)) ∈ U1
  ) {
    assumeAll
    val piTerm = Π(x :: T1, T2(x))
    have(∀(x, (x ∈ T1) ==> (T2(x) ∈ U1))) subproof {
      have(∀(x, (x ∈ T1) ==> (T2(x) ∈ U2))) by Hypothesis
      thenHave(x ∈ T1 ==> (T2(x) ∈ U2)) by InstantiateForall(x)
      thenHave(x ∈ T1 ==> (T2(x) ∈ U1)) by Tautology.fromLastStep(Subset.membership of (x := U2, y := U1, z := T2(x)))
      thenHave(thesis) by RightForall
    }
    thenHave(thesis) by Tautology.fromLastStep(
      universePiClosure of (U := U1)
    )
  }

  /**
   * Theorem --- Covariance of Pi types (Dependent Function Types).
   *
   * If two Pi types share the same domain, and the codomain of the first is
   * a subset of the codomain of the second for all inputs (pointwise subset),
   * then the first Pi type is a subset of the second.
   */
  val piCovariance = Theorem(
    (T === T1, ∀(x ∈ T, T2(x) ⊆ T2p(x))) |- Π(x :: T, T2(x)) ⊆ Π(x :: T1, T2p(x))
  ) {
    assumeAll
    val equalFormula = have(T === T1) by Hypothesis
    have(f ∈ Π(x :: T, T2(x)) ==> f ∈ Π(x :: T1, T2p(x))) subproof {
      assume(f ∈ Π(x :: T, T2(x)))
      have(f ∈ Π(x :: T, T2(x))) by Hypothesis
      thenHave(f ∈ Π(x :: T1, T2(x))) by Substitute(equalFormula)
      thenHave(f ∈ { f ∈ 𝒫(T1 × ⋃({ T2(a) | a ∈ T1 })) | (∀(x ∈ T1, ∃!(y, (x, y) ∈ f))) /\ (∀(a, ∀(b, (a, b) ∈ f ==> (b ∈ T2(a))))) }) by Substitute(Pi.definition)
      val stmt = thenHave(f ∈ 𝒫(T1 × ⋃({ T2(a) | a ∈ T1 })) /\ (∀(x ∈ T1, ∃!(y, (x, y) ∈ f))) /\ (∀(a, ∀(b, (a, b) ∈ f ==> (b ∈ T2(a)))))) by Tautology.fromLastStep(piExpansion of (e1 := f))

      have(∀(x ∈ T, T2(x) ⊆ T2p(x))) by Tautology
      thenHave(x ∈ T ==> T2(x) ⊆ T2p(x)) by InstantiateForall(x)
      thenHave(x ∈ T1 ==> T2(x) ⊆ T2p(x)) by Substitute(equalFormula)
      val pred = thenHave(∀(x ∈ T1, T2(x) ⊆ T2p(x))) by RightForall

      // cond1: f ∈ 𝒫(T1 × ⋃({ T2p(a) | a ∈ T1 })
      have(f ∈ 𝒫(T1 × ⋃({ T2(a) | a ∈ T1 }))) by Weakening(stmt)
      val stmt1 = thenHave(f ⊆ (T1 × ⋃({ T2(a) | a ∈ T1 }))) by Tautology.fromLastStep(powerSetAxiom of (x := f, y := (T1 × ⋃({ T2(a) | a ∈ T1 }))))
      have(⋃({ T2(a) | a ∈ T1 }) ⊆ ⋃({ T2p(a) | a ∈ T1 })) subproof {
        have(x ∈ ⋃({ T2(a) | a ∈ T1 }) ==> x ∈ ⋃({ T2p(a) | a ∈ T1 })) subproof {
          assume(x ∈ ⋃({ T2(a) | a ∈ T1 }))
          val stmt1 = have(∃(y, y ∈ { T2(a) | a ∈ T1 } /\ x ∈ y)) by Tautology.from(unionAxiom of (z := x, x := { T2(a) | a ∈ T1 }))
          have((y ∈ { T2(a) | a ∈ T1 }, x ∈ y) |- x ∈ ⋃({ T2p(a) | a ∈ T1 })) subproof {
            assumeAll
            val stmt2 = have(∃(a ∈ T1, T2(a) === y)) by Tautology.from(Replacement.membership of (F := λ(x, T2(x)), A := T1))
            have((a ∈ T1, T2(a) === y) |- x ∈ ⋃({ T2p(a) | a ∈ T1 })) subproof {
              assumeAll
              val equalFormula2 = have(T2(a) === y) by Hypothesis
              have(a ∈ T1 ==> T2(a) ⊆ T2p(a)) by InstantiateForall(a)(pred)
              thenHave(T2(a) ⊆ T2p(a)) by Tautology.fromLastStep()
              thenHave(y ⊆ T2p(a)) by Substitute(equalFormula2)
              val stmt3 = thenHave(x ∈ T2p(a)) by Tautology.fromLastStep(Subset.membership of (x := y, y := T2p(a), z := x))
              have(T2p(a) === T2p(a)) by Congruence
              thenHave(a ∈ T1 /\ (T2p(a) === T2p(a))) by Tautology.fromLastStep()
              thenHave(∃(x ∈ T1, T2p(x) === T2p(a))) by RightExists
              thenHave(T2p(a) ∈ { T2p(x) | x ∈ T1 } /\ x ∈ T2p(a)) by Tautology.fromLastStep(
                Replacement.membership of (y := T2p(a), F := λ(x, T2p(x)), A := T1),
                stmt3
              )
              thenHave(∃(z, z ∈ { T2p(x) | x ∈ T1 } /\ x ∈ z)) by RightExists
              thenHave(thesis) by Tautology.fromLastStep(unionAxiom of (z := x, x := { T2p(x) | x ∈ T1 }))
            }
            thenHave(a ∈ T1 /\ (T2(a) === y) |- x ∈ ⋃({ T2p(a) | a ∈ T1 })) by Restate
            thenHave(∃(a ∈ T1, T2(a) === y) |- x ∈ ⋃({ T2p(a) | a ∈ T1 })) by LeftExists
            thenHave(thesis) by Tautology.fromLastStep(stmt2)
          }
          thenHave(y ∈ { T2(a) | a ∈ T1 } /\ x ∈ y |- x ∈ ⋃({ T2p(a) | a ∈ T1 })) by Restate
          thenHave(∃(y, y ∈ { T2(a) | a ∈ T1 } /\ x ∈ y) |- x ∈ ⋃({ T2p(a) | a ∈ T1 })) by LeftExists
          thenHave(thesis) by Tautology.fromLastStep(stmt1)
        }
        thenHave(∀(x, x ∈ ⋃({ T2(a) | a ∈ T1 }) ==> x ∈ ⋃({ T2p(a) | a ∈ T1 }))) by RightForall
        thenHave(thesis) by Tautology.fromLastStep(Subset.definition of (x := ⋃({ T2(a) | a ∈ T1 }), y := ⋃({ T2p(a) | a ∈ T1 }), z := x))
      }
      val cond1 = thenHave(f ∈ 𝒫(T1 × ⋃({ T2p(a) | a ∈ T1 }))) by Tautology.fromLastStep(
        stmt1,
        Subset.reflexivity of (x := T1),
        CartesianProduct.monotonic of (A := T1, B := ⋃({ T2(a) | a ∈ T1 }), C := T1, D := ⋃({ T2p(a) | a ∈ T1 })),
        Subset.transitivity of (x := f, y := (T1 × ⋃({ T2(a) | a ∈ T1 })), z := (T1 × ⋃({ T2p(a) | a ∈ T1 }))),
        powerSetAxiom of (x := f, y := (T1 × ⋃({ T2p(a) | a ∈ T1 })))
      )

      // Cond2: ∀(x ∈ T1, ∃!(y, (x, y) ∈ f))
      val cond2 = have(∀(x ∈ T1, ∃!(y, (x, y) ∈ f))) by Weakening(stmt)

      // Cond3: ∀(a, ∀(b, (a, b) ∈ f ==> (b ∈ T2p(a)))))
      val cond3 = have(∀(a, ∀(b, (a, b) ∈ f ==> (b ∈ T2p(a))))) subproof {
        have((a, b) ∈ f ==> b ∈ T2p(a)) subproof {
          assume((a, b) ∈ f)
          have(∀(a, ∀(b, (a, b) ∈ f ==> (b ∈ T2(a))))) by Weakening(stmt)
          thenHave((a, b) ∈ f ==> b ∈ T2(a)) by InstantiateForall(a, b)
          val stmt3 = thenHave(b ∈ T2(a)) by Tautology.fromLastStep()
          have(a ∈ T1 ==> T2(a) ⊆ T2p(a)) by InstantiateForall(a)(pred)
          thenHave(T2(a) ⊆ T2p(a)) by Tautology.fromLastStep(
            stmt1,
            Subset.membership of (x := f, y := (T1 × ⋃({ T2(a) | a ∈ T1 })), z := (a, b)),
            CartesianProduct.pairMembership of (x := a, y := b, A := T1, B := ⋃({ T2(a) | a ∈ T1 }))
          )
          thenHave(thesis) by Tautology.fromLastStep(
            stmt3,
            Subset.membership of (x := T2(a), y := T2p(a), z := b)
          )
        }
        thenHave(∀(b, (a, b) ∈ f ==> b ∈ T2p(a))) by RightForall
        thenHave(thesis) by RightForall
      }

      have(f ∈ { f ∈ 𝒫(T1 × ⋃({ T2p(a) | a ∈ T1 })) | (∀(x ∈ T1, ∃!(y, (x, y) ∈ f))) /\ (∀(a, ∀(b, (a, b) ∈ f ==> (b ∈ T2p(a))))) }) by Tautology.from(
        cond1,
        cond2,
        cond3,
        piExpansion of (e1 := f, T2 := T2p)
      )
      thenHave(f ∈ Π(x :: T1, T2p(x))) by Substitute(Pi.definition of (T2 := T2p))
    }
    thenHave(∀(f ∈ Π(x :: T, T2(x)), f ∈ Π(x :: T1, T2p(x)))) by RightForall
    thenHave(thesis) by Tautology.fromLastStep(Subset.definition of (x := Π(x :: T, T2(x)), y := Π(x :: T1, T2p(x)), z := f))
  }
