package lisa.maths.Arithmetic

import lisa.maths.SetTheory.Base.Predef.{*, given}
import lisa.maths.Quantifiers
import lisa.maths.SetTheory.Functions.Predef.*
import lisa.maths.SetTheory.Functions.BasicTheorems as FunBasicTheorems
import lisa.maths.SetTheory.Functions.Operations.Restriction
import lisa.maths.SetTheory.Base.{CartesianProduct, EmptySet, FoundationAxiom, Intersection, Singleton, Union}
import lisa.maths.SetTheory.Order.Predef.*
import lisa.maths.SetTheory.Relations.BasicTheorems
import lisa.maths.SetTheory.Relations.WellFoundedRelation.wellFounded
import lisa.maths.SetTheory.Order.WellOrders.{InitialSegment, WellOrder, WellOrderedRecursion}
import lisa.maths.SetTheory.Order.WellOrders.WellOrder.wellOrder

/**
 * Set-theory lemmas that arithmetic depends on but that are missing from the
 * current set-theory library.
 *
 * IMPORTANT: we add them here (in Arithmetic) instead of editing set-theory files.
 */
object Necessary extends lisa.Main {
  private val A, R = variable[Set]
  private val f = variable[Set]
  private val x, y, z = variable[Set]
  private val a = variable[Set]
  private val m0 = variable[Set]
  private val B, t = variable[Set]
  // Binary functional used for generic well-ordered recursion existence.
  // We intentionally name it `F` so `.of(F := ...)` instantiations target this symbol (and not the unary class-function `F`).
  private val F = variable[Set >>: Set >>: Set]
  // NOTE: do not name this `F` (it collides with the widely-used class-function symbol `F : Set -> Set`).
  val Func = variable[Set >>: Set >>: Set]
  private val G = variable[Set]

  extension (f: Expr[Set]) {
    private inline def apply(x: Expr[Set]): Expr[Set] = app(f)(x)
  }

  /**
   * A recursion operator that returns a *function on* `A` satisfying the recursion equation (Arithmetic-local).
   *
   * NOTE: `lazy` to avoid initialization-order issues (it depends on later theorems in this file).
   */
  lazy val recursiveFunctionOn = DEF(
    λ(
      Func,
      λ(
        A,
        λ(
          R,
          ε(
            G,
            (λ(
              G,
              functionOn(G)(A) /\
                ∀(x ∈ A, G(x) === Func(x)(G ↾ InitialSegment.initialSegment(x)(A)(R)))
            ))(G)
          )
        )
      )
    )
  )

  /**
   * Spec lemma for `recursiveFunctionOn` (Arithmetic-local).
   *
   * NOTE: `lazy` to avoid initialization-order issues.
   */
  lazy val recursiveFunctionOnSpec = Theorem(
    WellOrder.wellOrder(A)(R) |-
      (functionOn(recursiveFunctionOn(Func)(A)(R))(A) /\
        ∀(
          x ∈ A,
          recursiveFunctionOn(Func)(A)(R)(x) ===
            Func(x)(recursiveFunctionOn(Func)(A)(R) ↾ InitialSegment.initialSegment(x)(A)(R))
        ))
  ) {
    assume(WellOrder.wellOrder(A)(R))

    val body = functionOn(G)(A) /\
      ∀(x ∈ A, G(x) === Func(x)(G ↾ InitialSegment.initialSegment(x)(A)(R)))

    val PredG = λ(G, body)

    val ex0 = have(∃(G, body)).by(Restate.from(wellOrderedRecursionExistence.of(F := Func)))
    val exG = have(∃(G, PredG(G))).by(Restate.from(ex0))

    val epsProp = have(PredG(ε(G, PredG(G)))).by(
      Cut(exG, Quantifiers.existsEpsilon.of(x := G, P := PredG))
    )

    val defEq = recursiveFunctionOn.definition.of(Func := Func, A := A, R := R)

    val epsAbs = have(Abs(G, body)(ε(G, Abs(G, body)(G)))).by(Restate.from(epsProp))
    val rec = recursiveFunctionOn(Func)(A)(R)
    val eps = ε(G, Abs(G, body)(G))

    val defEq0 = have(rec === eps).by(Restate.from(defEq))
    val defEqSym = have(eps === rec).by(Cut(defEq0, have(rec === eps |- eps === rec).by(Congruence)))

    val absOnRec = have(Abs(G, body)(rec)).by(
      Cut(
        defEqSym,
        have(eps === rec |- Abs(G, body)(rec)) subproof {
          assume(eps === rec)
          val epsAbsW = have(Abs(G, body)(eps)).by(Weakening(epsAbs))
          have(Abs(G, body)(rec)).by(
            RightSubstEq.withParametersSimple(List((eps, rec)), (Seq(t), Abs(G, body)(t)))(epsAbsW)
          )
        }
      )
    )
    have(thesis).by(Restate.from(absOnRec))
  }

  private val inAImpliesNeqM = Lemma((z ∈ A, m0 ∉ A) |- ¬(z === m0)) {
    val zInA = assume(z ∈ A); val mNotInA = assume(m0 ∉ A)
    have(z === m0 |- ()) subproof {
      val zEqm = assume(z === m0)
      val mInA = have(m0 ∈ A).by(Congruence.from(zInA, zEqm))
      have(thesis).by(Tautology.from(mInA, mNotInA))
    }
    thenHave(thesis).by(Restate)
  }

  private val successorSetMembership = Lemma(z ∈ (A ∪ singleton(m0)) <=> (z ∈ A) \/ (z === m0)) {
    have(thesis).by(Tautology.from(Union.membership.of(x := A, y := singleton(m0), z := z), Singleton.membership.of(x := m0, y := z)))
  }

  private val successorRelMembership = Lemma((x, y) ∈ ((R ∩ (A × A)) ∪ (A × singleton(m0))) <=> ((((x, y) ∈ R) /\ (x ∈ A) /\ (y ∈ A)) \/ ((x ∈ A) /\ (y === m0)))) {
    have(thesis).by(Tautology.from(
      Union.membership.of(x := (R ∩ (A × A)), y := (A × singleton(m0)), z := (x, y)),
      Intersection.membership.of(x := R, y := (A × A), z := (x, y)),
      CartesianProduct.pairMembership.of(A := A, B := A, x := x, y := y),
      CartesianProduct.pairMembership.of(A := A, B := singleton(m0), x := x, y := y),
      Singleton.membership.of(x := m0, y := y)
    ))
  }

  /** Restriction application (Arithmetic-local): if `f` is a function on `A` and `x ∈ A`, then `(f ↾ A)(x) = f(x)`. */
  val restrictionApp = Lemma((functionOn(f)(A), x ∈ A) |- (f ↾ A)(x) === f(x)) {
    val fOnA = assume(functionOn(f)(A))
    val xInA = assume(x ∈ A)

    val funF = have(function(f)).by(Tautology.from(FunBasicTheorems.functionOnIsFunction.of(f := f, A := A), fOnA))
    val domF = have(dom(f) === A).by(Tautology.from(FunBasicTheorems.functionOnDomain.of(f := f, A := A), fOnA))
    val xInDomF = have(x ∈ dom(f)).by(Congruence.from(xInA, domF))

    have(thesis).by(Tautology.from(
      Restriction.restrictedApp.of(f := f, A := A, x := x),
      funF,
      xInDomF,
      xInA
    ))
  }

  /**
   * Restriction application on subsets (Arithmetic-local):
   * if `f` is a function on `A`, `B ⊆ A` and `x ∈ B`, then `(f ↾ B)(x) = f(x)`.
   */
  val restrictionAppSubset = Lemma((functionOn(f)(A), B ⊆ A, x ∈ B) |- (f ↾ B)(x) === f(x)) {
    val fOnA = assume(functionOn(f)(A))
    val BSubA = assume(B ⊆ A)
    val xInB = assume(x ∈ B)

    val funF = have(function(f)).by(Tautology.from(FunBasicTheorems.functionOnIsFunction.of(f := f, A := A), fOnA))
    val domF = have(dom(f) === A).by(Tautology.from(FunBasicTheorems.functionOnDomain.of(f := f, A := A), fOnA))

    val xInA = have(x ∈ A).by(Tautology.from(Subset.membership.of(x := B, y := A, z := x), BSubA, xInB))
    val xInDomF = have(x ∈ dom(f)).by(Congruence.from(xInA, domF))

    have(thesis).by(Tautology.from(
      Restriction.restrictedApp.of(f := f, A := B, x := x),
      funF,
      xInDomF,
      xInB
    ))
  }

  /**
   * Successor well-order (Arithmetic-local).
   *
   * If `(A, R)` is a well-order and `m ∉ A`, then adding a fresh top element `m`
   * yields a well-order on `A ∪ {m}`.
   */
  private val successorWellOrder = Theorem(
    (WellOrder.wellOrder(A)(R), m0 ∉ A) |- WellOrder.wellOrder(A ∪ singleton(m0))((R ∩ (A × A)) ∪ (A × singleton(m0)))
  ) {
    val woAR = assume(WellOrder.wellOrder(A)(R))
    val `m∉A` = assume(m0 ∉ A)

    val m = m0
    val A2 = A ∪ singleton(m)
    val R0 = R ∩ (A × A)
    val R2 = R0 ∪ (A × singleton(m))

    // Membership characterizations for A2 and R2.
    val `A2.mem` = have(z ∈ A2 <=> (z ∈ A) \/ (z === m)).by(Tautology.from(successorSetMembership.of(m0 := m)))
    val `R2.mem` = have((x, y) ∈ R2 <=> ((((x, y) ∈ R) /\ (x ∈ A) /\ (y ∈ A)) \/ ((x ∈ A) /\ (y === m)))).by(Tautology.from(successorRelMembership.of(m0 := m)))

    val `m∈A2` = have(m ∈ A2).by(Tautology.from(Union.membership.of(x := A, y := singleton(m), z := m), Singleton.membership.of(x := m, y := m)))

    // Prove that (A2, R2) is a well-order.
    val `R.trans` = have(transitive(R)(A)).by(Tautology.from(WellOrder.transitivity.of(A := A, < := R), woAR))
    val `R.total` = have(total(R)(A)).by(Tautology.from(WellOrder.totality.of(A := A, < := R), woAR))
    val `R.irrefl` = have(irreflexive(R)(A)).by(Tautology.from(WellOrder.irreflexivity.of(A := A, < := R), woAR))

    val `A⊆A2` = have(A ⊆ A2).by(Tautology.from(Union.leftSubset.of(x := A, y := singleton(m))))
    val `{m}⊆A2` = have(singleton(m) ⊆ A2).by(Tautology.from(Union.rightSubset.of(x := A, y := singleton(m))))

    // relation(R2)
    val `R2⊆A2×A2` = have(R2 ⊆ (A2 × A2)) subproof {
      val `A×A⊆A2×A2` = have((A × A) ⊆ (A2 × A2)).by(Tautology.from(CartesianProduct.monotonic.of(A := A, B := A, C := A2, D := A2), `A⊆A2`, `A⊆A2`))
      val `R0⊆A×A` = have(R0 ⊆ (A × A)).by(Tautology.from(Intersection.subsetRight.of(x := R, y := (A × A))))
      val `R0⊆A2×A2` = have(R0 ⊆ (A2 × A2)).by(Tautology.from(Subset.transitivity.of(x := R0, y := (A × A), z := (A2 × A2)), `R0⊆A×A`, `A×A⊆A2×A2`))
      val `A×{m}⊆A2×A2` = have((A × singleton(m)) ⊆ (A2 × A2)).by(Tautology.from(CartesianProduct.monotonic.of(A := A, B := singleton(m), C := A2, D := A2), `A⊆A2`, `{m}⊆A2`))
      have(thesis).by(Tautology.from(Union.leftUnionSubset.of(x := R0, y := (A × singleton(m)), z := (A2 × A2)), `R0⊆A2×A2`, `A×{m}⊆A2×A2`))
    }
    val relBetweenR2 = have(relationBetween(R2)(A2)(A2)).by(Tautology.from(relationBetween.definition.of(R := R2, X := A2, Y := A2), `R2⊆A2×A2`))
    val `relation(R2)` = have(relation(R2)).by(Tautology.from(BasicTheorems.relationBetweenIsRelation.of(R := R2, X := A2, Y := A2), relBetweenR2))

    // irreflexive(R2)(A2)
    val `irrefl(R2)(A2)` = have(irreflexive(R2)(A2)) subproof {
      have(z ∈ A2 |- ¬((z, z) ∈ R2)) subproof {
        assume(z ∈ A2)
        val zCases = have((z ∈ A) \/ (z === m)).by(Tautology.from(`A2.mem`))
        val zInA = have(z ∈ A |- ¬((z, z) ∈ R2)) subproof {
          val zInA = assume(z ∈ A)

          val zNeqM = have(¬(z === m)).by(Tautology.from(inAImpliesNeqM.of(m0 := m), zInA, `m∉A`))

          val notzzInR = have(¬(z R z)).by(Tautology.from(BasicTheorems.appliedIrreflexivity.of(R := R, X := A, x := z), `R.irrefl`, zInA))

          have((z, z) ∈ R2 |- ()) subproof {
            val zzInR2 = assume((z, z) ∈ R2)
            val zzInR = have((z, z) ∈ R).by(Tautology.from(`R2.mem` of (x := z, y := z), zzInR2, zNeqM))
            have(thesis).by(Tautology.from(notzzInR, zzInR))
          }
          thenHave(thesis).by(Restate)
        }
        val zEqm = have(z === m |- ¬((z, z) ∈ R2)) subproof {
          val zEqmFact = assume(z === m)
          val zInA_fromR2 = have((z, z) ∈ R2 |- z ∈ A).by(Tautology.from(`R2.mem` of (x := z, y := z)))
          have((z, z) ∈ R2 |- ()) subproof {
            val zzInR2 = assume((z, z) ∈ R2)
            val zInA = have(z ∈ A).by(Tautology.from(zzInR2, zInA_fromR2))
            val mInA = have(m ∈ A).by(Congruence.from(zInA, zEqmFact))
            have(thesis).by(Tautology.from(mInA, `m∉A`))
          }
          thenHave(thesis).by(Restate)
        }
        have(thesis).by(Tautology.from(zCases, zInA, zEqm))
      }
      thenHave(z ∈ A2 ==> ¬((z, z) ∈ R2)).by(Restate)
      thenHave(∀(z ∈ A2, ¬((z, z) ∈ R2))).by(RightForall)
      have(thesis).by(Tautology.from(irreflexive.definition.of(R := R2, X := A2), lastStep))
    }

    // transitive(R2)(A2)
    val `trans(R2)(A2)` = have(transitive(R2)(A2)) subproof {
      have((x ∈ A2, y ∈ A2, z ∈ A2, (x, y) ∈ R2, (y, z) ∈ R2) |- (x, z) ∈ R2) subproof {
        assume(x ∈ A2)
        assume(y ∈ A2)
        assume(z ∈ A2)
        val xyInR2 = assume((x, y) ∈ R2)
        val yzInR2 = assume((y, z) ∈ R2)

        val `x∈A` = have(x ∈ A).by(Tautology.from(`R2.mem` of (x := x, y := y), xyInR2))
        val `y∈A` = have(y ∈ A).by(Tautology.from(`R2.mem` of (x := y, y := z), yzInR2))
        val zCases = have((z ∈ A) \/ (z === m)).by(Tautology.from(`A2.mem` of (z := z)))

        val zEqm = have(z === m |- (x, z) ∈ R2) subproof {
          val zEqm = assume(z === m)
          have(thesis).by(Tautology.from(`R2.mem` of (x := x, y := z), `x∈A`, zEqm))
        }

        val zInA = have(z ∈ A |- (x, z) ∈ R2) subproof {
          val zInA_fact = assume(z ∈ A)

          val yNeqM = have(¬(y === m)).by(Tautology.from(inAImpliesNeqM.of(z := y, m0 := m), `y∈A`, `m∉A`))

          val zNeqM = have(¬(z === m)).by(Tautology.from(inAImpliesNeqM.of(z := z, m0 := m), zInA_fact, `m∉A`))

          val `xy∈R` = have((x, y) ∈ R).by(Tautology.from(`R2.mem` of (x := x, y := y), xyInR2, yNeqM))
          val `yz∈R` = have((y, z) ∈ R).by(Tautology.from(`R2.mem` of (x := y, y := z), yzInR2, zNeqM))
          val xzInR = have((x, z) ∈ R).by(Tautology.from(BasicTheorems.appliedTransitivity.of(R := R, X := A, x := x, y := y, z := z), `R.trans`, `x∈A`, `y∈A`, zInA_fact, `xy∈R`, `yz∈R`))
          have(((x, z) ∈ R) /\ (x ∈ A) /\ (z ∈ A)).by(Tautology.from(xzInR, `x∈A`, zInA_fact))
          thenHave((x, z) ∈ R2).by(Tautology.fromLastStep(`R2.mem` of (x := x, y := z)))
          thenHave(thesis).by(Restate)
        }

        have(thesis).by(Tautology.from(zCases, zEqm, zInA))
      }
      thenHave(() |- ((x ∈ A2) /\ (y ∈ A2) /\ (z ∈ A2) /\ ((x, y) ∈ R2) /\ ((y, z) ∈ R2)) ==> (x, z) ∈ R2).by(Tableau)
      thenHave(() |- ∀(z, ((x ∈ A2) /\ (y ∈ A2) /\ (z ∈ A2) /\ ((x, y) ∈ R2) /\ ((y, z) ∈ R2)) ==> (x, z) ∈ R2)).by(RightForall)
      thenHave(() |- ∀(y, ∀(z, ((x ∈ A2) /\ (y ∈ A2) /\ (z ∈ A2) /\ ((x, y) ∈ R2) /\ ((y, z) ∈ R2)) ==> (x, z) ∈ R2))).by(RightForall)
      thenHave(() |- ∀(x, ∀(y, ∀(z, ((x ∈ A2) /\ (y ∈ A2) /\ (z ∈ A2) /\ ((x, y) ∈ R2) /\ ((y, z) ∈ R2)) ==> (x, z) ∈ R2)))).by(RightForall)
      thenHave(∀(x ∈ A2, ∀(y ∈ A2, ∀(z ∈ A2, ((x, y) ∈ R2) /\ ((y, z) ∈ R2) ==> (x, z) ∈ R2)))).by(Tableau)
      have(thesis).by(Tautology.from(transitive.definition.of(R := R2, X := A2), lastStep))
    }

    // total(R2)(A2)
    val `total(R2)(A2)` = have(total(R2)(A2)) subproof {
      have((x ∈ A2, y ∈ A2) |- ((x, y) ∈ R2) \/ ((y, x) ∈ R2) \/ (x === y)) subproof {
        assume(x ∈ A2)
        assume(y ∈ A2)
        val xCases = have((x ∈ A) \/ (x === m)).by(Tautology.from(`A2.mem` of (z := x)))
        val yCases = have((y ∈ A) \/ (y === m)).by(Tautology.from(`A2.mem` of (z := y)))

        val bothInA = have((x ∈ A, y ∈ A) |- ((x, y) ∈ R2) \/ ((y, x) ∈ R2) \/ (x === y)) subproof {
          assume(x ∈ A)
          assume(y ∈ A)
          val totR = have((x ∈ A, y ∈ A) |- ((x, y) ∈ R) \/ ((y, x) ∈ R) \/ (x === y)).by(Tautology.from(BasicTheorems.appliedTotality.of(R := R, X := A, x := x, y := y), `R.total`))
          have(thesis).by(Tautology.from(totR, `R2.mem` of (x := x, y := y), `R2.mem` of (x := y, y := x)))
        }

        val xEqm_yInA = have((x === m, y ∈ A) |- ((x, y) ∈ R2) \/ ((y, x) ∈ R2) \/ (x === y)).by(
          Tautology.from(`R2.mem` of (x := y, y := x))
        )

        val xInA_yEqm = have((x ∈ A, y === m) |- ((x, y) ∈ R2) \/ ((y, x) ∈ R2) \/ (x === y)).by(
          Tautology.from(`R2.mem` of (x := x, y := y))
        )
        val bothEqm = have((x === m, y === m) |- ((x, y) ∈ R2) \/ ((y, x) ∈ R2) \/ (x === y)) subproof {
          assume(x === m)
          assume(y === m)
          have(x === y).by(Congruence)
          thenHave(thesis).by(Tautology)
        }
        have(thesis).by(Tautology.from(xCases, yCases, bothInA, xEqm_yInA, xInA_yEqm, bothEqm))
      }
      thenHave(() |- ((x ∈ A2) /\ (y ∈ A2)) ==> ((x, y) ∈ R2) \/ ((y, x) ∈ R2) \/ (x === y)).by(Tableau)
      thenHave(() |- ∀(y, ((x ∈ A2) /\ (y ∈ A2)) ==> ((x, y) ∈ R2) \/ ((y, x) ∈ R2) \/ (x === y))).by(RightForall)
      thenHave(() |- ∀(x, ∀(y, ((x ∈ A2) /\ (y ∈ A2)) ==> ((x, y) ∈ R2) \/ ((y, x) ∈ R2) \/ (x === y)))).by(RightForall)
      thenHave(∀(x ∈ A2, ∀(y ∈ A2, ((x, y) ∈ R2) \/ ((y, x) ∈ R2) \/ (x === y)))).by(Tableau)
      have(thesis).by(Tautology.from(total.definition.of(R := R2, X := A2), lastStep))
    }

    // strictTotalOrder(A2)(R2)
    val `strictPartialOrder(A2)(R2)` = have(strictPartialOrder(A2)(R2)).by(Tautology.from(strictPartialOrder.definition.of(A := A2, < := R2), `relation(R2)`, `trans(R2)(A2)`, `irrefl(R2)(A2)`))
    val `strictTotalOrder(A2)(R2)` = have(strictTotalOrder(A2)(R2)).by(Tautology.from(strictTotalOrder.definition.of(A := A2, < := R2), `strictPartialOrder(A2)(R2)`, `total(R2)(A2)`))

    // wellFounded(R2)(A2)
    val `wellFounded(R2)(A2)` = have(wellFounded(R2)(A2)) subproof {
      val T = B ∩ A
      val `T⊆A` = have(T ⊆ A).by(Tautology.from(Intersection.subsetRight.of(x := B, y := A)))

      have((B ⊆ A2, B ≠ ∅) |- ∃(t, minimal(t)(B)(R2))) subproof {
        val `B⊆A2` = assume(B ⊆ A2)
        val `B≠∅` = assume(B ≠ ∅)

        val em = have((T === ∅) \/ (T ≠ ∅)).by(Tautology)

        val Tnonempty = have(T ≠ ∅ |- ∃(t, minimal(t)(B)(R2))) subproof {
          val `T≠∅` = assume(T ≠ ∅)
          val minT = have(∃(t, minimal(t)(T)(R))).by(Tautology.from(WellOrder.minimalElement.of(A := A, < := R, B := T), woAR, `T⊆A`, `T≠∅`))

          have(minimal(t)(T)(R) |- minimal(t)(B)(R2)) subproof {
            assume(minimal(t)(T)(R))
            val `t∈T` = have(t ∈ T).by(Tautology.from(minimal.definition.of(a := t, A := T, < := R)))
            val `t∈B` = have(t ∈ B).by(Tautology.from(`t∈T`, Intersection.membership.of(x := B, y := A, z := t)))
            val `t∈A` = have(t ∈ A).by(Tautology.from(`t∈T`, Intersection.membership.of(x := B, y := A, z := t)))
            val noPredT = have(∀(z, z ∈ T ==> ¬((z, t) ∈ R))).by(Tautology.from(minimal.definition.of(a := t, A := T, < := R)))
            // Show: ∀z∈B, ¬(z R2 t)
            val tNeqM = have(¬(t === m)).by(Tautology.from(inAImpliesNeqM.of(z := t, m0 := m), `t∈A`, `m∉A`))

            have(z ∈ B |- ¬((z, t) ∈ R2)) subproof {
              val zInB = assume(z ∈ B)
              have((z, t) ∈ R2 |- ()) subproof {
                val ztInR2 = assume((z, t) ∈ R2)
                val zInT = have(z ∈ T).by(Tautology.from(Intersection.membership.of(x := B, y := A, z := z), zInB, `R2.mem` of (x := z, y := t), ztInR2, tNeqM))
                val noPredImp = have(z ∈ T ==> ¬((z, t) ∈ R)).by(InstantiateForall(z)(noPredT))
                val zNotRt = have(¬((z, t) ∈ R)).by(Tautology.from(noPredImp, zInT))
                have(thesis).by(Tautology.from(`R2.mem` of (x := z, y := t), ztInR2, tNeqM, zNotRt))
              }
              thenHave(thesis).by(Restate)
            }
            thenHave(z ∈ B ==> ¬((z, t) ∈ R2)).by(Restate)
            val noPredB = thenHave(∀(z, z ∈ B ==> ¬((z, t) ∈ R2))).by(Generalize)
            have(thesis).by(Tautology.from(minimal.definition.of(a := t, A := B, < := R2), `t∈B`, noPredB))
          }
          thenHave(minimal(t)(T)(R) |- ∃(t, minimal(t)(B)(R2))).by(RightExists)
          thenHave(∃(t, minimal(t)(T)(R)) |- ∃(t, minimal(t)(B)(R2))).by(LeftExists)
          have(thesis).by(Cut(minT, lastStep))
        }

        val Tempty = have(T === ∅ |- ∃(t, minimal(t)(B)(R2))) subproof {
          val `T=∅` = assume(T === ∅)
          // Show m ∈ B.
          val `∃y y∈B` = have(∃(y, y ∈ B)).by(Tautology.from(EmptySet.nonEmptyHasElement.of(x := B), `B≠∅`))
          val b0 = ε(y, y ∈ B)
          val `b0∈B` = have(b0 ∈ B).by(Cut(`∃y y∈B`, Quantifiers.existsEpsilon.of(x := y, P := λ(y, y ∈ B))))
          val b0InA2 = have(b0 ∈ A2).by(Tautology.from(Subset.membership.of(x := B, y := A2, z := b0), `B⊆A2`, `b0∈B`))
          val b0Cases = have((b0 ∈ A) \/ (b0 === m)).by(Tautology.from(`A2.mem` of (z := b0), b0InA2))
          val b0NotInA = have(b0 ∈ A |- ()) subproof {
            assume(b0 ∈ A)
            have(b0 ∈ T).by(Tautology.from(Intersection.membership.of(x := B, y := A, z := b0), `b0∈B`, lastStep))
            have(b0 ∈ ∅).by(Congruence.from(lastStep, `T=∅`))
            have(thesis).by(Tautology.from(lastStep, EmptySet.definition.of(x := b0)))
          }
          val `b0=m` = have(b0 === m).by(Tautology.from(b0Cases, b0NotInA))
          val `m∈B` = have(m ∈ B).by(Congruence.from(`b0∈B`, `b0=m`))

          // Show: ∀z∈B, ¬(z R2 m).
          val noPredM = have(∀(z, z ∈ B ==> ¬((z, m) ∈ R2))) subproof {
            have(z ∈ B |- ¬((z, m) ∈ R2)) subproof {
              val `z∈B` = assume(z ∈ B)
              have((z, m) ∈ R2 |- ()) subproof {
                val zInA = have((z, m) ∈ R2 |- z ∈ A).by(Weakening(`R2.mem` of (x := z, y := m)))
                val zInT = have((z, m) ∈ R2 |- z ∈ T).by(Tautology.from(Intersection.membership.of(x := B, y := A, z := z), `z∈B`, zInA))
                have((z, m) ∈ R2 |- z ∈ ∅) by Congruence.from(zInT, `T=∅`)
                thenHave((z, m) ∈ R2 |- ()).by(Tautology.fromLastStep(EmptySet.definition.of(x := z)))
              }
              thenHave(thesis).by(Restate)
            }
            thenHave(z ∈ B ==> ¬((z, m) ∈ R2)).by(Restate)
            thenHave(∀(z, z ∈ B ==> ¬((z, m) ∈ R2))).by(Generalize)
          }

          have(minimal(m)(B)(R2)).by(Tautology.from(minimal.definition.of(a := m, A := B, < := R2), `m∈B`, noPredM))
          thenHave(thesis).by(RightExists)
        }

        have(thesis).by(Tautology.from(em, Tnonempty, Tempty))
      }

      thenHave((WellOrder.wellOrder(A)(R), m ∉ A, B ⊆ A2, B ≠ ∅) |- ∃(t, minimal(t)(B)(R2))).by(Restate)
      thenHave((WellOrder.wellOrder(A)(R), m ∉ A) |- ((B ⊆ A2) /\ (B ≠ ∅)) ==> ∃(t, minimal(t)(B)(R2))).by(Tableau)
      thenHave((WellOrder.wellOrder(A)(R), m ∉ A) |- ∀(B, (B ⊆ A2) /\ (B ≠ ∅) ==> ∃(t, minimal(t)(B)(R2)))).by(RightForall)
      have(thesis).by(Tautology.from(wellFounded.definition.of(R := R2, X := A2), lastStep))
    }

    have(thesis).by(Tautology.from(WellOrder.wellOrder.definition.of(A := A2, < := R2), `strictTotalOrder(A2)(R2)`, `wellFounded(R2)(A2)`))
  }

  /**
   * Well-ordered recursion existence (Arithmetic-local).
   */
  val wellOrderedRecursionExistence = Theorem(
    WellOrder.wellOrder(A)(R) |- ∃(G, functionOn(G)(A) /\ ∀(x ∈ A, G(x) === F(x)(G ↾ InitialSegment.initialSegment(x)(A)(R))))
  ) {
    val woAR = assume(WellOrder.wellOrder(A)(R))

    // Pick a fresh element m ∉ A.
    val m = ε(y, y ∉ A)
    val `∃y y∉A` = have(∃(y, y ∉ A)).by(Tautology.from(FoundationAxiom.freshElement.of(x := A)))
    val `m∉A` = have(m ∉ A).by(Cut(`∃y y∉A`, Quantifiers.existsEpsilon.of(x := y, P := λ(y, y ∉ A))))

    // Successor set and successor relation.
    val A2 = A ∪ singleton(m)
    val R0 = R ∩ (A × A)
    val R2 = R0 ∪ (A × singleton(m))

    // Membership characterizations for A2 and R2.
    val `A2.mem` = have(z ∈ A2 <=> (z ∈ A) \/ (z === m)).by(Tautology.from(successorSetMembership.of(m0 := m)))
    val `R2.mem` = have((x, y) ∈ R2 <=> ((((x, y) ∈ R) /\ (x ∈ A) /\ (y ∈ A)) \/ ((x ∈ A) /\ (y === m)))).by(Tautology.from(successorRelMembership.of(m0 := m)))

    val `m∈A2` = have(m ∈ A2).by(Tautology.from(Union.membership.of(x := A, y := singleton(m), z := m), Singleton.membership.of(x := m, y := m)))

    val `wellOrder(A2)(R2)` = have(WellOrder.wellOrder(A2)(R2)).by(Tautology.from(successorWellOrder.of(m0 := m), woAR, `m∉A`))

    // 2) Compute initial segments in the successor well-order.
    val `initSeg(m)=A` = have(InitialSegment.initialSegment(m)(A2)(R2) === A) subproof {
      val memDef = InitialSegment.membership.of(x := m, A := A2, < := R2, y := z)
      val mRefl = have(m === m).by(Restate)
      have(z ∈ InitialSegment.initialSegment(m)(A2)(R2) <=> z ∈ A).by(Tautology.from(memDef, `A2.mem` of (z := z), `R2.mem` of (x := z, y := m), `m∉A`, mRefl))
      thenHave(thesis).by(Extensionality)
    }

    val `initSeg-on-A` = have(x ∈ A |- InitialSegment.initialSegment(x)(A2)(R2) === InitialSegment.initialSegment(x)(A)(R)) subproof {
      val `x∈A` = assume(x ∈ A)
      val memA2 = InitialSegment.membership.of(x := x, A := A2, < := R2, y := z)
      val memA = InitialSegment.membership.of(x := x, A := A, < := R, y := z)

      val xNeqM = have(¬(x === m)).by(Tautology.from(inAImpliesNeqM.of(z := x, m0 := m), `x∈A`, `m∉A`))

      have(z ∈ InitialSegment.initialSegment(x)(A2)(R2) <=> z ∈ InitialSegment.initialSegment(x)(A)(R)).by(Tautology.from(memA2, memA, `A2.mem` of (z := z), `R2.mem` of (x := z, y := x), `x∈A`, xNeqM))
      thenHave(thesis).by(Extensionality)
    }

    // 3) Apply recursiveSequence at the top element A2 = A ∪ singleton(m) to obtain an approximation until m.
    val recSeqInst = WellOrderedRecursion.recursiveSequence.of(A := A2, < := R2, F := F)
    val recSeq = have(recSeqInst.result.right.head).by(Cut(`wellOrder(A2)(R2)`, recSeqInst))
    val Pm = (m ∈ A2) /\ functionOn(G)(InitialSegment.initialSegment(m)(A2)(R2)) /\
      ∀(a ∈ InitialSegment.initialSegment(m)(A2)(R2), G(a) === F(a)(G ↾ InitialSegment.initialSegment(a)(A2)(R2)))
    val recAtM_sequent = have(m ∈ A2 |- Quantifiers.∃!(G, Pm)).by(InstantiateForall(m)(recSeq))
    val recAtM = have(Quantifiers.∃!(G, Pm)).by(Tautology.from(recAtM_sequent, `m∈A2`))
    val exAtM = have(∃(G, Pm)).by(Tautology.from(recAtM, Quantifiers.existsOneImpliesExists.of(P := λ(G, Pm))))

    val exAtM_wo = have(WellOrder.wellOrder(A)(R) |- ∃(G, Pm)).by(Weakening(exAtM))

    have(thesis) subproof {
      have(
        Pm
        |- functionOn(G)(A) /\ ∀(x ∈ A, G(x) === F(x)(G ↾ InitialSegment.initialSegment(x)(A)(R)))
      ) subproof {
        assume(Pm)

        val funOnInit = have(functionOn(G)(InitialSegment.initialSegment(m)(A2)(R2))).by(Tautology)
        val funOnA = have(functionOn(G)(A)).by(Congruence.from(funOnInit, `initSeg(m)=A`))

        val eqOnInit = have(∀(a ∈ InitialSegment.initialSegment(m)(A2)(R2), G(a) === F(a)(G ↾ InitialSegment.initialSegment(a)(A2)(R2)))).by(Tautology)
        val eqAtX = have(x ∈ InitialSegment.initialSegment(m)(A2)(R2) |- G(x) === F(x)(G ↾ InitialSegment.initialSegment(x)(A2)(R2))).by(InstantiateForall(x)(eqOnInit))

        have(x ∈ A |- G(x) === F(x)(G ↾ InitialSegment.initialSegment(x)(A)(R))) subproof {
          val xInA_fact = assume(x ∈ A)
          val xInInit = have(x ∈ InitialSegment.initialSegment(m)(A2)(R2)).by(Congruence.from(xInA_fact, `initSeg(m)=A`))
          val step1 = have(G(x) === F(x)(G ↾ InitialSegment.initialSegment(x)(A2)(R2))).by(Tautology.from(eqAtX, xInInit))
          val segEq = have(InitialSegment.initialSegment(x)(A2)(R2) === InitialSegment.initialSegment(x)(A)(R)).by(Tautology.from(`initSeg-on-A`, xInA_fact))
          have(thesis).by(Congruence.from(step1, segEq))
        }
        thenHave((x ∈ A) ==> (G(x) === F(x)(G ↾ InitialSegment.initialSegment(x)(A)(R)))).by(Restate)
        thenHave(∀(x, (x ∈ A) ==> (G(x) === F(x)(G ↾ InitialSegment.initialSegment(x)(A)(R))))).by(RightForall)
        have(thesis).by(Tautology.from(funOnA, lastStep))
      }
      thenHave((WellOrder.wellOrder(A)(R), Pm) |- functionOn(G)(A) /\ ∀(x ∈ A, G(x) === F(x)(G ↾ InitialSegment.initialSegment(x)(A)(R)))).by(Weakening)
      thenHave((WellOrder.wellOrder(A)(R), Pm) |- ∃(G, functionOn(G)(A) /\ ∀(x ∈ A, G(x) === F(x)(G ↾ InitialSegment.initialSegment(x)(A)(R))))).by(RightExists)
      thenHave((WellOrder.wellOrder(A)(R), ∃(G, Pm)) |- ∃(G, functionOn(G)(A) /\ ∀(x ∈ A, G(x) === F(x)(G ↾ InitialSegment.initialSegment(x)(A)(R))))).by(LeftExists)
      have(thesis).by(Cut(exAtM_wo, lastStep))
    }
  }

}

