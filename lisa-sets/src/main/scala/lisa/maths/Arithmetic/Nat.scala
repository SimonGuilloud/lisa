package lisa.maths.Arithmetic

import lisa.maths.Arithmetic.Predef.{*, given}
import lisa.maths.Quantifiers
import lisa.maths.SetTheory.SetTheory.{inductive, successor}
import lisa.maths.SetTheory.Base.{Singleton, Subset, Union}
import lisa.maths.SetTheory.Base.FoundationAxiom
import lisa.maths.SetTheory.Order.Extrema
import lisa.maths.SetTheory.Order.Predef.*
import lisa.maths.SetTheory.Relations.Examples.MembershipRelation
import lisa.maths.SetTheory.Relations.WellFoundedRelation.wellFounded
import lisa.maths.SetTheory.Functions.Predef.*
import lisa.maths.SetTheory.Order.WellOrders.{WellOrder, WellOrderedRecursion}
import lisa.maths.SetTheory.Order.WellOrders.InitialSegment
import lisa.maths.SetTheory.Ordinals.TransitiveSet
import scala.languageFeature.higherKinds

/**
 * Natural numbers (work-in-progress).
 *
 * This file currently provides an *axiomatic* interface for `ℕ`, successor, addition and multiplication,
 * together with an induction principle.
 *
 * Goal (see `GOALS.md`): replace these axioms by theorems derived from the set-theoretic construction
 * of `ℕ` (as the least inductive set / von Neumann naturals).
 */
object Nat extends lisa.Main {
  private val m = variable[Ind]
  private val n = variable[Ind]
  private val k = variable[Ind]
  private val A = variable[Ind]
  private val R = variable[Ind]
  private val X = variable[Ind]

  ///////////////////////////////
  // Set-theoretic construction //
  ///////////////////////////////

  private val i = variable[Ind]

  /** A chosen inductive set (witness of Infinity). */
  private val I: Expr[Ind] = ε(i, inductive(i))

  /** The witness `I` is inductive. */
  private val IInductive = Theorem(inductive(I)) {
    val epsInd = have(∃(i, inductive(i)) |- inductive(ε(i, inductive(i)))) by Restate.from(
      Quantifiers.existsEpsilon of (x := i, P := λ(i, inductive(i)))
    )
    have(thesis) by Cut(lisa.maths.SetTheory.SetTheory.inductiveSetExists, epsInd)
  }

  /** The set of natural numbers (von Neumann naturals): the elements of `I` that belong to every inductive set. */
  val ℕ = DEF({ n ∈ I | ∀(i, inductive(i) ==> (n ∈ i)) })

  /** Zero (von Neumann encoding). */
  val zero = DEF(∅)

  /** Successor (set-theoretic successor), as a Lisa definition. */
  val Succ = DEF(λ(x, successor(x)))

  /** Membership characterization of successor: `u ∈ Succ(v) <=> u ∈ v ∨ u = v`. */
  val succMembership = Theorem(
    (k ∈ Succ(n)) <=> (k ∈ n) \/ (k === n)
  ) {
    val succDef = have(Succ(n) === successor(n)) by Restate.from(Succ.definition of (x := n))
    val memSucc = have(k ∈ Succ(n) <=> (k ∈ n) \/ (k === n)) by Tautology.from(
      have(k ∈ Succ(n) <=> k ∈ successor(n)) by Congruence.from(succDef),
      have(k ∈ successor(n) <=> (k ∈ n) \/ (k === n)) by Tautology.from(
        have(k ∈ successor(n) <=> k ∈ (n ∪ Singleton.singleton(n))) by Congruence.from(successor.definition of (x := n)),
        have(k ∈ (n ∪ Singleton.singleton(n)) <=> (k ∈ n) \/ (k ∈ Singleton.singleton(n))) by Tautology.from(
          Union.membership of (x := n, y := Singleton.singleton(n), z := k)
        ),
        have(k ∈ Singleton.singleton(n) <=> (k === n)) by Tautology.from(Singleton.membership of (x := n, y := k))
      )
    )
    have(thesis) by Restate.from(memSucc)
  }

  /** Theorem: `n ∈ Succ(n)`. */
  val nInSucc = Theorem(n ∈ Succ(n)) {
    val mem = have(n ∈ Succ(n) <=> (n ∈ n) \/ (n === n)) by Restate.from(succMembership of (k := n, n := n))
    val refl = have(n === n) by Restate
    have(thesis) by Tautology.from(mem, refl)
  }

  /** Theorem: successor is injective, i.e. `Succ(m) = Succ(n) <=> m = n`. */
  val succInjective = Theorem(
    (Succ(m) === Succ(n)) <=> (m === n)
  ) {
    val `==>` = have(Succ(m) === Succ(n) |- m === n) subproof {
      assume(Succ(m) === Succ(n))

      val mInSn = have(m ∈ Succ(n)) by Congruence.from(nInSucc of (n := m))
      val mCase = have(m ∈ n \/ (m === n)) by Tautology.from(
        succMembership of (k := m, n := n),
        mInSn
      )
      val nInSm = have(n ∈ Succ(m)) by Congruence.from(nInSucc of (n := n))
      val nCase = have(n ∈ m \/ (n === m)) by Tautology.from(
        succMembership of (k := n, n := m),
        nInSm
      )

      // Flip the equality disjunct in `nCase` to `m === n`.
      val eqSymm = have(n === m |- m === n) by Congruence

      val asym = have(Succ(m) === Succ(n) |- ¬((m ∈ n) /\ (n ∈ m))) by Weakening(
        FoundationAxiom.membershipAsymmetric of (x := m, y := n)
      )

      have(Succ(m) === Succ(n) |- m === n) by Tableau.from(mCase, nCase, eqSymm, asym)
    }

    val `<==` = have(m === n |- Succ(m) === Succ(n)) by Congruence

    have(thesis) by Tautology.from(`==>`, `<==`)
  }

  /** Numeral `1` as `Succ(0)`. */
  val one: Expr[Ind] = Succ(zero)

  /** Numeral `2` as `Succ(1)`. */
  val two: Expr[Ind] = Succ(one)

  private val memRel = MembershipRelation.membershipRelation(ℕ)

  /** Addition (defined by well-ordered recursion on `(ℕ, ∈_ℕ)`; recursion on the second argument). */
  val add = DEF(
    λ(m,
      λ(n,
        app(
          Necessary.recursiveFunctionOn(
            λ(x,
              λ(h,
                ε(y,
                  ((x === zero) /\ (y === m)) \/
                    ∃(k, (k ∈ ℕ) /\ (x === Succ(k)) /\ (y === Succ(app(h)(k))))
                )
              )
            )
          )(ℕ)(memRel)
        )(n)
      )
    )
  ).printInfix("+")

  /** Multiplication (defined by well-ordered recursion on `(ℕ, ∈_ℕ)`; recursion on the second argument). */
  val mul = DEF(
    λ(m,
      λ(n,
        app(
          Necessary.recursiveFunctionOn(
            λ(x,
              λ(h,
                ε(y,
                  ((x === zero) /\ (y === zero)) \/
                    ∃(k, (k ∈ ℕ) /\ (x === Succ(k)) /\ (y === add(app(h)(k))(m)))
                )
              )
            )
          )(ℕ)(memRel)
        )(n)
      )
    )
  ).printInfix("*")

  // Basic notations.
  extension (a: Expr[Ind])
    infix def +(b: Expr[Ind]): Expr[Ind] = add(a)(b)
    infix def *(b: Expr[Ind]): Expr[Ind] = mul(a)(b)

  ////////////////////////////////
  // Recursion-defined candidates //
  ////////////////////////////////

  /** Alias: recursion-defined addition candidate. */
  val addRec = add

  /** Alias: recursion-defined multiplication candidate. */
  val mulRec = mul

  ///////////////
  // Axioms/API //
  ///////////////

  /** Theorem: `0 ∈ ℕ` (from the set-theoretic definition). */
  val zeroInℕ = Theorem(zero ∈ ℕ) {
    val zeroDef = have(zero === ∅) by Restate.from(zero.definition)
    val NDef = have(ℕ === { k ∈ I | ∀(i, inductive(i) ==> (k ∈ i)) }) by Restate.from(ℕ.definition)
    val memN0 = have(zero ∈ ℕ <=> zero ∈ { k ∈ I | ∀(i, inductive(i) ==> (k ∈ i)) }) by Congruence.from(NDef)
    val memComp0 = have(zero ∈ { k ∈ I | ∀(i, inductive(i) ==> (k ∈ i)) } <=> (zero ∈ I /\ ∀(i, inductive(i) ==> (zero ∈ i)))) by Comprehension.apply
    val memℕ0 = have(zero ∈ ℕ <=> (zero ∈ I /\ ∀(i, inductive(i) ==> (zero ∈ i)))) by Tautology.from(memN0, memComp0)

    val indIffEmpty = have(inductive(I) <=> ((∅ ∈ I) /\ ∀(n, (n ∈ I) ==> (successor(n) ∈ I)))) by Restate.from(inductive.definition of (x := I))
    val iff0I = have((zero ∈ I) <=> (∅ ∈ I)) by Congruence.from(zeroDef)
    val emptyInI = have(∅ ∈ I) by Tautology.from(IInductive, indIffEmpty)
    val zeroInI = have(zero ∈ I) by Tautology.from(emptyInI, iff0I)

    val indiIff = have(inductive(i) <=> ((∅ ∈ i) /\ ∀(n, (n ∈ i) ==> (successor(n) ∈ i)))) by Restate.from(inductive.definition of (x := i))
    val indImpEmpty = have(inductive(i) ==> (∅ ∈ i)) by Tautology.from(indiIff)
    val iff0 = have((zero ∈ i) <=> (∅ ∈ i)) by Congruence.from(zeroDef)
    have(inductive(i) ==> (zero ∈ i)) by Tautology.from(indImpEmpty, iff0)
    val all0 = thenHave(∀(i, inductive(i) ==> (zero ∈ i))) by RightForall

    val rhs = have(zero ∈ I /\ ∀(i, inductive(i) ==> (zero ∈ i))) by Tautology.from(zeroInI, all0)
    have(thesis) by Tautology.from(memℕ0, rhs)
  }

  /** Lemma: unfold membership in `ℕ` to its set-theoretic definition. */
  val memℕ = Lemma(n ∈ ℕ <=> (n ∈ I /\ ∀(i, inductive(i) ==> (n ∈ i)))) {
    val NDef = have(ℕ === { k ∈ I | ∀(i, inductive(i) ==> (k ∈ i)) }) by Restate.from(ℕ.definition)
    val memN = have(n ∈ ℕ <=> n ∈ { k ∈ I | ∀(i, inductive(i) ==> (k ∈ i)) }) by Congruence.from(NDef)
    val memComp = have(n ∈ { k ∈ I | ∀(i, inductive(i) ==> (k ∈ i)) } <=> (n ∈ I /\ ∀(i, inductive(i) ==> (n ∈ i)))) by Comprehension.apply
    have(thesis) by Tautology.from(memN, memComp)
  }

  /** Lemma: `n ∈ ℕ` implies `n` is in every inductive set. */
  val inAllInductive = Lemma(n ∈ ℕ |- ∀(i, inductive(i) ==> (n ∈ i))) {
    have(thesis) by Tautology.from(memℕ)
  }

  /** Theorem: `ℕ` is inductive. */
  val ℕInductive = Theorem(inductive(ℕ)) {
    val zeroDef = have(zero === ∅) by Restate.from(zero.definition)
    val indDef = have(inductive(ℕ) <=> ((∅ ∈ ℕ) /\ ∀(n, (n ∈ ℕ) ==> (successor(n) ∈ ℕ)))) by Restate.from(inductive.definition of (x := ℕ))

    val memN = have(n ∈ ℕ <=> (n ∈ I /\ ∀(i, inductive(i) ==> (n ∈ i)))) by Restate.from(memℕ)
    val memSN = have(successor(n) ∈ ℕ <=> (successor(n) ∈ I /\ ∀(i, inductive(i) ==> (successor(n) ∈ i)))) by Restate.from(memℕ of (n := successor(n)))

    val indIff = have(inductive(I) <=> ((∅ ∈ I) /\ ∀(k, (k ∈ I) ==> (successor(k) ∈ I)))) by Restate.from(inductive.definition of (x := I))
    have(∀(k, (k ∈ I) ==> (successor(k) ∈ I))) by Tautology.from(indIff, IInductive)
    val succInIFromInI = thenHave((n ∈ I) ==> (successor(n) ∈ I)) by InstantiateForall(n)

    val succInI = have(n ∈ ℕ |- successor(n) ∈ I) by Tautology.from(memN, succInIFromInI)

    have(n ∈ ℕ |- ∀(i, inductive(i) ==> (n ∈ i))) by Tautology.from(memN)
    val nInInd = thenHave(n ∈ ℕ |- (inductive(i) ==> (n ∈ i))) by InstantiateForall(i)

    val indiIff = have(inductive(i) <=> ((∅ ∈ i) /\ ∀(k, (k ∈ i) ==> (successor(k) ∈ i)))) by Restate.from(inductive.definition of (x := i))
    have(inductive(i) ==> ∀(k, (k ∈ i) ==> (successor(k) ∈ i))) by Tautology.from(indiIff)
    thenHave(inductive(i) |- ∀(k, (k ∈ i) ==> (successor(k) ∈ i))) by Tautology
    val stepInInd = thenHave(inductive(i) |- (n ∈ i) ==> (successor(n) ∈ i)) by InstantiateForall(n)

    have(n ∈ ℕ |- inductive(i) ==> (successor(n) ∈ i)) by Tautology.from(nInInd, stepInInd)
    val allSuccInInd = thenHave(n ∈ ℕ |- ∀(i, inductive(i) ==> (successor(n) ∈ i))) by RightForall

    val rhs = have(n ∈ ℕ |- successor(n) ∈ I /\ ∀(i, inductive(i) ==> (successor(n) ∈ i))) by Tautology.from(succInI, allSuccInInd)
    have(n ∈ ℕ |- successor(n) ∈ ℕ) by Tautology.from(memSN, rhs)
    thenHave((n ∈ ℕ) ==> (successor(n) ∈ ℕ)) by Tautology
    val succAll = thenHave(∀(n, (n ∈ ℕ) ==> (successor(n) ∈ ℕ))) by RightForall

    val iff0 = have((zero ∈ ℕ) <=> (∅ ∈ ℕ)) by Congruence.from(zeroDef)
    val emptyInℕ = have(∅ ∈ ℕ) by Tautology.from(zeroInℕ, iff0)
    val conj = have((∅ ∈ ℕ) /\ ∀(n, (n ∈ ℕ) ==> (successor(n) ∈ ℕ))) by Tautology.from(emptyInℕ, succAll)
    have(thesis) by Tautology.from(indDef, conj)
  }

  /** Theorem: closure of successor on `ℕ` (corollary of `inductive(ℕ)`). */
  val succClosed = Theorem(n ∈ ℕ |- Succ(n) ∈ ℕ) {
    val indDef = have(inductive(ℕ) <=> ((∅ ∈ ℕ) /\ ∀(n, (n ∈ ℕ) ==> (successor(n) ∈ ℕ)))) by Restate.from(inductive.definition of (x := ℕ))
    val succAll = have(∀(n, (n ∈ ℕ) ==> (successor(n) ∈ ℕ))) by Tautology.from(indDef, ℕInductive)

    have((n ∈ ℕ) ==> (successor(n) ∈ ℕ)) by InstantiateForall(n)(succAll)
    val succInℕ = thenHave(n ∈ ℕ |- successor(n) ∈ ℕ) by Tautology

    val defEq = have(Succ(n) === successor(n)) by Restate.from(Succ.definition of (x := n))
    val iff = have(Succ(n) ∈ ℕ <=> successor(n) ∈ ℕ) by Congruence.from(defEq)
    have(thesis) by Tautology.from(succInℕ, iff)
  }

  /** Theorem: `1 ∈ ℕ`. */
  val oneInℕ = Theorem(one ∈ ℕ) {
    have(thesis) by Cut(zeroInℕ, succClosed.of(n := zero))
  }

  /** Theorem: `2 ∈ ℕ`. */
  val twoInℕ = Theorem(two ∈ ℕ) {
    have(thesis) by Cut(oneInℕ, succClosed.of(n := one))
  }

  /**
   * Induction axiom (second-order over predicates).
   *
   * `P(0) ∧ (∀n. n ∈ ℕ → (P(n) → P(S(n)))) → (∀n. n ∈ ℕ → P(n))`
   */
  private val Pred = variable[Ind >>: Prop]
  private val KPred: Expr[Ind] = { n ∈ ℕ | Pred(n) }
  val induction = Theorem(
    (Pred(zero), ∀(n, (n ∈ ℕ) ==> (Pred(n) ==> Pred(Succ(n))))) |-
      ∀(n, (n ∈ ℕ) ==> Pred(n))
  ) {
    val H0 = Pred(zero)
    val Hstep = ∀(n, (n ∈ ℕ) ==> (Pred(n) ==> Pred(Succ(n))))

    val hyp0 = have((H0, Hstep) |- H0) by Tautology
    val hypAllStep = have((H0, Hstep) |- Hstep) by Tautology

    val memK = have(n ∈ KPred <=> (n ∈ ℕ /\ Pred(n))) by Comprehension.apply
    val memℕUnfold = have(n ∈ ℕ <=> (n ∈ I /\ ∀(i, inductive(i) ==> (n ∈ i)))) by Restate.from(Nat.memℕ)

    // Base: 0 ∈ KPred
    val zeroMemℕ = have((H0, Hstep) |- zero ∈ ℕ) by Tautology.from(zeroInℕ)
    val memK0 = have(zero ∈ KPred <=> (zero ∈ ℕ /\ Pred(zero))) by Comprehension.apply
    val zeroConj = have((H0, Hstep) |- zero ∈ ℕ /\ Pred(zero)) by Tautology.from(zeroMemℕ, hyp0)
    val zeroMemK = have((H0, Hstep) |- zero ∈ KPred) by Tautology.from(memK0, zeroConj)

    val zeroDef = have(zero === ∅) by Restate.from(zero.definition)
    val iff0K = have((zero ∈ KPred) <=> (∅ ∈ KPred)) by Congruence.from(zeroDef)
    val emptyMemK = have((H0, Hstep) |- ∅ ∈ KPred) by Tautology.from(zeroMemK, iff0K)

    // Step: n ∈ KPred -> Succ(n) ∈ KPred
    val predStep = have((H0, Hstep) |- (n ∈ ℕ) ==> (Pred(n) ==> Pred(Succ(n)))) by InstantiateForall(n)(hypAllStep)

    val nInℕ = have((H0, Hstep, n ∈ KPred) |- n ∈ ℕ) by Tautology.from(memK)
    val predN = have((H0, Hstep, n ∈ KPred) |- Pred(n)) by Tautology.from(memK)
    val succFact = have(n ∈ ℕ |- Succ(n) ∈ ℕ).by(Restate.from(succClosed))
    val succInℕ = have((H0, Hstep, n ∈ KPred) |- Succ(n) ∈ ℕ).by(Cut(nInℕ, succFact))
    val predSucc = have((H0, Hstep, n ∈ KPred) |- Pred(Succ(n))) by Tautology.from(nInℕ, predN, predStep)

    val memKS = have(Succ(n) ∈ KPred <=> (Succ(n) ∈ ℕ /\ Pred(Succ(n)))) by Comprehension.apply
    val SnConj = have((H0, Hstep, n ∈ KPred) |- Succ(n) ∈ ℕ /\ Pred(Succ(n))) by Tautology.from(succInℕ, predSucc)
    have((H0, Hstep, n ∈ KPred) |- Succ(n) ∈ KPred) by Tautology.from(memKS, SnConj)
    thenHave((H0, Hstep) |- (n ∈ KPred) ==> (Succ(n) ∈ KPred)) by Tautology
    val allStepK = thenHave((H0, Hstep) |- ∀(n, (n ∈ KPred) ==> (Succ(n) ∈ KPred))) by RightForall

    // KPred is inductive
    val indDefK = have(inductive(KPred) <=> ((∅ ∈ KPred) /\ ∀(n, (n ∈ KPred) ==> (successor(n) ∈ KPred)))) by Restate.from(inductive.definition of (x := KPred))

    val defEqK = have(Succ(n) === successor(n)) by Restate.from(Succ.definition of (x := n))
    val iffK = have(Succ(n) ∈ KPred <=> successor(n) ∈ KPred) by Congruence.from(defEqK)

    have((H0, Hstep) |- (n ∈ KPred) ==> (Succ(n) ∈ KPred)) by InstantiateForall(n)(allStepK)
    val stepSucc = have((H0, Hstep) |- (n ∈ KPred) ==> (successor(n) ∈ KPred)) by Tautology.from(iffK, lastStep)
    val allStepKSucc = thenHave((H0, Hstep) |- ∀(n, (n ∈ KPred) ==> (successor(n) ∈ KPred))) by RightForall
    val indK = have((H0, Hstep) |- inductive(KPred)) by Tautology.from(indDefK, emptyMemK, allStepKSucc)

    // From definition of ℕ: n ∈ ℕ -> (inductive(KPred) -> n ∈ KPred)
    have((H0, Hstep, n ∈ ℕ) |- ∀(i, inductive(i) ==> (n ∈ i))) by Tautology.from(memℕUnfold)
    val nInKFromInd = thenHave((H0, Hstep, n ∈ ℕ) |- inductive(KPred) ==> (n ∈ KPred)) by InstantiateForall(KPred)
    val indKInCtx = have((H0, Hstep, n ∈ ℕ) |- inductive(KPred)) by Tautology.from(indK)
    val nInK = have((H0, Hstep, n ∈ ℕ) |- n ∈ KPred) by Tautology.from(nInKFromInd, indKInCtx)

    // Hence Pred(n)
    have((H0, Hstep, n ∈ ℕ) |- Pred(n)) by Tautology.from(memK, nInK)
    thenHave((H0, Hstep) |- (n ∈ ℕ) ==> Pred(n)) by Tautology
    val concl = thenHave((H0, Hstep) |- ∀(n, (n ∈ ℕ) ==> Pred(n))) by RightForall
    have(thesis).by(Restate.from(concl))
  }

  /** Lemma: `n ∈ ℕ` implies `0 ∈ Succ(n)`. */
  val `n ∈ ℕ -> 0 ∈ Succ(n)` = Lemma((n ∈ ℕ) |- (zero ∈ Succ(n))) {
    val P = λ(n, zero ∈ Succ(n))

    val base = have(P(zero)) by Tautology.from(succMembership of (n := zero, k := zero))

    val step = have(∀(n, (n ∈ ℕ) ==> (P(n) ==> P(Succ(n))))) subproof {
      have((n ∈ ℕ) |- (P(n) ==> P(Succ(n)))) subproof {
        assume(n ∈ ℕ)
        assume(P(n))

        val defSn = have(Succ(n) === successor(n)) by Restate.from(Succ.definition of (x := n))
        val defSSn = have(Succ(Succ(n)) === successor(Succ(n))) by Restate.from(Succ.definition of (x := Succ(n)))

        val SnSub = have(Succ(n) ⊆ Succ(Succ(n))) by Congruence.from(
          Union.leftSubset of (x := successor(n), y := Singleton.singleton(successor(n))),
          successor.definition of (x := successor(n)),
          defSn,
          defSSn
        )

        val PSn = have(P(Succ(n))) by Tautology.from(
          Subset.membership of (x := Succ(n), y := Succ(Succ(n)), z := zero),
          SnSub,
          have(zero ∈ Succ(n)) by Restate
        )
        val imp = thenHave(P(n) ==> P(Succ(n))) by Tautology
        have(thesis) by Restate.from(imp)
      }
      thenHave((n ∈ ℕ) ==> (P(n) ==> P(Succ(n)))) by Tautology
      thenHave(thesis) by RightForall
    }

    val all = have(∀(n, (n ∈ ℕ) ==> P(n))).by(Tautology.from(induction of (Pred := P), base, step))

    have((n ∈ ℕ) ==> P(n)) by InstantiateForall(n)(all)
    thenHave(thesis) by Tautology
  }

  /** Theorem (Isabelle/ZF `natE`-style): every natural is either `0` or a successor. */
  val natCases = Theorem(
    (n ∈ ℕ) |- (n === zero) \/ ∃(m, (m ∈ ℕ) /\ (n === Succ(m)))
  ) {
    val P = λ(n, (n === zero) \/ ∃(m, (m ∈ ℕ) /\ (n === Succ(m))))

    val base = have(P(zero)) by Tautology

    val step = have(∀(n, (n ∈ ℕ) ==> (P(n) ==> P(Succ(n))))) subproof {
      have((n ∈ ℕ) ==> (P(n) ==> P(Succ(n)))) subproof {
        assume(n ∈ ℕ)
        assume(P(n))
        val rhs = have((n ∈ ℕ) /\ (Succ(n) === Succ(n))) by Tautology
        val ex = have(∃(m, (m ∈ ℕ) /\ (Succ(n) === Succ(m)))) by RightExists(rhs)
        thenHave(thesis) by Restate
      }
      thenHave(thesis) by RightForall
    }

    val all = have(∀(n, (n ∈ ℕ) ==> P(n))).by(Tautology.from(induction of (Pred := P), base, step))

    have((n ∈ ℕ) ==> P(n)) by InstantiateForall(n)(all)
    thenHave(thesis) by Tautology
  }
  /** Lemma: if `n ⊆ ℕ` and `n ∈ ℕ`, then `Succ(n) ⊆ ℕ`. */
  private val succSubsetℕ = Lemma((n ⊆ ℕ, n ∈ ℕ) |- Succ(n) ⊆ ℕ) {
    assume(n ⊆ ℕ)
    assume(n ∈ ℕ)

    val memSucc1 = have(k ∈ successor(n) <=> k ∈ (n ∪ Singleton.singleton(n))) by Congruence.from(successor.definition of (x := n))
    val memSucc2 = have(k ∈ (n ∪ Singleton.singleton(n)) <=> (k ∈ n) \/ (k ∈ Singleton.singleton(n))) by Tautology.from(
      Union.membership of (x := n, y := Singleton.singleton(n), z := k)
    )
    val memSucc = have(k ∈ successor(n) <=> (k ∈ n) \/ (k ∈ Singleton.singleton(n))) by Tautology.from(memSucc1, memSucc2)

    val memSing = have(k ∈ Singleton.singleton(n) <=> (k === n)) by Tautology.from(Singleton.membership of (x := n, y := k))

    val inFromSubset = have(k ∈ n ==> k ∈ ℕ) by Tautology.from(Subset.membership of (x := n, y := ℕ, z := k))

    val eqMem = have((k === n, n ∈ ℕ) |- k ∈ ℕ) by Congruence
    val nInℕ = have(n ∈ ℕ) by Restate
    val eqImp = have(n ∈ ℕ |- (k === n ==> k ∈ ℕ)) by Tautology.from(eqMem)
    val inFromEq = have(k === n ==> k ∈ ℕ) by Tautology.from(eqImp, nInℕ)
    val inFromSingleton = have(k ∈ Singleton.singleton(n) ==> k ∈ ℕ) by Tautology.from(memSing, inFromEq)

    have((k ∈ successor(n)) ==> (k ∈ ℕ)) by Tautology.from(memSucc, inFromSubset, inFromSingleton)
    val all = thenHave(∀(k, (k ∈ successor(n)) ==> (k ∈ ℕ))) by RightForall

    val succSub = have(successor(n) ⊆ ℕ) by Tautology.from(Subset.definition of (x := successor(n), y := ℕ), all)
    val defEq = have(Succ(n) === successor(n)) by Restate.from(Succ.definition of (x := n))
    val iff = have(Succ(n) ⊆ ℕ <=> successor(n) ⊆ ℕ) by Congruence.from(defEq)
    have(thesis) by Tautology.from(iff, succSub)
  }

  /** Theorem: `ℕ` is a transitive set (i.e. $x ∈ y ∈ \mathbb{N} ⇒ x ∈ \mathbb{N}$). */
  val ℕTransitive = Theorem(TransitiveSet.transitiveSet(ℕ)) {
    val P = λ(n, n ⊆ ℕ)
    val zeroDef = have(zero === ∅) by Restate.from(zero.definition)
    val iff0 = have(P(zero) <=> P(∅)) by Congruence.from(zeroDef)
    val baseEmpty = have(P(∅)) by Restate.from(Subset.leftEmpty of (x := ℕ))
    val base = have(P(zero)) by Tautology.from(iff0, baseEmpty)
    have((n ∈ ℕ) ==> (P(n) ==> P(Succ(n)))) by Tautology.from(succSubsetℕ)
    val step = thenHave(∀(n, (n ∈ ℕ) ==> (P(n) ==> P(Succ(n))))) by RightForall
    val all = have(∀(n, (n ∈ ℕ) ==> P(n))).by(Tautology.from(induction of (Pred := P), base, step))
    have(thesis) by Tautology.from(TransitiveSet.alternativeDefinition of (A := ℕ), all)
  }

  /** Lemma: if `n ∈ ℕ`, then `n ⊆ ℕ`. */
  val `n ∈ ℕ -> n ⊆ ℕ` = Lemma((n ∈ ℕ) |- n ⊆ ℕ) {
    have(thesis) by Tautology.from(TransitiveSet.elementIsSubset.of(A := ℕ, x := n), ℕTransitive)
  }


  /** For von Neumann naturals: if `n ∈ ℕ` then the `∈_ℕ`-initial segment below `n` is exactly `n`. */
  val natInitialSegment = Theorem(
    (n ∈ ℕ) |- InitialSegment.initialSegment(n)(ℕ)(memRel) === n
  ) {
    assume(n ∈ ℕ)

    val nSubℕ = have(n ⊆ ℕ).by(Tautology.from(TransitiveSet.elementIsSubset.of(A := ℕ, x := n), ℕTransitive))

    val memInit = have(k ∈ InitialSegment.initialSegment(n)(ℕ)(memRel) <=> (k ∈ ℕ) /\ ((k, n) ∈ memRel)).by(Tautology.from(
      InitialSegment.membership.of(y := k, x := n, A := ℕ, < := memRel)
    ))

    val memRelMem = have((k, n) ∈ memRel <=> (k ∈ ℕ) /\ (n ∈ ℕ) /\ (k ∈ n)).by(Tautology.from(
      MembershipRelation.membership.of(x := k, y := n, A := ℕ)
    ))

    val initToMem = have(k ∈ InitialSegment.initialSegment(n)(ℕ)(memRel) ==> k ∈ n).by(Tautology.from(memInit, memRelMem))

    val memToInit = have(k ∈ n ==> k ∈ InitialSegment.initialSegment(n)(ℕ)(memRel)).by(Tautology.from(
      memInit,
      memRelMem,
      Subset.membership.of(x := n, y := ℕ, z := k),
      nSubℕ
    ))

    have(k ∈ InitialSegment.initialSegment(n)(ℕ)(memRel) <=> k ∈ n).by(Tautology.from(initToMem, memToInit))
    thenHave(thesis).by(Extensionality)
  }

  /** Theorem: every element of `ℕ` is a transitive set (i.e. $n ∈ \mathbb{N} ⇒ transitiveSet(n)$). */
  val natElementsTransitive = Theorem(
    (n ∈ ℕ) |- TransitiveSet.transitiveSet(n)
  ) {
    val P = λ(n, TransitiveSet.transitiveSet(n))

    val zeroDef = have(zero === ∅) by Restate.from(zero.definition)
    val iff0 = have(P(zero) <=> P(∅)) by Congruence.from(zeroDef)
    val baseEmpty = have(P(∅)) by Restate.from(TransitiveSet.emptySet)
    val base = have(P(zero)) by Tautology.from(iff0, baseEmpty)

    val step = have(∀(n, (n ∈ ℕ) ==> (P(n) ==> P(Succ(n))))) subproof {
      have((n ∈ ℕ) |- (P(n) ==> P(Succ(n)))) subproof {
        assume(n ∈ ℕ)
        val Pn = assume(P(n))

        // transitiveSet(n) gives: ∀k. k ∈ n ==> k ⊆ n
        val nAlt = have(∀(k, k ∈ n ==> k ⊆ n)).by(Tautology.from(
          TransitiveSet.alternativeDefinition of (A := n),
          Pn
        ))

        // n ⊆ S(n)
        val nSubSucc = have(n ⊆ Succ(n)) subproof {
          val defEq = have(Succ(n) === successor(n)) by Restate.from(Succ.definition of (x := n))
          val memSucc0 = have(k ∈ Succ(n) <=> k ∈ successor(n)) by Congruence.from(defEq)
          val memSucc1 = have(k ∈ successor(n) <=> k ∈ (n ∪ Singleton.singleton(n))) by Congruence.from(successor.definition of (x := n))
          val memSucc = have(k ∈ Succ(n) <=> k ∈ (n ∪ Singleton.singleton(n))) by Tautology.from(memSucc0, memSucc1)
          val memUnion = have(k ∈ (n ∪ Singleton.singleton(n)) <=> (k ∈ n) \/ (k ∈ Singleton.singleton(n))) by Tautology.from(
            Union.membership of (x := n, y := Singleton.singleton(n), z := k)
          )

          val disj = have(k ∈ n |- (k ∈ n) \/ (k ∈ Singleton.singleton(n))) by Tautology
          val memU = have(k ∈ n |- k ∈ (n ∪ Singleton.singleton(n))) by Tautology.from(memUnion, disj)
          val memS = have(k ∈ n |- k ∈ Succ(n)) by Tautology.from(memSucc, memU)
          thenHave(k ∈ n ==> k ∈ Succ(n)) by Tautology
          val all = thenHave(∀(k, k ∈ n ==> k ∈ Succ(n))) by RightForall
          have(thesis) by Tautology.from(Subset.definition of (x := n, y := Succ(n)), all)
        }

        // Show: ∀k. k ∈ S(n) ==> k ⊆ S(n)
        have(k ∈ Succ(n) ==> k ⊆ Succ(n)) subproof {
          assume(k ∈ Succ(n))

          val defEq = have(Succ(n) === successor(n)) by Restate.from(Succ.definition of (x := n))
          val memSucc0 = have(k ∈ Succ(n) <=> k ∈ successor(n)) by Congruence.from(defEq)
          val memSucc1 = have(k ∈ successor(n) <=> k ∈ (n ∪ Singleton.singleton(n))) by Congruence.from(successor.definition of (x := n))
          val mem1 = have(k ∈ Succ(n) <=> k ∈ (n ∪ Singleton.singleton(n))) by Tautology.from(memSucc0, memSucc1)
          val mem2 = have(k ∈ (n ∪ Singleton.singleton(n)) <=> (k ∈ n) \/ (k ∈ Singleton.singleton(n))) by Tautology.from(
            Union.membership of (x := n, y := Singleton.singleton(n), z := k)
          )
          val memSucc = have(k ∈ Succ(n) <=> (k ∈ n) \/ (k ∈ Singleton.singleton(n))) by Tautology.from(mem1, mem2)

          val caseIn = have(k ∈ n ==> k ⊆ Succ(n)) subproof {
            val kInN = assume(k ∈ n)
            val kSubNImp = have(k ∈ n ==> k ⊆ n) by InstantiateForall(k)(nAlt)
            val kSubN = have(k ⊆ n) by Tautology.from(kSubNImp, kInN)
            have(k ⊆ Succ(n)) by Tautology.from(kSubN, nSubSucc, Subset.transitivity of (x := k, y := n, z := Succ(n)))
            thenHave(thesis) by Tautology
          }

          val memSing = have(k ∈ Singleton.singleton(n) <=> (k === n)) by Tautology.from(Singleton.membership of (x := n, y := k))

          val caseEq = have(k ∈ Singleton.singleton(n) ==> k ⊆ Succ(n)) subproof {
            val kInSing = assume(k ∈ Singleton.singleton(n))
            val kEqN = have(k === n) by Tautology.from(memSing, kInSing)
            val eqSub = have((k === n, n ⊆ Succ(n)) |- k ⊆ Succ(n)) by Congruence
            have(k ⊆ Succ(n)) by Tautology.from(kEqN, nSubSucc, eqSub)
            thenHave(thesis) by Tautology
          }

          have(thesis) by Tautology.from(memSucc, caseIn, caseEq)
        }
        val SnAlt = thenHave(∀(k, k ∈ Succ(n) ==> k ⊆ Succ(n))) by RightForall

        val PSn = have(P(Succ(n))) by Tautology.from(TransitiveSet.alternativeDefinition of (A := Succ(n)), SnAlt)
        have(thesis) by Tautology.from(PSn)
      }
      thenHave((n ∈ ℕ) ==> (P(n) ==> P(Succ(n)))) by Tautology
      thenHave(thesis) by RightForall
    }

    val premise = have(P(zero) /\ ∀(n, (n ∈ ℕ) ==> (P(n) ==> P(Succ(n))))).by(Tautology.from(base, step))
    val all = have(∀(n, (n ∈ ℕ) ==> P(n))).by(Tautology.from(induction of (Pred := P), premise))

    have((n ∈ ℕ) ==> P(n)).by(InstantiateForall(n)(all))
    thenHave(thesis) by Restate
  }

  /** Theorem: the membership relation restricted to `ℕ` is well-founded on `ℕ`. */
  val natMembershipWellFounded = Theorem(
    wellFounded(MembershipRelation.membershipRelation(ℕ))(ℕ)
  ) {
    val memRel = MembershipRelation.membershipRelation(ℕ)

    val rhsWF = have(∀(A, (A ⊆ ℕ) /\ (A ≠ ∅) ==> ∃(m, Extrema.minimal(m)(A)(memRel)))) subproof {
      have((A ⊆ ℕ) |- ((A ≠ ∅) ==> ∃(m, Extrema.minimal(m)(A)(memRel)))) subproof {
        val ASubNat = assume(A ⊆ ℕ)

        have(A ≠ ∅ |- ∃(m, Extrema.minimal(m)(A)(memRel))) subproof {
          val ANonEmpty = assume(A ≠ ∅)

          val foundationInstance = have(∃(m, (m ∈ A) /\ ∀(k, k ∈ A ==> k ∉ m))) by Tautology.from(
            axiomOfFoundation of (x := A),
            ANonEmpty
          )

          have((m ∈ A) /\ ∀(k, k ∈ A ==> k ∉ m) |- Extrema.minimal(m)(A)(memRel)) subproof {
            assume((m ∈ A) /\ ∀(k, k ∈ A ==> k ∉ m))

            val mInA = have(m ∈ A) by Tautology
            val allNotIn = have(∀(k, k ∈ A ==> k ∉ m)) by Tautology
            val mInℕ = have(m ∈ ℕ) by Tautology.from(mInA, Subset.membership of (x := A, y := ℕ, z := m), ASubNat)

            have(k ∈ A |- ¬((k, m) ∈ memRel)) subproof {
              val kInA = assume(k ∈ A)

              val kNotInMImp = have(k ∈ A ==> k ∉ m) by InstantiateForall(k)(allNotIn)

              val relImpliesMem = have((k, m) ∈ memRel |- k ∈ m) by Tautology.from(MembershipRelation.membership of (x := k, y := m, A := ℕ))

              have((k, m) ∈ memRel |- ()) by Tautology.from(kNotInMImp, relImpliesMem)
              thenHave(thesis) by RightNot
            }
            thenHave(k ∈ A ==> ¬((k, m) ∈ memRel)) by Tautology
            val allNoRel = thenHave(∀(k, k ∈ A ==> ¬((k, m) ∈ memRel))) by RightForall

            val rhs = have(m ∈ A /\ ∀(k, k ∈ A ==> ¬((k, m) ∈ memRel))) by Tautology.from(mInA, allNoRel)
              have(thesis) by Tautology.from(Extrema.minimal.definition of (A := A, a := m, < := memRel), rhs)
          }

          thenHave((m ∈ A) /\ ∀(k, k ∈ A ==> k ∉ m) |- ∃(m, Extrema.minimal(m)(A)(memRel))) by RightExists
          val exToMin = thenHave(∃(m, (m ∈ A) /\ ∀(k, k ∈ A ==> k ∉ m)) |- ∃(m, Extrema.minimal(m)(A)(memRel))) by LeftExists
          have(thesis) by Cut(foundationInstance, exToMin)
        }

        thenHave(thesis) by Tautology
      }

      thenHave((A ⊆ ℕ) /\ (A ≠ ∅) ==> ∃(m, Extrema.minimal(m)(A)(memRel))) by Tautology
      thenHave(thesis) by RightForall
    }

    val wfDef = have(wellFounded(memRel)(ℕ) <=> ∀(A, (A ⊆ ℕ) /\ (A ≠ ∅) ==> ∃(m, Extrema.minimal(m)(A)(memRel)))) by Restate.from(
      wellFounded.definition of (R := memRel, X := ℕ)
    )
    have(thesis) by Tautology.from(wfDef, rhsWF)
  }

  //////////////////////
  // Well-order on ℕ  //
  //////////////////////

  /** Lemma: successor is never empty, hence `Succ(n) ≠ 0` (Isabelle/HOL `Nat.thy`: `Suc_not_Zero`). */
  val succNeZero = Lemma((n ∈ ℕ) |- (Succ(n) =/= zero)) {
    assume(n ∈ ℕ)
    val nInSn = have(n ∈ Succ(n)).by(Weakening(nInSucc))
    have(Succ(n) === zero |- ()) subproof {
      val SnEq0 = assume(Succ(n) === zero)
      val nIn0 = have(n ∈ zero) by Congruence.from(nInSn, SnEq0)
      val zeroDef = have(zero === ∅) by Restate.from(zero.definition)
      val iff0 = have(n ∈ zero <=> n ∈ ∅) by Congruence.from(zeroDef)
      val nInEmpty = have(n ∈ ∅) by Tautology.from(iff0, nIn0)
      have(thesis) by Tautology.from(EmptySet.definition.of(x := n), nInEmpty)
    }
    thenHave(thesis) by Restate
  }

  /** Zero is not a successor (Isabelle/HOL `Nat.thy`: `Zero_not_Suc`). */
  val zeroNeSucc = Theorem((n ∈ ℕ) |- (zero =/= Succ(n))) {
    val nInℕ = assume(n ∈ ℕ)

    have((n ∈ ℕ, zero === Succ(n)) |- ()) subproof {
      val zEqSn = assume(zero === Succ(n))
      val SnEq0 = have(Succ(n) === zero).by(Congruence.from(zEqSn))
      val SnNe0 = have(Succ(n) =/= zero).by(Tautology.from(nInℕ, succNeZero.of(n := n)))
      val notSnEq0 = have(¬(Succ(n) === zero)).by(Tautology.from(SnNe0))
      have(thesis).by(Tautology.from(SnEq0, notSnEq0))
    }
    thenHave(thesis) by Restate
  }

  /** Successor is never equal to itself (Isabelle/HOL `Nat.thy`: `Suc_n_not_n`). */
  val succNeSelf = Theorem((n ∈ ℕ) |- (Succ(n) =/= n)) {
    val nInℕ = assume(n ∈ ℕ)

    have((n ∈ ℕ, Succ(n) === n) |- ()) subproof {
      val SnEqn = assume(Succ(n) === n)
      val nInSn = have(n ∈ Succ(n)).by(Weakening(nInSucc.of(n := n)))
      val nInn = have(n ∈ n).by(Congruence.from(nInSn, SnEqn))
      val nNotInn = have(n ∉ n).by(Weakening(FoundationAxiom.selfNonInclusion.of(x := n)))
      have(thesis).by(Tautology.from(nInn, nNotInn))
    }
    thenHave(thesis) by Restate
  }

  /** No natural is equal to its successor (Isabelle/HOL `Nat.thy`: `n_not_Suc_n`). */
  val selfNeSucc = Theorem((n ∈ ℕ) |- (n =/= Succ(n))) {
    val nInℕ = assume(n ∈ ℕ)

    have((n ∈ ℕ, n === Succ(n)) |- ()) subproof {
      val nEqSn = assume(n === Succ(n))
      val SnEqn = have(Succ(n) === n).by(Congruence.from(nEqSn))
      val SnNen = have(Succ(n) =/= n).by(Tautology.from(succNeSelf.of(n := n)))
      val notSnEqn = have(¬(Succ(n) === n)).by(Tautology.from(SnNen))
      have(thesis).by(Tautology.from(SnEqn, notSnEqn))
    }
    thenHave(thesis) by Restate
  }

  /**
   * Lemma (successor step): if `k ∈ n` and `n ∈ ℕ` then `S(k) ∈ n` or `S(k) = n`.
   * This is the key inductive property used to show linearity of `∈` on naturals.
   */
  private val succStepInNat = Theorem(
    (k ∈ n, n ∈ ℕ) |- (Succ(k) ∈ n) \/ (Succ(k) === n)
  ) {
    // Prove by induction on n the predicate: ∀k. k ∈ n ==> (S(k) ∈ n) \/ (S(k) = n)
    val P = λ(n, ∀(k, k ∈ n ==> ((Succ(k) ∈ n) \/ (Succ(k) === n))))

    val base = have(P(zero)) subproof {
      have(k ∈ zero |- (Succ(k) ∈ zero) \/ (Succ(k) === zero)) subproof {
        val kIn0 = assume(k ∈ zero)
        val zeroDef = have(zero === ∅) by Restate.from(zero.definition)
        val iff0 = have(k ∈ zero <=> k ∈ ∅) by Congruence.from(zeroDef)
        val kInEmpty = have(k ∈ ∅) by Tautology.from(iff0, kIn0)
        have(thesis) by Tautology.from(EmptySet.definition.of(x := k), kInEmpty)
      }
      thenHave(k ∈ zero ==> ((Succ(k) ∈ zero) \/ (Succ(k) === zero))) by Restate
      thenHave(∀(k, k ∈ zero ==> ((Succ(k) ∈ zero) \/ (Succ(k) === zero)))) by RightForall
      thenHave(thesis) by Restate
    }

    val step = have(∀(n, (n ∈ ℕ) ==> (P(n) ==> P(Succ(n))))) subproof {
      have((n ∈ ℕ) |- (P(n) ==> P(Succ(n)))) subproof {
        val nInℕ = assume(n ∈ ℕ)
        val Pn = assume(P(n))

        have(∀(k, k ∈ Succ(n) ==> ((Succ(k) ∈ Succ(n)) \/ (Succ(k) === Succ(n))))) subproof {
          have(k ∈ Succ(n) |- (Succ(k) ∈ Succ(n)) \/ (Succ(k) === Succ(n))) subproof {
            val kInSn = assume(k ∈ Succ(n))

            val kCases = have((k ∈ n) \/ (k === n)) by Tautology.from(succMembership.of(n := n, k := k), kInSn)

            val SkEqSn = have(k === n |- Succ(k) === Succ(n)) by Congruence
            val caseEq = have(k === n |- (Succ(k) ∈ Succ(n)) \/ (Succ(k) === Succ(n))) by Tautology.from(SkEqSn)

            val caseIn = have(k ∈ n |- (Succ(k) ∈ Succ(n)) \/ (Succ(k) === Succ(n))) subproof {
              val kInN = assume(k ∈ n)

              have(∀(k, k ∈ n ==> ((Succ(k) ∈ n) \/ (Succ(k) === n)))) by Restate.from(Pn)
              val impSk = thenHave(k ∈ n ==> ((Succ(k) ∈ n) \/ (Succ(k) === n))) by InstantiateForall(k)
              val SkInNorEq = have((Succ(k) ∈ n) \/ (Succ(k) === n)) by Tautology.from(impSk)

              val fromIn = have(Succ(k) ∈ n |- (Succ(k) ∈ Succ(n)) \/ (Succ(k) === Succ(n))) subproof {
                assume(Succ(k) ∈ n)
                have(thesis).by(Tautology.from(succMembership.of(n := n, k := Succ(k))))
              }

              val nInSn = have(Succ(k) === n |- n ∈ Succ(n)).by(Weakening(nInSucc))
              val SkInSn = have(Succ(k) === n |- Succ(k) ∈ Succ(n)).by(Congruence.from(nInSn))
              val fromEq = have(Succ(k) === n |- (Succ(k) ∈ Succ(n)) \/ (Succ(k) === Succ(n))) by Tautology.from(SkInSn)

              val C = (Succ(k) ∈ Succ(n)) \/ (Succ(k) === Succ(n))

              have(thesis).by(Tautology.from(SkInNorEq, fromIn, fromEq))
            }

            val C2 = (Succ(k) ∈ Succ(n)) \/ (Succ(k) === Succ(n))

            have(thesis).by(Tautology.from(kCases, caseIn, caseEq))
          }
          thenHave(k ∈ Succ(n) ==> ((Succ(k) ∈ Succ(n)) \/ (Succ(k) === Succ(n)))) by Restate
          thenHave(∀(k, k ∈ Succ(n) ==> ((Succ(k) ∈ Succ(n)) \/ (Succ(k) === Succ(n))))) by RightForall
          thenHave(thesis) by Restate
        }

        thenHave(P(Succ(n))) by Restate
        val imp = thenHave(P(n) ==> P(Succ(n))) by Tautology
        have(thesis) by Restate.from(imp)
      }
      thenHave((n ∈ ℕ) ==> (P(n) ==> P(Succ(n)))) by Tautology
      thenHave(thesis) by RightForall
    }

    val premise = have(P(zero) /\ ∀(n, (n ∈ ℕ) ==> (P(n) ==> P(Succ(n))))) by Tautology.from(base, step)
    val all = have(∀(n, (n ∈ ℕ) ==> P(n))) by Tautology.from(induction.of(Pred := P), premise)

    // Use the proved ∀n∈ℕ. P(n) at our specific n.
    val nInℕ = assume(n ∈ ℕ)
    val impN = have((n ∈ ℕ) ==> P(n)) by InstantiateForall(n)(all)
    val Pn = have(P(n)) by Tautology.from(impN, nInℕ)

    // Now instantiate P(n) at k and apply k ∈ n.
    have(∀(k, k ∈ n ==> ((Succ(k) ∈ n) \/ (Succ(k) === n)))) by Restate.from(Pn)
    val imp = thenHave(k ∈ n ==> ((Succ(k) ∈ n) \/ (Succ(k) === n))) by InstantiateForall(k)
    assume(k ∈ n)
    have(thesis) by Tautology.from(imp)
  }

  /** Lemma: if `k ∈ n` and `n ∈ ℕ`, then `Succ(k) ∈ Succ(n)`. */
  private val succMemMonotone = Lemma((k ∈ n, n ∈ ℕ) |- Succ(k) ∈ Succ(n)) {
    assume(k ∈ n)
    assume(n ∈ ℕ)
    val fromIn = have(Succ(k) ∈ n |- Succ(k) ∈ Succ(n)) by Tautology.from(succMembership.of(n := n, k := Succ(k)))
    val nInSn = have(n ∈ Succ(n)).by(Weakening(nInSucc))
    val fromEq = have(Succ(k) === n |- Succ(k) ∈ Succ(n)).by(Congruence.from(nInSn))

    val disj = have((Succ(k) ∈ n) \/ (Succ(k) === n)) by Tautology.from(succStepInNat)
    have(thesis) by Tautology.from(disj, fromIn, fromEq)
  }

  /** Theorem: any two naturals are comparable by membership (trichotomy on `∈`). */
  private val natComparability = Theorem(
    (m ∈ ℕ, n ∈ ℕ) |- (m === n) \/ (m ∈ n) \/ (n ∈ m)
  ) {
    // Induction on n with predicate: ∀m∈ℕ, m = n \/ m ∈ n \/ n ∈ m
    val Q = λ(n, ∀(m, (m ∈ ℕ) ==> ((m === n) \/ (m ∈ n) \/ (n ∈ m))))

    val base = have(Q(zero)) subproof {
      have((m ∈ ℕ) |- (m === zero) \/ (m ∈ zero) \/ (zero ∈ m)) subproof {
        val mInℕ = assume(m ∈ ℕ)
        val mCases = have((m === zero) \/ ∃(k, (k ∈ ℕ) /\ (m === Succ(k)))) by Tautology.from(natCases.of(n := m), mInℕ)

        val caseZero = have(m === zero |- (m === zero) \/ (m ∈ zero) \/ (zero ∈ m)) by Tautology

        val caseSucc = have(∃(k, (k ∈ ℕ) /\ (m === Succ(k))) |- (m === zero) \/ (m ∈ zero) \/ (zero ∈ m)) subproof {
          assume(∃(k, (k ∈ ℕ) /\ (m === Succ(k))))
          have((k ∈ ℕ) /\ (m === Succ(k)) |- (m === zero) \/ (m ∈ zero) \/ (zero ∈ m)) subproof {
            assume((k ∈ ℕ) /\ (m === Succ(k)))
            val kInℕ = have(k ∈ ℕ) by Tautology
            val mEqSk = have(m === Succ(k)) by Tautology

            val zeroInSk = have(zero ∈ Succ(k)) by Tautology.from(`n ∈ ℕ -> 0 ∈ Succ(n)`.of(n := k), kInℕ)
            val zeroInM = have(zero ∈ m) by Congruence.from(zeroInSk, mEqSk)
            have(thesis) by Tautology.from(zeroInM)
          }
          thenHave(∃(k, (k ∈ ℕ) /\ (m === Succ(k))) |- (m === zero) \/ (m ∈ zero) \/ (zero ∈ m)) by LeftExists
        }

        val goal = (m === zero) \/ (m ∈ zero) \/ (zero ∈ m)

        have(thesis) by Tautology.from(mCases, caseZero, caseSucc)
      }
      thenHave((m ∈ ℕ) ==> ((m === zero) \/ (m ∈ zero) \/ (zero ∈ m))) by Restate
      val allM = thenHave(∀(m, (m ∈ ℕ) ==> ((m === zero) \/ (m ∈ zero) \/ (zero ∈ m)))) by RightForall
      have(thesis) by Restate.from(allM)
    }

    val step = have(∀(n, (n ∈ ℕ) ==> (Q(n) ==> Q(Succ(n))))) subproof {
      have((n ∈ ℕ) |- (Q(n) ==> Q(Succ(n)))) subproof {
        val nInℕ = assume(n ∈ ℕ)
        val Qn = assume(Q(n))

        have((m ∈ ℕ) |- (m === Succ(n)) \/ (m ∈ Succ(n)) \/ (Succ(n) ∈ m)) subproof {
          val mInℕ = assume(m ∈ ℕ)

          val mCases = have((m === zero) \/ ∃(k, (k ∈ ℕ) /\ (m === Succ(k)))) by Tautology.from(natCases.of(n := m), mInℕ)

          val caseZero = have(m === zero |- (m === Succ(n)) \/ (m ∈ Succ(n)) \/ (Succ(n) ∈ m)) subproof {
            assume(m === zero)
            // 0 ∈ Succ(n)
            val zeroInSn = have(zero ∈ Succ(n)) by Tautology.from(`n ∈ ℕ -> 0 ∈ Succ(n)`.of(n := n), nInℕ)
            have(m ∈ Succ(n)) by Congruence.from(zeroInSn, lastStep)
            have(thesis) by Tautology.from(lastStep)
          }

          val caseSucc = have(∃(k, (k ∈ ℕ) /\ (m === Succ(k))) |- (m === Succ(n)) \/ (m ∈ Succ(n)) \/ (Succ(n) ∈ m)) subproof {
            assume(∃(k, (k ∈ ℕ) /\ (m === Succ(k))))

            have((k ∈ ℕ) /\ (m === Succ(k)) |- (m === Succ(n)) \/ (m ∈ Succ(n)) \/ (Succ(n) ∈ m)) subproof {
              assume((k ∈ ℕ) /\ (m === Succ(k)))
              val kInℕ = have(k ∈ ℕ) by Tautology
              val mEqSk = have(m === Succ(k)) by Tautology

              // Compare k and n using Q(n)
              have(∀(m, (m ∈ ℕ) ==> ((m === n) \/ (m ∈ n) \/ (n ∈ m)))) by Restate.from(Qn)
              thenHave((k ∈ ℕ) ==> ((k === n) \/ (k ∈ n) \/ (n ∈ k))) by InstantiateForall(k)
              val cmp = have((k === n) \/ (k ∈ n) \/ (n ∈ k)) by Tautology.from(lastStep)

              val eqCase = have(k === n |- (m === Succ(n)) \/ (m ∈ Succ(n)) \/ (Succ(n) ∈ m)) subproof {
                assume(k === n)
                have(Succ(k) === Succ(n)) by Congruence
                have(m === Succ(n)) by Congruence.from(mEqSk, lastStep)
                have(thesis) by Tautology.from(lastStep)
              }

              val ltCase = have(k ∈ n |- (m === Succ(n)) \/ (m ∈ Succ(n)) \/ (Succ(n) ∈ m)) subproof {
                assume(k ∈ n)
                val kInN2 = assume(k ∈ n)
                val SkInSn = have(Succ(k) ∈ Succ(n)) by Tautology.from(succMemMonotone.of(k := k, n := n), kInN2, nInℕ)
                have(m ∈ Succ(n)) by Congruence.from(SkInSn, mEqSk)
                have(thesis) by Tautology.from(lastStep)
              }

              val gtCase = have(n ∈ k |- (m === Succ(n)) \/ (m ∈ Succ(n)) \/ (Succ(n) ∈ m)) subproof {
                assume(n ∈ k)
                val nInK2 = assume(n ∈ k)
                val SnInSk = have(Succ(n) ∈ Succ(k)) by Tautology.from(succMemMonotone.of(k := n, n := k), nInK2, kInℕ)
                have(Succ(n) ∈ m) by Congruence.from(SnInSk, mEqSk)
                have(thesis) by Tautology.from(lastStep)
              }

              val goal = (m === Succ(n)) \/ (m ∈ Succ(n)) \/ (Succ(n) ∈ m)

              val eqSeq = have(k === n |- goal) by Tautology.from(eqCase)
              val ltSeq = have(k ∈ n |- goal) by Tautology.from(ltCase)
              val gtSeq = have(n ∈ k |- goal) by Tautology.from(gtCase)

              have(thesis) by Tautology.from(cmp, eqSeq, ltSeq, gtSeq)
            }

            thenHave(∃(k, (k ∈ ℕ) /\ (m === Succ(k))) |- (m === Succ(n)) \/ (m ∈ Succ(n)) \/ (Succ(n) ∈ m)) by LeftExists
            have(thesis) by Restate.from(lastStep)
          }

          val goal2 = (m === Succ(n)) \/ (m ∈ Succ(n)) \/ (Succ(n) ∈ m)

          val caseZeroSeq = have(m === zero |- goal2) by Tautology.from(caseZero)
          val caseSuccSeq = have(∃(k, (k ∈ ℕ) /\ (m === Succ(k))) |- goal2) by Tautology.from(caseSucc)

          have(thesis) by Tautology.from(mCases, caseZeroSeq, caseSuccSeq)
        }

        thenHave((m ∈ ℕ) ==> ((m === Succ(n)) \/ (m ∈ Succ(n)) \/ (Succ(n) ∈ m))) by Restate
        val allM = thenHave(∀(m, (m ∈ ℕ) ==> ((m === Succ(n)) \/ (m ∈ Succ(n)) \/ (Succ(n) ∈ m)))) by RightForall
        have(Q(Succ(n))) by Restate.from(allM)
        val imp = thenHave(Q(n) ==> Q(Succ(n))) by Tautology
        have(thesis) by Restate.from(imp)
      }
      thenHave((n ∈ ℕ) ==> (Q(n) ==> Q(Succ(n)))) by Tautology
      thenHave(thesis) by RightForall
    }

    val premise = have(Q(zero) /\ ∀(n, (n ∈ ℕ) ==> (Q(n) ==> Q(Succ(n))))) by Tautology.from(base, step)
    val all = have(∀(n, (n ∈ ℕ) ==> Q(n))) by Tautology.from(induction.of(Pred := Q), premise)

    // Instantiate at our n, then at m.
    assume(n ∈ ℕ)
    val impN = have((n ∈ ℕ) ==> Q(n)) by InstantiateForall(n)(all)
    val nInℕ2 = assume(n ∈ ℕ)
    val Qn = have(Q(n)) by Tautology.from(impN, nInℕ2)

    have(∀(m, (m ∈ ℕ) ==> ((m === n) \/ (m ∈ n) \/ (n ∈ m)))) by Restate.from(Qn)
    val imp = thenHave((m ∈ ℕ) ==> ((m === n) \/ (m ∈ n) \/ (n ∈ m))) by InstantiateForall(m)
    val mInℕ2 = assume(m ∈ ℕ)
    have((m === n) \/ (m ∈ n) \/ (n ∈ m)) by Tautology.from(imp)
    have(thesis) by Restate.from(lastStep)
  }

  /** Theorem: `∈_ℕ` is total on `ℕ`. */
  private val natMemRelTotal = Theorem(
    total(memRel)(ℕ)
  ) {
    val goal = ((m, n) ∈ memRel) \/ ((n, m) ∈ memRel) \/ (m === n)

    val mnGoal = have((m ∈ ℕ, n ∈ ℕ) |- goal) subproof {
      val mInℕ = assume(m ∈ ℕ)
      val nInℕ = assume(n ∈ ℕ)
      val cmp = have((m === n) \/ (m ∈ n) \/ (n ∈ m)) by Tautology.from(natComparability)
      val eqCase = have(m === n |- goal) by Tautology

      val mnCase = have(m ∈ n |- goal) subproof {
        assume(m ∈ n)
        have(thesis) by Tautology.from(MembershipRelation.membership.of(x := m, y := n, A := ℕ))
      }

      val nmCase = have(n ∈ m |- goal) subproof {
        assume(n ∈ m)
        have(thesis) by Tautology.from(MembershipRelation.membership.of(x := n, y := m, A := ℕ))
      }

      have(thesis) by Tautology.from(cmp, eqCase, mnCase, nmCase)
    }

    val all = have(∀(m, (m ∈ ℕ) ==> ∀(n, (n ∈ ℕ) ==> goal))) subproof {
      have((m ∈ ℕ) |- ∀(n, (n ∈ ℕ) ==> goal)) subproof {
        val mInℕ = assume(m ∈ ℕ)
        have((n ∈ ℕ) |- goal) subproof {
          val nInℕ = assume(n ∈ ℕ)
          have(goal) by Tautology.from(mnGoal, mInℕ, nInℕ)
        }
        thenHave((n ∈ ℕ) ==> goal) by Restate
        thenHave(∀(n, (n ∈ ℕ) ==> goal)) by RightForall
      }
      thenHave((m ∈ ℕ) ==> ∀(n, (n ∈ ℕ) ==> goal)) by Restate
      thenHave(thesis) by RightForall
    }

    val allBdd = have(∀(m ∈ ℕ, ∀(n ∈ ℕ, goal))) by Restate.from(all)
    have(thesis) by Substitute(total.definition.of(R := memRel, X := ℕ))(allBdd)
  }

  /** Theorem: `(ℕ, ∈_ℕ)` is a well-order. */
  val natWellOrder = Theorem(
    WellOrder.wellOrder(ℕ)(memRel)
  ) {
    // relation(memRel)
    val relOn = have(lisa.maths.SetTheory.Relations.Relation.relationOn(memRel)(ℕ)).by(Restate.from(MembershipRelation.isRelation.of(A := ℕ)))
    val rel = have(lisa.maths.SetTheory.Relations.Relation.relation(memRel)).by(Tautology.from(
      lisa.maths.SetTheory.Relations.BasicTheorems.relationOnIsRelation.of(R := memRel, X := ℕ),
      relOn
    ))

    // irreflexive(memRel)(ℕ)
    val irrefl = have(irreflexive(memRel)(ℕ)) by Restate.from(MembershipRelation.irreflexivity.of(A := ℕ))

    // transitive(memRel)(ℕ)
    val trans = have(transitive(memRel)(ℕ)) subproof {
      have((m ∈ ℕ, n ∈ ℕ, k ∈ ℕ, (m, n) ∈ memRel, (n, k) ∈ memRel) |- (m, k) ∈ memRel) subproof {
        val mInℕ = assume(m ∈ ℕ)
        val nInℕ = assume(n ∈ ℕ)
        val kInℕ = assume(k ∈ ℕ)

        val mnRel = assume((m, n) ∈ memRel)
        val mInN = have(m ∈ n) by Tautology.from(MembershipRelation.membership.of(x := m, y := n, A := ℕ))

        val nkRel = assume((n, k) ∈ memRel)
        val nInK = have(n ∈ k) by Tautology.from(MembershipRelation.membership.of(x := n, y := k, A := ℕ))

        // k is transitive (as a natural), so from m ∈ n and n ∈ k we infer m ∈ k.
        val kTrans = have(TransitiveSet.transitiveSet(k)) by Tautology.from(natElementsTransitive.of(n := k))
        val mInK = have(m ∈ k) by Tautology.from(TransitiveSet.transitivity.of(x := m, y := n, A := k), kTrans, mInN, nInK)

        have(thesis) by Tautology.from(MembershipRelation.membership.of(x := m, y := k, A := ℕ), mInK)
      }
      thenHave(() |- ((m ∈ ℕ) /\ (n ∈ ℕ) /\ (k ∈ ℕ) /\ ((m, n) ∈ memRel) /\ ((n, k) ∈ memRel)) ==> ((m, k) ∈ memRel)) by Tableau
      thenHave(() |- ∀(k, ((m ∈ ℕ) /\ (n ∈ ℕ) /\ (k ∈ ℕ) /\ ((m, n) ∈ memRel) /\ ((n, k) ∈ memRel)) ==> ((m, k) ∈ memRel))) by RightForall
      thenHave(() |- ∀(n, ∀(k, ((m ∈ ℕ) /\ (n ∈ ℕ) /\ (k ∈ ℕ) /\ ((m, n) ∈ memRel) /\ ((n, k) ∈ memRel)) ==> ((m, k) ∈ memRel)))) by RightForall
      val allConj = thenHave(() |- ∀(m, ∀(n, ∀(k, ((m ∈ ℕ) /\ (n ∈ ℕ) /\ (k ∈ ℕ) /\ ((m, n) ∈ memRel) /\ ((n, k) ∈ memRel)) ==> ((m, k) ∈ memRel))))) by RightForall
      val relImp = (((m, n) ∈ memRel) /\ ((n, k) ∈ memRel)) ==> ((m, k) ∈ memRel)

      have(∀(m, (m ∈ ℕ) ==> ∀(n, (n ∈ ℕ) ==> ∀(k, (k ∈ ℕ) ==> relImp)))) subproof {
        have((m ∈ ℕ) |- ∀(n, (n ∈ ℕ) ==> ∀(k, (k ∈ ℕ) ==> relImp))) subproof {
          val mInℕ = assume(m ∈ ℕ)

          have((n ∈ ℕ) |- ∀(k, (k ∈ ℕ) ==> relImp)) subproof {
            val nInℕ = assume(n ∈ ℕ)

            have((k ∈ ℕ) |- relImp) subproof {
              val kInℕ = assume(k ∈ ℕ)

              have(((m, n) ∈ memRel) /\ ((n, k) ∈ memRel) |- (m, k) ∈ memRel) subproof {
                assume(((m, n) ∈ memRel) /\ ((n, k) ∈ memRel))
                val mn = have((m, n) ∈ memRel) by Tautology
                val nk = have((n, k) ∈ memRel) by Tautology

                val allNk = have(∀(n, ∀(k, ((m ∈ ℕ) /\ (n ∈ ℕ) /\ (k ∈ ℕ) /\ ((m, n) ∈ memRel) /\ ((n, k) ∈ memRel)) ==> ((m, k) ∈ memRel)))).by(InstantiateForall(m)(allConj))
                val allK = thenHave(∀(k, ((m ∈ ℕ) /\ (n ∈ ℕ) /\ (k ∈ ℕ) /\ ((m, n) ∈ memRel) /\ ((n, k) ∈ memRel)) ==> ((m, k) ∈ memRel))) by InstantiateForall(n)
                val imp = thenHave(((m ∈ ℕ) /\ (n ∈ ℕ) /\ (k ∈ ℕ) /\ ((m, n) ∈ memRel) /\ ((n, k) ∈ memRel)) ==> ((m, k) ∈ memRel)) by InstantiateForall(k)

                have((m, k) ∈ memRel) by Tautology.from(imp, mn, nk)
              }
              thenHave(relImp) by Restate
            }
            thenHave((k ∈ ℕ) ==> relImp) by Restate
            thenHave(∀(k, (k ∈ ℕ) ==> relImp)) by RightForall
          }
          thenHave((n ∈ ℕ) ==> ∀(k, (k ∈ ℕ) ==> relImp)) by Restate
          thenHave(∀(n, (n ∈ ℕ) ==> ∀(k, (k ∈ ℕ) ==> relImp))) by RightForall
        }
        thenHave((m ∈ ℕ) ==> ∀(n, (n ∈ ℕ) ==> ∀(k, (k ∈ ℕ) ==> relImp))) by Restate
        thenHave(∀(m, (m ∈ ℕ) ==> ∀(n, (n ∈ ℕ) ==> ∀(k, (k ∈ ℕ) ==> relImp)))) by RightForall
      }

      thenHave(∀(m ∈ ℕ, ∀(n ∈ ℕ, ∀(k ∈ ℕ, relImp)))) by Restate
      thenHave(thesis) by Substitute(transitive.definition.of(R := memRel, X := ℕ))
    }

    val tot = have(total(memRel)(ℕ)).by(Restate.from(natMemRelTotal))
    val wf = have(wellFounded(memRel)(ℕ)).by(Restate.from(natMembershipWellFounded))

    have(thesis) by Tautology.from(
      WellOrder.wellOrder.definition.of(A := ℕ, < := memRel),
      lisa.maths.SetTheory.Order.TotalOrder.strictTotalOrder.definition.of(A := ℕ, < := memRel),
      lisa.maths.SetTheory.Order.PartialOrder.strictPartialOrder.definition.of(A := ℕ, < := memRel),
      rel,
      trans,
      irrefl,
      tot,
      wf
    )
  }

  /** Theorem: recursion equation for addition at `0` (recursion on the second argument). */
  val addZero = Theorem(m + zero === m) {
    val res = have(m + zero === m) subproof {
      val wo = have(WellOrder.wellOrder(ℕ)(memRel)).by(Restate.from(natWellOrder))

      val Fm = λ(x, λ(h, ε(y, ((x === zero) /\ (y === m)) \/ ∃(k, (k ∈ ℕ) /\ (x === Succ(k)) /\ (y === Succ(app(h)(k)))))))

      val Gm = Necessary.recursiveFunctionOn(Fm)(ℕ)(memRel)

      val eqAll = have(
        ∀(x ∈ ℕ, app(Gm)(x) === Fm(x)(Gm ↾ InitialSegment.initialSegment(x)(ℕ)(memRel)))
      ).by(Tautology.from(wo, Necessary.recursiveFunctionOnSpec.of(A := ℕ, R := memRel, Necessary.Func := Fm)))

      val eq0 = have(
        zero ∈ ℕ |- app(Gm)(zero) === Fm(zero)(Gm ↾ InitialSegment.initialSegment(zero)(ℕ)(memRel))
      ).by(InstantiateForall(zero)(eqAll))

      val init0 = have(zero ∈ ℕ |- InitialSegment.initialSegment(zero)(ℕ)(memRel) === zero).by(
        Restate.from(natInitialSegment.of(n := zero))
      )

      val eq0r = have(zero ∈ ℕ |- app(Gm)(zero) === Fm(zero)(Gm ↾ zero)).by(Substitute(init0)(eq0))

      val Q = λ(
        y,
        ((zero === zero) /\ (y === m)) \/
          ∃(k, (k ∈ ℕ) /\ (zero === Succ(k)) /\ (y === Succ(app(Gm ↾ zero)(k))))
      )

      val Fm0 = have(Fm(zero)(Gm ↾ zero) === ε(x, Q(x))).by(Restate)

      val zRefl = have(zero === zero) by Restate
      val mRefl = have(m === m) by Restate
      val Qm = have(Q(m)).by(Tautology.from(zRefl, mRefl))

      val uniq = have(∀(y, Q(y) ==> (y === m))) subproof {
        have(Q(y) |- y === m) subproof {
          assume(Q(y))

          val disj = have(
            ((zero === zero) /\ (y === m)) \/
              ∃(k, (k ∈ ℕ) /\ (zero === Succ(k)) /\ (y === Succ(app(Gm ↾ zero)(k))))
          ).by(Restate)

          val case1 = have(((zero === zero) /\ (y === m)) ==> (y === m)).by(Tautology)

          val contra = have(∃(k, (k ∈ ℕ) /\ (zero === Succ(k)) /\ (y === Succ(app(Gm ↾ zero)(k)))) |- ()) subproof {
            assume(∃(k, (k ∈ ℕ) /\ (zero === Succ(k)) /\ (y === Succ(app(Gm ↾ zero)(k)))))
            have((k ∈ ℕ) /\ (zero === Succ(k)) /\ (y === Succ(app(Gm ↾ zero)(k))) |- ()) subproof {
              val kInℕ = have((k ∈ ℕ) /\ (zero === Succ(k)) /\ (y === Succ(app(Gm ↾ zero)(k))) |- k ∈ ℕ).by(Tautology)
              val zEqSk = have((k ∈ ℕ) /\ (zero === Succ(k)) /\ (y === Succ(app(Gm ↾ zero)(k))) |- zero === Succ(k)).by(Tautology)
              val SkEq0 = have((k ∈ ℕ) /\ (zero === Succ(k)) /\ (y === Succ(app(Gm ↾ zero)(k))) |- Succ(k) === zero).by(Congruence.from(zEqSk))
              val SkNe0 = have(k ∈ ℕ |- (Succ(k) =/= zero)).by(Weakening(succNeZero.of(n := k)))
              val notSkEq0 = have((k ∈ ℕ) /\ (zero === Succ(k)) /\ (y === Succ(app(Gm ↾ zero)(k))) |- ¬(Succ(k) === zero)).by(Tautology.from(SkNe0, kInℕ))
              have(thesis).by(Tautology.from(SkEq0, notSkEq0))
            }
            thenHave(thesis).by(LeftExists)
          }
          val case2 = have(∃(k, (k ∈ ℕ) /\ (zero === Succ(k)) /\ (y === Succ(app(Gm ↾ zero)(k)))) ==> (y === m)).by(
            Restate.from(have(∃(k, (k ∈ ℕ) /\ (zero === Succ(k)) /\ (y === Succ(app(Gm ↾ zero)(k)))) |- y === m).by(Weakening(contra)))
          )

          have(thesis).by(Tautology.from(disj, case1, case2))
        }
        thenHave(Q(y) ==> (y === m)).by(Restate)
        thenHave(thesis).by(RightForall)
      }

      val ex1 = have(Quantifiers.∃!(x, Q(x))) subproof {
        have(Q(m) /\ ∀(y, Q(y) ==> (y === m))).by(Tautology.from(Qm, uniq))
        thenHave(∃(x, Q(x) /\ ∀(k, Q(k) ==> (k === x)))).by(RightExists)
        thenHave(thesis).by(Substitute(Quantifiers.∃!.definition.of(P := Q)))
      }

      val epsIff = Quantifiers.existsOneEpsilonUniqueness.of(P := Q, y := m)
      val epsIff2 = have(Q(m) <=> (m === ε(x, Q(x)))).by(Cut(ex1, epsIff))
      val mEqEps = have(m === ε(x, Q(x))).by(Tautology.from(Qm, epsIff2))
      val epsSym = have(m === ε(x, Q(x)) |- ε(x, Q(x)) === m) by Congruence
      val epsEq = have(ε(x, Q(x)) === m).by(Cut(mEqEps, epsSym))

      val addDef0 = have(m + zero === app(Gm)(zero)).by(Restate.from(add.definition.of(m := m, n := zero)))

      val rhsEqM = have(Fm(zero)(Gm ↾ zero) === m).by(Congruence.from(Fm0, epsEq))

      val rec0 = have(zero ∈ ℕ |- m + zero === m).by(Congruence.from(addDef0, eq0r, rhsEqM))
      have(thesis).by(Cut(zeroInℕ, rec0))
    }
    have(thesis).by(Restate.from(res))
  }

  /** Theorem: recursion equation for addition at successors (requires `n ∈ ℕ`). */
  val addSucc = Theorem(n ∈ ℕ |- (m + Succ(n) === Succ(m + n))) {
    val nInℕ = assume(n ∈ ℕ)

    val wo = have(WellOrder.wellOrder(ℕ)(memRel)).by(Restate.from(natWellOrder))

    val Fm = λ(x, λ(h, ε(y, ((x === zero) /\ (y === m)) \/ ∃(k, (k ∈ ℕ) /\ (x === Succ(k)) /\ (y === Succ(app(h)(k)))))))

    val Gm = Necessary.recursiveFunctionOn(Fm)(ℕ)(memRel)

    val eqAll = have(
      ∀(x ∈ ℕ, app(Gm)(x) === Fm(x)(Gm ↾ InitialSegment.initialSegment(x)(ℕ)(memRel)))
    ).by(Tautology.from(wo, Necessary.recursiveFunctionOnSpec.of(A := ℕ, R := memRel, Necessary.Func := Fm)))

    val SnInℕ = have(Succ(n) ∈ ℕ).by(Cut(nInℕ, succClosed.of(n := n)))

    val eqSn = have(
      Succ(n) ∈ ℕ |- app(Gm)(Succ(n)) === Fm(Succ(n))(Gm ↾ InitialSegment.initialSegment(Succ(n))(ℕ)(memRel))
    ).by(InstantiateForall(Succ(n))(eqAll))

    val initSn = have(Succ(n) ∈ ℕ |- InitialSegment.initialSegment(Succ(n))(ℕ)(memRel) === Succ(n)).by(
      Restate.from(natInitialSegment.of(n := Succ(n)))
    )

    val eqSnr = have(Succ(n) ∈ ℕ |- app(Gm)(Succ(n)) === Fm(Succ(n))(Gm ↾ Succ(n))).by(Substitute(initSn)(eqSn))

    val hSn = Gm ↾ Succ(n)

    val Q = λ(
      y,
      ((Succ(n) === zero) /\ (y === m)) \/
        ∃(k, (k ∈ ℕ) /\ (Succ(n) === Succ(k)) /\ (y === Succ(app(hSn)(k))))
    )

    val FmSn = have(Fm(Succ(n))(hSn) === ε(y, Q(y))).by(Restate)

    val exY = have(∃(y, Q(y))) subproof {
      have((n ∈ ℕ) /\ (Succ(n) === Succ(n)) /\ (Succ(app(hSn)(n)) === Succ(app(hSn)(n)))).by(Tautology.from(nInℕ))
      thenHave(
        ∃(k, (k ∈ ℕ) /\ (Succ(n) === Succ(k)) /\ (Succ(app(hSn)(n)) === Succ(app(hSn)(k))))
      ).by(RightExists)
      thenHave(Q(Succ(app(hSn)(n)))).by(Tautology)
      thenHave(thesis).by(RightExists)
    }

    val uniq = have(∀(y, Q(y) ==> (y === Succ(app(hSn)(n))))) subproof {
      have(Q(y) |- y === Succ(app(hSn)(n))) subproof {
        assume(Q(y))

        val SnNe0 = have(Succ(n) =/= zero).by(Tautology.from(nInℕ, succNeZero.of(n := n)))
        val notSnEq0 = have(¬(Succ(n) === zero)).by(Tautology.from(SnNe0))

        val notCase1 = have(¬((Succ(n) === zero) /\ (y === m))).by(Tautology.from(notSnEq0))
        val notCase1Under = have(Q(y) |- ¬((Succ(n) === zero) /\ (y === m))).by(Weakening(notCase1))

        val disj = have(
          ((Succ(n) === zero) /\ (y === m)) \/
            ∃(k, (k ∈ ℕ) /\ (Succ(n) === Succ(k)) /\ (y === Succ(app(hSn)(k))))
        ).by(Restate)

        val exK = have(Q(y) |- ∃(k, (k ∈ ℕ) /\ (Succ(n) === Succ(k)) /\ (y === Succ(app(hSn)(k))))).by(Tautology.from(disj, notCase1Under))

        val fromExK = have(
          ∃(k, (k ∈ ℕ) /\ (Succ(n) === Succ(k)) /\ (y === Succ(app(hSn)(k)))) |- y === Succ(app(hSn)(n))
        ) subproof {
          assume(∃(k, (k ∈ ℕ) /\ (Succ(n) === Succ(k)) /\ (y === Succ(app(hSn)(k)))))

          have((k ∈ ℕ) /\ (Succ(n) === Succ(k)) /\ (y === Succ(app(hSn)(k))) |- y === Succ(app(hSn)(n))) subproof {
            val SnEqSk = have((k ∈ ℕ) /\ (Succ(n) === Succ(k)) /\ (y === Succ(app(hSn)(k))) |- Succ(n) === Succ(k)).by(Tautology)
            val yEq = have((k ∈ ℕ) /\ (Succ(n) === Succ(k)) /\ (y === Succ(app(hSn)(k))) |- y === Succ(app(hSn)(k))).by(Tautology)

            val inj = have(Succ(n) === Succ(k) |- n === k).by(Tautology.from(succInjective.of(m := n, n := k)))

            val nEqk = have((k ∈ ℕ) /\ (Succ(n) === Succ(k)) /\ (y === Succ(app(hSn)(k))) |- n === k).by(Cut(SnEqSk, inj))
            val kEqn = have((k ∈ ℕ) /\ (Succ(n) === Succ(k)) /\ (y === Succ(app(hSn)(k))) |- k === n).by(Congruence.from(nEqk))

            val hkEq = have((k ∈ ℕ) /\ (Succ(n) === Succ(k)) /\ (y === Succ(app(hSn)(k))) |- app(hSn)(k) === app(hSn)(n)).by(
              Congruence.from(kEqn)
            )
            val SkEqSn = have((k ∈ ℕ) /\ (Succ(n) === Succ(k)) /\ (y === Succ(app(hSn)(k))) |- Succ(app(hSn)(k)) === Succ(app(hSn)(n))).by(
              Congruence.from(hkEq)
            )

            have(thesis).by(Congruence.from(yEq, SkEqSn))
          }
          thenHave(∃(k, (k ∈ ℕ) /\ (Succ(n) === Succ(k)) /\ (y === Succ(app(hSn)(k)))) |- y === Succ(app(hSn)(n))).by(LeftExists)
        }

        have(thesis).by(Cut(exK, fromExK))
      }
      thenHave(Q(y) ==> (y === Succ(app(hSn)(n)))).by(Restate)
      thenHave(thesis).by(RightForall)
    }

    val epsEq = have(ε(y, Q(y)) === Succ(app(hSn)(n))) subproof {
      val epsQ = have(Q(ε(y, Q(y)))).by(Cut(exY, Quantifiers.existsEpsilon.of(x := y, P := Q)))
      val epsImp = have(Q(ε(y, Q(y))) ==> (ε(y, Q(y)) === Succ(app(hSn)(n)))).by(InstantiateForall(ε(y, Q(y)))(uniq))
      have(thesis).by(Tautology.from(epsQ, epsImp))
    }

    val hSnAtN = have(app(hSn)(n) === app(Gm)(n)) subproof {
      val nSubℕ = have(n ⊆ ℕ).by(Cut(nInℕ, `n ∈ ℕ -> n ⊆ ℕ`))
      val SnSubℕ = have(Succ(n) ⊆ ℕ).by(Tautology.from(succSubsetℕ, nSubℕ, nInℕ))
      val nInSn = have(n ∈ Succ(n)).by(Weakening(nInSucc))
      val restEq = have((functionOn(Gm)(ℕ), Succ(n) ⊆ ℕ, n ∈ Succ(n)) |- app(Gm ↾ Succ(n))(n) === app(Gm)(n)).by(
        Restate.from(Necessary.restrictionAppSubset.of(f := Gm, A := ℕ, B := Succ(n), x := n))
      )
      val GmOn = have(functionOn(Gm)(ℕ)).by(Tautology.from(wo, Necessary.recursiveFunctionOnSpec.of(A := ℕ, R := memRel, Necessary.Func := Fm)))
      have(thesis).by(Tautology.from(restEq, GmOn, SnSubℕ, nInSn))
    }

    val rhs1 = have(Fm(Succ(n))(hSn) === Succ(app(hSn)(n))).by(Congruence.from(FmSn, epsEq))
    val rhs2 = have(Succ(app(hSn)(n)) === Succ(app(Gm)(n))).by(Congruence.from(hSnAtN))
    val trans = have((Fm(Succ(n))(hSn) === Succ(app(hSn)(n)), Succ(app(hSn)(n)) === Succ(app(Gm)(n))) |- Fm(Succ(n))(hSn) === Succ(app(Gm)(n))).by(Congruence)
    val trans1 = have((Fm(Succ(n))(hSn) === Succ(app(hSn)(n))) |- Fm(Succ(n))(hSn) === Succ(app(Gm)(n))).by(Cut(rhs2, trans))
    val rhsEq = have(Fm(Succ(n))(hSn) === Succ(app(Gm)(n))).by(Cut(rhs1, trans1))

    val addDefSn = have(m + Succ(n) === app(Gm)(Succ(n))).by(Restate.from(add.definition.of(m := m, n := Succ(n))))
    val addDefN = have(m + n === app(Gm)(n)).by(Restate.from(add.definition.of(m := m, n := n)))

    val Smn = have(Succ(m + n) === Succ(app(Gm)(n))).by(Congruence.from(addDefN))

    val recSn = have(Succ(n) ∈ ℕ |- m + Succ(n) === Succ(m + n)).by(Congruence.from(addDefSn, eqSnr, rhsEq, Smn))
    have(m + Succ(n) === Succ(m + n)).by(Cut(SnInℕ, recSn))
    thenHave(thesis).by(Restate)
  }

  /** Theorem: recursion equation for multiplication at `0` (recursion on the second argument). */
  val mulZero = Theorem(m * zero === zero) {
    val res = have(m * zero === zero) subproof {
      val wo = have(WellOrder.wellOrder(ℕ)(memRel)).by(Restate.from(natWellOrder))

      val Fm = λ(x, λ(h, ε(y, ((x === zero) /\ (y === zero)) \/ ∃(k, (k ∈ ℕ) /\ (x === Succ(k)) /\ (y === add(app(h)(k))(m))))))

      val Gm = Necessary.recursiveFunctionOn(Fm)(ℕ)(memRel)

      val eqAll = have(
        ∀(x ∈ ℕ, app(Gm)(x) === Fm(x)(Gm ↾ InitialSegment.initialSegment(x)(ℕ)(memRel)))
      ).by(Tautology.from(wo, Necessary.recursiveFunctionOnSpec.of(A := ℕ, R := memRel, Necessary.Func := Fm)))

      val eq0 = have(
        zero ∈ ℕ |- app(Gm)(zero) === Fm(zero)(Gm ↾ InitialSegment.initialSegment(zero)(ℕ)(memRel))
      ).by(InstantiateForall(zero)(eqAll))

      val init0 = have(zero ∈ ℕ |- InitialSegment.initialSegment(zero)(ℕ)(memRel) === zero).by(
        Restate.from(natInitialSegment.of(n := zero))
      )

      val eq0r = have(zero ∈ ℕ |- app(Gm)(zero) === Fm(zero)(Gm ↾ zero)).by(Substitute(init0)(eq0))

      val Q = λ(
        y,
        ((zero === zero) /\ (y === zero)) \/
          ∃(k, (k ∈ ℕ) /\ (zero === Succ(k)) /\ (y === add(app(Gm ↾ zero)(k))(m)))
      )

      val Fm0 = have(Fm(zero)(Gm ↾ zero) === ε(y, Q(y))).by(Restate)

      val exY = have(∃(y, Q(y))) subproof {
        val zRefl = have(zero === zero).by(Restate)
        have(Q(zero)).by(Tautology.from(zRefl))
        thenHave(thesis).by(RightExists)
      }

      val uniq = have(∀(y, Q(y) ==> (y === zero))) subproof {
        have(Q(y) |- y === zero) subproof {
          assume(Q(y))

          val disj = have(
            ((zero === zero) /\ (y === zero)) \/
              ∃(k, (k ∈ ℕ) /\ (zero === Succ(k)) /\ (y === add(app(Gm ↾ zero)(k))(m)))
          ).by(Restate)

          val case1 = have((zero === zero) /\ (y === zero) |- y === zero).by(Tautology)

          val case2 = have(∃(k, (k ∈ ℕ) /\ (zero === Succ(k)) /\ (y === add(app(Gm ↾ zero)(k))(m))) |- y === zero) subproof {
            assume(∃(k, (k ∈ ℕ) /\ (zero === Succ(k)) /\ (y === add(app(Gm ↾ zero)(k))(m))))

            have((k ∈ ℕ) /\ (zero === Succ(k)) /\ (y === add(app(Gm ↾ zero)(k))(m)) |- ()) subproof {
              val kInℕ = have((k ∈ ℕ) /\ (zero === Succ(k)) /\ (y === add(app(Gm ↾ zero)(k))(m)) |- k ∈ ℕ).by(Tautology)
              val zEqSk = have((k ∈ ℕ) /\ (zero === Succ(k)) /\ (y === add(app(Gm ↾ zero)(k))(m)) |- zero === Succ(k)).by(Tautology)
              val SkEq0 = have((k ∈ ℕ) /\ (zero === Succ(k)) /\ (y === add(app(Gm ↾ zero)(k))(m)) |- Succ(k) === zero).by(Congruence.from(zEqSk))
              val SkNe0 = have(k ∈ ℕ |- (Succ(k) =/= zero)).by(Weakening(succNeZero.of(n := k)))
              val notSkEq0 = have((k ∈ ℕ) /\ (zero === Succ(k)) /\ (y === add(app(Gm ↾ zero)(k))(m)) |- ¬(Succ(k) === zero)).by(Tautology.from(SkNe0, kInℕ))
              have(thesis).by(Tautology.from(SkEq0, notSkEq0))
            }
            thenHave(∃(k, (k ∈ ℕ) /\ (zero === Succ(k)) /\ (y === add(app(Gm ↾ zero)(k))(m))) |- ()).by(LeftExists)
            have(thesis).by(Weakening(lastStep))
          }

          have(thesis).by(Tautology.from(disj, case1, case2))
        }
        thenHave(Q(y) ==> (y === zero)).by(Restate)
        thenHave(thesis).by(RightForall)
      }

      val epsEq = have(ε(y, Q(y)) === zero) subproof {
        val epsQ = have(Q(ε(y, Q(y)))).by(Cut(exY, Quantifiers.existsEpsilon.of(x := y, P := Q)))
        val epsImp = have(Q(ε(y, Q(y))) ==> (ε(y, Q(y)) === zero)).by(InstantiateForall(ε(y, Q(y)))(uniq))
        have(thesis).by(Tautology.from(epsQ, epsImp))
      }

      val mulDef0 = have(m * zero === app(Gm)(zero)).by(Restate.from(mul.definition.of(m := m, n := zero)))

      val rhsEq0 = have(Fm(zero)(Gm ↾ zero) === zero).by(Congruence.from(Fm0, epsEq))

      val rec0 = have(zero ∈ ℕ |- m * zero === zero).by(Congruence.from(mulDef0, eq0r, rhsEq0))
      have(thesis).by(Cut(zeroInℕ, rec0))
    }
    have(thesis).by(Restate.from(res))
  }

  /** Theorem: recursion equation for multiplication at successors (requires `n ∈ ℕ`). */
  val mulSucc = Theorem(n ∈ ℕ |- (m * Succ(n) === (m * n) + m)) {
    val nInℕ = assume(n ∈ ℕ)

      val wo = have(WellOrder.wellOrder(ℕ)(memRel)).by(Restate.from(natWellOrder))

      val Fm = λ(x, λ(h, ε(y, ((x === zero) /\ (y === zero)) \/ ∃(k, (k ∈ ℕ) /\ (x === Succ(k)) /\ (y === add(app(h)(k))(m))))))

      val Gm = Necessary.recursiveFunctionOn(Fm)(ℕ)(memRel)

      val eqAll = have(
        ∀(x ∈ ℕ, app(Gm)(x) === Fm(x)(Gm ↾ InitialSegment.initialSegment(x)(ℕ)(memRel)))
      ).by(Tautology.from(wo, Necessary.recursiveFunctionOnSpec.of(A := ℕ, R := memRel, Necessary.Func := Fm)))

      val SnInℕ = have(Succ(n) ∈ ℕ).by(Cut(nInℕ, succClosed.of(n := n)))

      val eqSn = have(
        Succ(n) ∈ ℕ |- app(Gm)(Succ(n)) === Fm(Succ(n))(Gm ↾ InitialSegment.initialSegment(Succ(n))(ℕ)(memRel))
      ).by(InstantiateForall(Succ(n))(eqAll))

      val initSn = have(Succ(n) ∈ ℕ |- InitialSegment.initialSegment(Succ(n))(ℕ)(memRel) === Succ(n)).by(
        Restate.from(natInitialSegment.of(n := Succ(n)))
      )

      val eqSnr = have(Succ(n) ∈ ℕ |- app(Gm)(Succ(n)) === Fm(Succ(n))(Gm ↾ Succ(n))).by(Substitute(initSn)(eqSn))

      val hSn = Gm ↾ Succ(n)

      val Q = λ(
        y,
        ((Succ(n) === zero) /\ (y === zero)) \/
          ∃(k, (k ∈ ℕ) /\ (Succ(n) === Succ(k)) /\ (y === add(app(hSn)(k))(m)))
      )

      val FmSn = have(Fm(Succ(n))(hSn) === ε(y, Q(y))).by(Restate)

      val exY = have(∃(y, Q(y))) subproof {
        have((n ∈ ℕ) /\ (Succ(n) === Succ(n)) /\ (add(app(hSn)(n))(m) === add(app(hSn)(n))(m))).by(Tautology.from(nInℕ))
        thenHave(∃(k, (k ∈ ℕ) /\ (Succ(n) === Succ(k)) /\ (add(app(hSn)(n))(m) === add(app(hSn)(k))(m)))).by(RightExists)
        thenHave(Q(add(app(hSn)(n))(m))).by(Tautology)
        thenHave(thesis).by(RightExists)
      }

      val uniq = have(∀(y, Q(y) ==> (y === add(app(hSn)(n))(m)))) subproof {
        have(Q(y) |- y === add(app(hSn)(n))(m)) subproof {
          assume(Q(y))

          val SnNe0 = have(Succ(n) =/= zero).by(Tautology.from(nInℕ, succNeZero.of(n := n)))
          val notSnEq0 = have(¬(Succ(n) === zero)).by(Tautology.from(SnNe0))

          val notCase1 = have(¬((Succ(n) === zero) /\ (y === zero))).by(Tautology.from(notSnEq0))
          val notCase1Under = have(Q(y) |- ¬((Succ(n) === zero) /\ (y === zero))).by(Weakening(notCase1))

          val disj = have(
            ((Succ(n) === zero) /\ (y === zero)) \/
              ∃(k, (k ∈ ℕ) /\ (Succ(n) === Succ(k)) /\ (y === add(app(hSn)(k))(m)))
          ).by(Restate)

          val exK = have(Q(y) |- ∃(k, (k ∈ ℕ) /\ (Succ(n) === Succ(k)) /\ (y === add(app(hSn)(k))(m)))).by(Tautology.from(disj, notCase1Under))

          val fromExK = have(
            ∃(k, (k ∈ ℕ) /\ (Succ(n) === Succ(k)) /\ (y === add(app(hSn)(k))(m))) |- y === add(app(hSn)(n))(m)
          ) subproof {
            assume(∃(k, (k ∈ ℕ) /\ (Succ(n) === Succ(k)) /\ (y === add(app(hSn)(k))(m))))

            have((k ∈ ℕ) /\ (Succ(n) === Succ(k)) /\ (y === add(app(hSn)(k))(m)) |- y === add(app(hSn)(n))(m)) subproof {
              val SnEqSk = have((k ∈ ℕ) /\ (Succ(n) === Succ(k)) /\ (y === add(app(hSn)(k))(m)) |- Succ(n) === Succ(k)).by(Tautology)
              val yEq = have((k ∈ ℕ) /\ (Succ(n) === Succ(k)) /\ (y === add(app(hSn)(k))(m)) |- y === add(app(hSn)(k))(m)).by(Tautology)

              val inj = have(Succ(n) === Succ(k) |- n === k).by(Tautology.from(succInjective.of(m := n, n := k)))

              val nEqk = have((k ∈ ℕ) /\ (Succ(n) === Succ(k)) /\ (y === add(app(hSn)(k))(m)) |- n === k).by(Cut(SnEqSk, inj))
              val kEqn = have((k ∈ ℕ) /\ (Succ(n) === Succ(k)) /\ (y === add(app(hSn)(k))(m)) |- k === n).by(Congruence.from(nEqk))

              val hkEq = have((k ∈ ℕ) /\ (Succ(n) === Succ(k)) /\ (y === add(app(hSn)(k))(m)) |- app(hSn)(k) === app(hSn)(n)).by(
                Congruence.from(kEqn)
              )

              val addEq = have((k ∈ ℕ) /\ (Succ(n) === Succ(k)) /\ (y === add(app(hSn)(k))(m)) |- add(app(hSn)(k))(m) === add(app(hSn)(n))(m)).by(
                Congruence.from(hkEq)
              )

              have(thesis).by(Congruence.from(yEq, addEq))
            }
            thenHave(∃(k, (k ∈ ℕ) /\ (Succ(n) === Succ(k)) /\ (y === add(app(hSn)(k))(m))) |- y === add(app(hSn)(n))(m)).by(LeftExists)
          }

          have(thesis).by(Cut(exK, fromExK))
        }
        thenHave(Q(y) ==> (y === add(app(hSn)(n))(m))).by(Restate)
        thenHave(thesis).by(RightForall)
      }

      val epsEq = have(ε(y, Q(y)) === add(app(hSn)(n))(m)) subproof {
        val epsQ = have(Q(ε(y, Q(y)))).by(Cut(exY, Quantifiers.existsEpsilon.of(x := y, P := Q)))
        val epsImp = have(Q(ε(y, Q(y))) ==> (ε(y, Q(y)) === add(app(hSn)(n))(m))).by(InstantiateForall(ε(y, Q(y)))(uniq))
        have(thesis).by(Tautology.from(epsQ, epsImp))
      }

      val hSnAtN = have(app(hSn)(n) === app(Gm)(n)) subproof {
        val nSubℕ = have(n ⊆ ℕ).by(Cut(nInℕ, `n ∈ ℕ -> n ⊆ ℕ`))
        val SnSubℕ = have(Succ(n) ⊆ ℕ).by(Tautology.from(succSubsetℕ, nSubℕ, nInℕ))
        val nInSn = have(n ∈ Succ(n)).by(Weakening(nInSucc.of(n := n)))
        val restEq = have((functionOn(Gm)(ℕ), Succ(n) ⊆ ℕ, n ∈ Succ(n)) |- app(Gm ↾ Succ(n))(n) === app(Gm)(n)).by(
          Restate.from(Necessary.restrictionAppSubset.of(f := Gm, A := ℕ, B := Succ(n), x := n))
        )
        val GmOn = have(functionOn(Gm)(ℕ)).by(Tautology.from(wo, Necessary.recursiveFunctionOnSpec.of(A := ℕ, R := memRel, Necessary.Func := Fm)))
        have(thesis).by(Tautology.from(restEq, GmOn, SnSubℕ, nInSn))
      }

      val rhs1 = have(Fm(Succ(n))(hSn) === add(app(hSn)(n))(m)).by(Congruence.from(FmSn, epsEq))
      val rhs2 = have(add(app(hSn)(n))(m) === add(app(Gm)(n))(m)).by(Congruence.from(hSnAtN))
      val trans = have((Fm(Succ(n))(hSn) === add(app(hSn)(n))(m), add(app(hSn)(n))(m) === add(app(Gm)(n))(m)) |- Fm(Succ(n))(hSn) === add(app(Gm)(n))(m)).by(Congruence)
      val trans1 = have((Fm(Succ(n))(hSn) === add(app(hSn)(n))(m)) |- Fm(Succ(n))(hSn) === add(app(Gm)(n))(m)).by(Cut(rhs2, trans))
      val rhsEq = have(Fm(Succ(n))(hSn) === add(app(Gm)(n))(m)).by(Cut(rhs1, trans1))

      val mulDefSn = have(m * Succ(n) === app(Gm)(Succ(n))).by(Restate.from(mul.definition.of(m := m, n := Succ(n))))
      val mulDefN = have(m * n === app(Gm)(n)).by(Restate.from(mul.definition.of(m := m, n := n)))

      val mulDefNsym = have(app(Gm)(n) === m * n).by(Congruence.from(mulDefN))
      val addRhs = have(add(app(Gm)(n))(m) === (m * n) + m).by(Congruence.from(mulDefNsym))

      val recSn = have(Succ(n) ∈ ℕ |- m * Succ(n) === (m * n) + m).by(Congruence.from(mulDefSn, eqSnr, rhsEq, addRhs))
        val res = have(m * Succ(n) === (m * n) + m).by(Cut(SnInℕ, recSn))
        have(thesis).by(Restate.from(res))
  }

  /** Theorem: closure of addition on `ℕ`. */
  val addClosed = Theorem((m ∈ ℕ, n ∈ ℕ) |- ((m + n) ∈ ℕ)) {
    val k = variable[Ind]

    val P = λ(n, ∀(k, (k ∈ ℕ) ==> ((k + n) ∈ ℕ)))

    val indUnfolded = have(
      (∀(k, (k ∈ ℕ) ==> ((k + zero) ∈ ℕ))) /\
        ∀(
          n,
          (n ∈ ℕ) ==>
            (∀(k, (k ∈ ℕ) ==> ((k + n) ∈ ℕ)) ==> ∀(k, (k ∈ ℕ) ==> ((k + Succ(n)) ∈ ℕ)))
        ) ==> ∀(n, (n ∈ ℕ) ==> ∀(k, (k ∈ ℕ) ==> ((k + n) ∈ ℕ)))
    ).by(Restate.from(induction of (Pred := P)))

    val baseAll = have(∀(k, (k ∈ ℕ) ==> ((k + zero) ∈ ℕ))) subproof {
      have((k ∈ ℕ) ==> ((k + zero) ∈ ℕ)) subproof {
        val kInℕ = assume(k ∈ ℕ)
        val eq = have(k + zero === k).by(Restate.from(addZero.of(m := k)))
        val iff = have((k + zero) ∈ ℕ <=> (k ∈ ℕ)).by(Congruence.from(eq))
        have((k + zero) ∈ ℕ).by(Tautology.from(iff, kInℕ))
      }
      thenHave(thesis).by(RightForall)
    }

    val stepAll = have(∀(n, (n ∈ ℕ) ==> (∀(k, (k ∈ ℕ) ==> ((k + n) ∈ ℕ)) ==> ∀(k, (k ∈ ℕ) ==> ((k + Succ(n)) ∈ ℕ))))) subproof {
      have((n ∈ ℕ) ==> (∀(k, (k ∈ ℕ) ==> ((k + n) ∈ ℕ)) ==> ∀(k, (k ∈ ℕ) ==> ((k + Succ(n)) ∈ ℕ)))) subproof {
        val nInℕ = assume(n ∈ ℕ)
        val IH = assume(∀(k, (k ∈ ℕ) ==> ((k + n) ∈ ℕ)))

        have(∀(k, (k ∈ ℕ) ==> ((k + Succ(n)) ∈ ℕ))) subproof {
          have((k ∈ ℕ) ==> ((k + Succ(n)) ∈ ℕ)) subproof {
            val kInℕ = assume(k ∈ ℕ)

            val ihImp = have((k ∈ ℕ) ==> ((k + n) ∈ ℕ)).by(InstantiateForall(k)(IH))
            val knInℕ = have((k + n) ∈ ℕ).by(Tautology.from(ihImp, kInℕ))

            val SknInℕ = have(Succ(k + n) ∈ ℕ).by(Cut(knInℕ, succClosed.of(n := k + n)))

            val nInℕw = have(n ∈ ℕ).by(Weakening(nInℕ))
            val eq = have(k + Succ(n) === Succ(k + n)).by(Cut(nInℕw, addSucc.of(m := k)))
            val iff = have((k + Succ(n)) ∈ ℕ <=> (Succ(k + n) ∈ ℕ)).by(Congruence.from(eq))
            have((k + Succ(n)) ∈ ℕ).by(Tautology.from(iff, SknInℕ))
          }
          thenHave(thesis).by(RightForall)
        }
      }
      thenHave(thesis).by(RightForall)
    }

    val premiseAll = have((∀(k, (k ∈ ℕ) ==> ((k + zero) ∈ ℕ))) /\ ∀(n, (n ∈ ℕ) ==> (∀(k, (k ∈ ℕ) ==> ((k + n) ∈ ℕ)) ==> ∀(k, (k ∈ ℕ) ==> ((k + Succ(n)) ∈ ℕ))))).by(Tautology.from(baseAll, stepAll))
    val allAll = have(∀(n, (n ∈ ℕ) ==> ∀(k, (k ∈ ℕ) ==> ((k + n) ∈ ℕ)))).by(Tautology.from(indUnfolded, premiseAll))

    val mInℕ = assume(m ∈ ℕ)
    val nInℕ = assume(n ∈ ℕ)

    val nImp = have((n ∈ ℕ) ==> ∀(k, (k ∈ ℕ) ==> ((k + n) ∈ ℕ))).by(InstantiateForall(n)(allAll))
    val allK = have(∀(k, (k ∈ ℕ) ==> ((k + n) ∈ ℕ))).by(Tautology.from(nImp, nInℕ))

    val mImp = have((m ∈ ℕ) ==> ((m + n) ∈ ℕ)).by(InstantiateForall(m)(allK))
    val res = have((m + n) ∈ ℕ).by(Tautology.from(mImp, mInℕ))
    have(thesis).by(Restate.from(res))
  }

  /** Theorem: closure of multiplication on `ℕ`. */
  val mulClosed = Theorem((m ∈ ℕ, n ∈ ℕ) |- ((m * n) ∈ ℕ)) {
    val k = variable[Ind]

    val P = λ(n, ∀(k, (k ∈ ℕ) ==> ((k * n) ∈ ℕ)))

    val indUnfolded = have(
      (∀(k, (k ∈ ℕ) ==> ((k * zero) ∈ ℕ))) /\
        ∀(
          n,
          (n ∈ ℕ) ==>
            (∀(k, (k ∈ ℕ) ==> ((k * n) ∈ ℕ)) ==> ∀(k, (k ∈ ℕ) ==> ((k * Succ(n)) ∈ ℕ)))
        ) ==> ∀(n, (n ∈ ℕ) ==> ∀(k, (k ∈ ℕ) ==> ((k * n) ∈ ℕ)))
    ).by(Restate.from(induction of (Pred := P)))

    val baseAll = have(∀(k, (k ∈ ℕ) ==> ((k * zero) ∈ ℕ))) subproof {
      have((k ∈ ℕ) ==> ((k * zero) ∈ ℕ)) subproof {
        assume(k ∈ ℕ)
        val eq = have(k * zero === zero).by(Restate.from(mulZero.of(m := k)))
        val iff = have((k * zero) ∈ ℕ <=> (zero ∈ ℕ)).by(Congruence.from(eq))
        have((k * zero) ∈ ℕ).by(Tautology.from(iff, zeroInℕ))
      }
      thenHave(thesis).by(RightForall)
    }

    val stepAll = have(∀(n, (n ∈ ℕ) ==> (∀(k, (k ∈ ℕ) ==> ((k * n) ∈ ℕ)) ==> ∀(k, (k ∈ ℕ) ==> ((k * Succ(n)) ∈ ℕ))))) subproof {
      have((n ∈ ℕ) ==> (∀(k, (k ∈ ℕ) ==> ((k * n) ∈ ℕ)) ==> ∀(k, (k ∈ ℕ) ==> ((k * Succ(n)) ∈ ℕ)))) subproof {
        val nInℕ = assume(n ∈ ℕ)
        val IH = assume(∀(k, (k ∈ ℕ) ==> ((k * n) ∈ ℕ)))

        have(∀(k, (k ∈ ℕ) ==> ((k * Succ(n)) ∈ ℕ))) subproof {
          have((k ∈ ℕ) ==> ((k * Succ(n)) ∈ ℕ)) subproof {
            val kInℕ = assume(k ∈ ℕ)

            val ihImp = have((k ∈ ℕ) ==> ((k * n) ∈ ℕ)).by(InstantiateForall(k)(IH))
            val knInℕ = have((k * n) ∈ ℕ).by(Tautology.from(ihImp, kInℕ))

            val rhsInℕ = have(((k * n) + k) ∈ ℕ).by(
              Tautology.from(addClosed.of(m := (k * n), n := k), knInℕ, kInℕ)
            )
            val nInℕw = have(n ∈ ℕ).by(Weakening(nInℕ))
            val eq = have(k * Succ(n) === (k * n) + k).by(Cut(nInℕw, mulSucc.of(m := k)))
            val iff = have((k * Succ(n)) ∈ ℕ <=> (((k * n) + k) ∈ ℕ)).by(Congruence.from(eq))
            have((k * Succ(n)) ∈ ℕ).by(Tautology.from(iff, rhsInℕ))
          }
          thenHave(thesis).by(RightForall)
        }
      }
      thenHave(thesis).by(RightForall)
    }

    val premiseAll = have((∀(k, (k ∈ ℕ) ==> ((k * zero) ∈ ℕ))) /\ ∀(n, (n ∈ ℕ) ==> (∀(k, (k ∈ ℕ) ==> ((k * n) ∈ ℕ)) ==> ∀(k, (k ∈ ℕ) ==> ((k * Succ(n)) ∈ ℕ))))).by(Tautology.from(baseAll, stepAll))
    val allAll = have(∀(n, (n ∈ ℕ) ==> ∀(k, (k ∈ ℕ) ==> ((k * n) ∈ ℕ)))).by(Tautology.from(indUnfolded, premiseAll))

    val mInℕ = assume(m ∈ ℕ)
    val nInℕ = assume(n ∈ ℕ)

    val nImp = have((n ∈ ℕ) ==> ∀(k, (k ∈ ℕ) ==> ((k * n) ∈ ℕ))).by(InstantiateForall(n)(allAll))
    val allK = have(∀(k, (k ∈ ℕ) ==> ((k * n) ∈ ℕ))).by(Tautology.from(nImp, nInℕ))

    val mImp = have((m ∈ ℕ) ==> ((m * n) ∈ ℕ)).by(InstantiateForall(m)(allK))
    val res = have((m * n) ∈ ℕ).by(Tautology.from(mImp, mInℕ))
    have(thesis).by(Restate.from(res))
  }

}
