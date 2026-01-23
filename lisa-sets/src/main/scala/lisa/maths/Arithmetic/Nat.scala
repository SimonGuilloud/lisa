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
    val exInd = have(∃(i, inductive(i)) ).by(Restate.from(lisa.maths.SetTheory.SetTheory.inductiveSetExists))
    val epsInd = have(∃(i, inductive(i)) |- inductive(ε(i, inductive(i)))) by Restate.from(
      Quantifiers.existsEpsilon of (x := i, P := λ(i, inductive(i)))
    )
    have(thesis) by Cut(exInd, epsInd)
  }

  /** The set of natural numbers (von Neumann naturals): the elements of `I` that belong to every inductive set. */
  val ℕ: Expr[Ind] = { n ∈ I | ∀(i, inductive(i) ==> (n ∈ i)) }

  /** Zero (von Neumann encoding). */
  val zero: Expr[Ind] = ∅

  /** Successor (set-theoretic successor). */
  def S(x: Expr[Ind]): Expr[Ind] = successor(x)

  /** Membership characterization of successor: `u ∈ S(v) <=> u ∈ v ∨ u = v`. */
  val succMembership = Theorem(
    (k ∈ S(n)) <=> (k ∈ n) \/ (k === n)
  ) {
    have(k ∈ successor(n) <=> k ∈ (n ∪ Singleton.singleton(n))) by Congruence.from(successor.definition of (x := n))
    val mem1 = lastStep
    have(k ∈ (n ∪ Singleton.singleton(n)) <=> (k ∈ n) \/ (k ∈ Singleton.singleton(n))) by Tautology.from(
      Union.membership of (x := n, y := Singleton.singleton(n), z := k)
    )
    val mem2 = lastStep
    have(k ∈ Singleton.singleton(n) <=> (k === n)) by Tautology.from(Singleton.membership of (x := n, y := k))
    val mem3 = lastStep

    have(k ∈ successor(n) <=> (k ∈ n) \/ (k === n)) by Tautology.from(mem1, mem2, mem3)
    thenHave(thesis) by Restate
  }

  /** Theorem: `n ∈ S(n)`. */
  val nInSucc = Theorem(n ∈ S(n)) {
    have(n ∈ S(n) <=> (n ∈ n) \/ (n === n)) by Restate.from(succMembership of (k := n, n := n))
    val mem = lastStep
    val refl = have(n === n) by Restate
    have((n ∈ n) \/ (n === n)) by Tautology.from(refl)
    have(thesis) by Tautology.from(mem, lastStep)
  }

  /** Theorem: successor is injective, i.e. `S(m) = S(n) <=> m = n`. */
  val succInjective = Theorem(
    (S(m) === S(n)) <=> (m === n)
  ) {
    val `==>` = have(S(m) === S(n) |- m === n) subproof {
      assume(S(m) === S(n))

      val mInSm = have(m ∈ S(m)) by Weakening(nInSucc of (n := m))
      val mInSn = have(m ∈ S(n)) by Congruence.from(mInSm)
      val mCase = have(m ∈ n \/ (m === n)) by Tautology.from(
        succMembership of (k := m, n := n),
        mInSn
      )

      val nInSn = have(n ∈ S(n)) by Weakening(nInSucc of (n := n))
      val nInSm = have(n ∈ S(m)) by Congruence.from(nInSn)
      val nCase = have(n ∈ m \/ (n === m)) by Tautology.from(
        succMembership of (k := n, n := m),
        nInSm
      )

      // Flip the equality disjunct in `nCase` to `m === n`.
      val eqSymm = have(n === m |- m === n) by Congruence
      val nCase2 = have(n ∈ m \/ (m === n)) by Tautology.from(nCase, eqSymm)

      val asym = have(S(m) === S(n) |- ¬((m ∈ n) /\ (n ∈ m))) by Weakening(
        FoundationAxiom.membershipAsymmetric of (x := m, y := n)
      )

      have(S(m) === S(n) |- m === n) by Tableau.from(mCase, nCase2, asym)
    }

    val `<==` = have(m === n |- S(m) === S(n)) by Congruence

    have(thesis) by Tautology.from(`==>`, `<==`)
  }

  /** Numeral `1` as `S(0)`. */
  val one: Expr[Ind] = S(zero)

  /** Numeral `2` as `S(1)`. */
  val two: Expr[Ind] = S(one)

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
                    ∃(k, (k ∈ ℕ) /\ (x === S(k)) /\ (y === S(app(h)(k))))
                )
              )
            )
          )(ℕ)(memRel)
        )(n)
      )
    )
  )

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
                    ∃(k, (k ∈ ℕ) /\ (x === S(k)) /\ (y === add(app(h)(k))(m)))
                )
              )
            )
          )(ℕ)(memRel)
        )(n)
      )
    )
  )

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
    val memℕ = have(zero ∈ ℕ <=> (zero ∈ I /\ ∀(i, inductive(i) ==> (zero ∈ i)))) by Comprehension.apply

    val indIff = have(inductive(I) <=> ((zero ∈ I) /\ ∀(n, (n ∈ I) ==> (S(n) ∈ I)))) by Restate.from(inductive.definition of (x := I))
    val indI0 = have(inductive(I) ==> (zero ∈ I)) by Tautology.from(indIff)
    val zeroInI = have(zero ∈ I) by Tautology.from(IInductive, indI0)

    val indiIff = have(inductive(i) <=> ((∅ ∈ i) /\ ∀(n, (n ∈ i) ==> (successor(n) ∈ i)))) by Restate.from(inductive.definition of (x := i))
    have(inductive(i) ==> (zero ∈ i)) by Tautology.from(indiIff)
    val all0 = thenHave(∀(i, inductive(i) ==> (zero ∈ i))) by RightForall

    val rhs = have(zero ∈ I /\ ∀(i, inductive(i) ==> (zero ∈ i))) by Tautology.from(zeroInI, all0)
    have(thesis) by Tautology.from(memℕ, rhs)
  }

  /** Theorem: `ℕ` is inductive. */
  val ℕInductive = Theorem(inductive(ℕ)) {
    val indDef = have(inductive(ℕ) <=> ((∅ ∈ ℕ) /\ ∀(n, (n ∈ ℕ) ==> (successor(n) ∈ ℕ)))) by Restate.from(inductive.definition of (x := ℕ))

    val zeroMem = have(∅ ∈ ℕ) by Restate.from(zeroInℕ)

    val memN = have(n ∈ ℕ <=> (n ∈ I /\ ∀(i, inductive(i) ==> (n ∈ i)))) by Comprehension.apply
    val memSN = have(successor(n) ∈ ℕ <=> (successor(n) ∈ I /\ ∀(i, inductive(i) ==> (successor(n) ∈ i)))) by Comprehension.apply

    val indIff = have(inductive(I) <=> ((∅ ∈ I) /\ ∀(k, (k ∈ I) ==> (successor(k) ∈ I)))) by Restate.from(inductive.definition of (x := I))
    have(∀(k, (k ∈ I) ==> (successor(k) ∈ I))) by Tautology.from(indIff, IInductive)
    thenHave((n ∈ I) ==> (successor(n) ∈ I)) by InstantiateForall(n)
    val succInIFromInI = lastStep

    val nInI = have(n ∈ ℕ |- n ∈ I) by Tautology.from(memN)
    val succInI = have(n ∈ ℕ |- successor(n) ∈ I) by Tautology.from(nInI, succInIFromInI)

    have(n ∈ ℕ |- ∀(i, inductive(i) ==> (n ∈ i))) by Tautology.from(memN)
    thenHave(n ∈ ℕ |- (inductive(i) ==> (n ∈ i))) by InstantiateForall(i)
    val nInInd = lastStep

    val indiIff = have(inductive(i) <=> ((∅ ∈ i) /\ ∀(k, (k ∈ i) ==> (successor(k) ∈ i)))) by Restate.from(inductive.definition of (x := i))
    have(inductive(i) ==> ∀(k, (k ∈ i) ==> (successor(k) ∈ i))) by Tautology.from(indiIff)
    thenHave(inductive(i) |- ∀(k, (k ∈ i) ==> (successor(k) ∈ i))) by Tautology
    thenHave(inductive(i) |- (n ∈ i) ==> (successor(n) ∈ i)) by InstantiateForall(n)
    val stepInInd = lastStep

    have(n ∈ ℕ |- inductive(i) ==> (successor(n) ∈ i)) by Tautology.from(nInInd, stepInInd)
    thenHave(n ∈ ℕ |- ∀(i, inductive(i) ==> (successor(n) ∈ i))) by RightForall
    val allSuccInInd = lastStep

    val rhs = have(n ∈ ℕ |- successor(n) ∈ I /\ ∀(i, inductive(i) ==> (successor(n) ∈ i))) by Tautology.from(succInI, allSuccInInd)
    have(n ∈ ℕ |- successor(n) ∈ ℕ) by Tautology.from(memSN, rhs)
    thenHave((n ∈ ℕ) ==> (successor(n) ∈ ℕ)) by Tautology
    thenHave(∀(n, (n ∈ ℕ) ==> (successor(n) ∈ ℕ))) by RightForall
    val succAll = lastStep

    have((∅ ∈ ℕ) /\ ∀(n, (n ∈ ℕ) ==> (successor(n) ∈ ℕ))) by Tautology.from(zeroMem, succAll)
    have(thesis) by Tautology.from(indDef, lastStep)
  }

  /** Theorem: closure of successor on `ℕ` (corollary of `inductive(ℕ)`). */
  val succClosed = Theorem(∀(n, (n ∈ ℕ) ==> (S(n) ∈ ℕ))) {
    have(inductive(ℕ) <=> ((∅ ∈ ℕ) /\ ∀(n, (n ∈ ℕ) ==> (successor(n) ∈ ℕ)))) by Restate.from(inductive.definition of (x := ℕ))
    val closed = have(∀(n, (n ∈ ℕ) ==> (successor(n) ∈ ℕ))) by Tautology.from(lastStep, ℕInductive)
    have(thesis) by Restate.from(closed)
  }

  /** Theorem: `1 ∈ ℕ`. */
  val oneInℕ = Theorem(one ∈ ℕ) {
    have(∀(n, (n ∈ ℕ) ==> (S(n) ∈ ℕ))) by Restate.from(succClosed)
    thenHave((zero ∈ ℕ) ==> (S(zero) ∈ ℕ)) by InstantiateForall(zero)
    have(thesis) by Tautology.from(zeroInℕ, lastStep)
  }

  /** Theorem: `2 ∈ ℕ`. */
  val twoInℕ = Theorem(two ∈ ℕ) {
    have(∀(n, (n ∈ ℕ) ==> (S(n) ∈ ℕ))) by Restate.from(succClosed)
    thenHave((one ∈ ℕ) ==> (S(one) ∈ ℕ)) by InstantiateForall(one)
    have(thesis) by Tautology.from(oneInℕ, lastStep)
  }

  /**
   * Induction axiom (second-order over predicates).
   *
   * `P(0) ∧ (∀n. n ∈ ℕ → (P(n) → P(S(n)))) → (∀n. n ∈ ℕ → P(n))`
   */
  private val Pred = variable[Ind >>: Prop]
  private val KPred: Expr[Ind] = { n ∈ ℕ | Pred(n) }
  val induction = Theorem(
    (Pred(zero) /\ ∀(n, (n ∈ ℕ) ==> (Pred(n) ==> Pred(S(n))))) ==> ∀(n, (n ∈ ℕ) ==> Pred(n))
  ) {
    val H = Pred(zero) /\ ∀(n, (n ∈ ℕ) ==> (Pred(n) ==> Pred(S(n))))

    val hyp0 = have(H |- Pred(zero)) by Tautology
    val hypAllStep = have(H |- ∀(n, (n ∈ ℕ) ==> (Pred(n) ==> Pred(S(n))))) by Tautology

    val memK = have(n ∈ KPred <=> (n ∈ ℕ /\ Pred(n))) by Comprehension.apply
    val memℕ = have(n ∈ ℕ <=> (n ∈ I /\ ∀(i, inductive(i) ==> (n ∈ i)))) by Comprehension.apply

    // Base: 0 ∈ KPred
    val zeroMemℕ = have(H |- zero ∈ ℕ) by Tautology.from(zeroInℕ)
    val memK0 = have(zero ∈ KPred <=> (zero ∈ ℕ /\ Pred(zero))) by Comprehension.apply
    have(H |- zero ∈ ℕ /\ Pred(zero)) by Tautology.from(zeroMemℕ, hyp0)
    val zeroMemK = have(H |- zero ∈ KPred) by Tautology.from(memK0, lastStep)

    // Step: n ∈ KPred -> S(n) ∈ KPred
    have(∀(k, (k ∈ ℕ) ==> (S(k) ∈ ℕ))).by(Restate.from(succClosed))
    thenHave((n ∈ ℕ) ==> (S(n) ∈ ℕ)) by InstantiateForall(n)
    val succInℕFromInℕ = lastStep

    have(H |- ∀(n, (n ∈ ℕ) ==> (Pred(n) ==> Pred(S(n))))) by Restate.from(hypAllStep)
    thenHave(H |- (n ∈ ℕ) ==> (Pred(n) ==> Pred(S(n)))) by InstantiateForall(n)
    val predStep = lastStep

    have(H /\ (n ∈ KPred) |- n ∈ ℕ) by Tautology.from(memK)
    val nInℕ = lastStep
    have(H /\ (n ∈ KPred) |- Pred(n)) by Tautology.from(memK)
    val predN = lastStep
    val succInℕ = have(H /\ (n ∈ KPred) |- S(n) ∈ ℕ) by Tautology.from(nInℕ, succInℕFromInℕ)
    val predSucc = have(H /\ (n ∈ KPred) |- Pred(S(n))) by Tautology.from(nInℕ, predN, predStep)

    val memKS = have(S(n) ∈ KPred <=> (S(n) ∈ ℕ /\ Pred(S(n)))) by Comprehension.apply
    have(H /\ (n ∈ KPred) |- S(n) ∈ ℕ /\ Pred(S(n))) by Tautology.from(succInℕ, predSucc)
    have(H /\ (n ∈ KPred) |- S(n) ∈ KPred) by Tautology.from(memKS, lastStep)
    thenHave(H |- (n ∈ KPred) ==> (S(n) ∈ KPred)) by Tautology
    thenHave(H |- ∀(n, (n ∈ KPred) ==> (S(n) ∈ KPred))) by RightForall
    val allStepK = lastStep

    // KPred is inductive
    val indDefK = have(inductive(KPred) <=> ((∅ ∈ KPred) /\ ∀(n, (n ∈ KPred) ==> (successor(n) ∈ KPred)))) by Restate.from(inductive.definition of (x := KPred))
    val allStepKSucc = have(H |- ∀(n, (n ∈ KPred) ==> (successor(n) ∈ KPred))) by Restate.from(allStepK)
    val indK = have(H |- inductive(KPred)) by Tautology.from(indDefK, zeroMemK, allStepKSucc)

    // From definition of ℕ: n ∈ ℕ -> (inductive(KPred) -> n ∈ KPred)
    have(H /\ (n ∈ ℕ) |- ∀(i, inductive(i) ==> (n ∈ i))) by Tautology.from(memℕ)
    thenHave(H /\ (n ∈ ℕ) |- inductive(KPred) ==> (n ∈ KPred)) by InstantiateForall(KPred)
    val nInKFromInd = lastStep
    have(H /\ (n ∈ ℕ) |- inductive(KPred)) by Tautology.from(indK)
    val indKInCtx = lastStep
    val nInK = have(H /\ (n ∈ ℕ) |- n ∈ KPred) by Tautology.from(indKInCtx, nInKFromInd)

    // Hence Pred(n)
    have(H /\ (n ∈ ℕ) |- Pred(n)) by Tautology.from(memK, nInK)
    thenHave(H |- (n ∈ ℕ) ==> Pred(n)) by Tautology
    thenHave(H |- ∀(n, (n ∈ ℕ) ==> Pred(n))) by RightForall

    have(thesis) by Tautology.from(lastStep)
  }

  /** Lemma: `n ∈ ℕ` implies `0 ∈ S(n)`. */
  val `n ∈ ℕ -> 0 ∈ S(n)` = Lemma((n ∈ ℕ) |- (zero ∈ S(n))) {
    val P = λ(n, zero ∈ S(n))

    val base = have(P(zero)) by Tautology.from(succMembership of (n := zero, k := zero))

    val step = have(∀(n, (n ∈ ℕ) ==> (P(n) ==> P(S(n))))) subproof {
      have((n ∈ ℕ) |- (P(n) ==> P(S(n)))) subproof {
        assume(n ∈ ℕ)
        assume(P(n))

        val SnSub = have(S(n) ⊆ S(S(n))) by Congruence.from(
          Union.leftSubset of (x := S(n), y := Singleton.singleton(S(n))),
          successor.definition of (x := S(n))
        )
        have(zero ∈ S(S(n))) by Tautology.from(
          Subset.membership of (x := S(n), y := S(S(n)), z := zero),
          SnSub,
          have(zero ∈ S(n)) by Restate
        )
        have(P(S(n))) by Restate.from(lastStep)
        thenHave(P(n) ==> P(S(n))) by Tautology
        have(thesis) by Tautology.from(lastStep)
      }
      thenHave((n ∈ ℕ) ==> (P(n) ==> P(S(n)))) by Tautology
      thenHave(thesis) by RightForall
    }

    val premise = have(P(zero) /\ ∀(n, (n ∈ ℕ) ==> (P(n) ==> P(S(n))))) by Tautology.from(base, step)
    val all = have(∀(n, (n ∈ ℕ) ==> P(n))) by Tautology.from(induction of (Pred := P), premise)

    have((n ∈ ℕ) ==> P(n)) by InstantiateForall(n)(all)
    thenHave(thesis) by Tautology
  }

  /** Theorem (Isabelle/ZF `natE`-style): every natural is either `0` or a successor. */
  val natCases = Theorem(
    (n ∈ ℕ) |- (n === zero) \/ ∃(m, (m ∈ ℕ) /\ (n === S(m)))
  ) {
    val P = λ(n, (n === zero) \/ ∃(m, (m ∈ ℕ) /\ (n === S(m))))

    val base = have(P(zero)) by Tautology

    val step = have(∀(n, (n ∈ ℕ) ==> (P(n) ==> P(S(n)))) ) subproof {
      have((n ∈ ℕ) |- (P(n) ==> P(S(n)))) subproof {
        assume(n ∈ ℕ)
        assume(P(n))

        val nInℕ = have(n ∈ ℕ) by Restate
        val refl = have(S(n) === S(n)) by Restate
        val rhs = have((n ∈ ℕ) /\ (S(n) === S(n))) by Tautology.from(nInℕ, refl)
        val ex = have(∃(m, (m ∈ ℕ) /\ (S(n) === S(m)))) by RightExists(rhs)

        have(P(S(n))) by Tautology.from(ex)
        have(thesis) by Tautology.from(lastStep)
      }
      thenHave((n ∈ ℕ) ==> (P(n) ==> P(S(n)))) by Tautology
      thenHave(thesis) by RightForall
    }

    val premise = have(P(zero) /\ ∀(n, (n ∈ ℕ) ==> (P(n) ==> P(S(n))))) by Tautology.from(base, step)
    val all = have(∀(n, (n ∈ ℕ) ==> P(n))) by Tautology.from(induction of (Pred := P), premise)

    have((n ∈ ℕ) ==> P(n)) by InstantiateForall(n)(all)
    thenHave(thesis) by Tautology
  }

  /** Lemma: if `n ⊆ ℕ` and `n ∈ ℕ`, then `S(n) ⊆ ℕ`. */
  private val succSubsetℕ = Lemma((n ⊆ ℕ, n ∈ ℕ) |- S(n) ⊆ ℕ) {
    assume(n ⊆ ℕ)
    assume(n ∈ ℕ)

    val memSucc1 = have(k ∈ successor(n) <=> k ∈ (n ∪ Singleton.singleton(n))) by Congruence.from(successor.definition of (x := n))
    val memSucc2 = have(k ∈ (n ∪ Singleton.singleton(n)) <=> (k ∈ n) \/ (k ∈ Singleton.singleton(n))) by Tautology.from(
      Union.membership of (x := n, y := Singleton.singleton(n), z := k)
    )
    val memSucc = have(k ∈ successor(n) <=> (k ∈ n) \/ (k ∈ Singleton.singleton(n))) by Tautology.from(memSucc1, memSucc2)

    have(k ∈ Singleton.singleton(n) <=> (k === n)) by Tautology.from(Singleton.membership of (x := n, y := k))
    val memSing = lastStep

    have(k ∈ n ==> k ∈ ℕ) by Tautology.from(Subset.membership of (x := n, y := ℕ, z := k))
    val inFromSubset = lastStep

    val eqMem = have((k === n, n ∈ ℕ) |- k ∈ ℕ) by Congruence
    val inFromEqCtx = have(n ∈ ℕ |- (k === n ==> k ∈ ℕ)) by Tautology.from(eqMem)
    val nInℕ = have(n ∈ ℕ) by Restate
    val inFromEq = have(k === n ==> k ∈ ℕ) by Tautology.from(inFromEqCtx, nInℕ)
    have(k ∈ Singleton.singleton(n) ==> k ∈ ℕ) by Tautology.from(memSing, inFromEq)
    val inFromSingleton = lastStep

    have((k ∈ successor(n)) ==> (k ∈ ℕ)) by Tautology.from(memSucc, inFromSubset, inFromSingleton)
    thenHave(∀(k, (k ∈ successor(n)) ==> (k ∈ ℕ))) by RightForall
    val succSub = have(successor(n) ⊆ ℕ) by Tautology.from(Subset.definition of (x := successor(n), y := ℕ), lastStep)
    have(thesis) by Tautology.from(succSub)
  }

  /** Theorem: `ℕ` is a transitive set (i.e. $x ∈ y ∈ \mathbb{N} ⇒ x ∈ \mathbb{N}$). */
  val ℕTransitive = Theorem(TransitiveSet.transitiveSet(ℕ)) {
    val P = λ(n, n ⊆ ℕ)

    val base = have(P(zero)) by Restate.from(Subset.leftEmpty of (x := ℕ))

    val step = have(∀(n, (n ∈ ℕ) ==> (P(n) ==> P(S(n))))) subproof {
      have((n ∈ ℕ) |- (P(n) ==> P(S(n)))) subproof {
        assume(n ∈ ℕ)
        assume(P(n))
        have(S(n) ⊆ ℕ) by Tautology.from(succSubsetℕ)
        have(P(S(n))) by Tautology.from(lastStep)
        thenHave(P(n) ==> P(S(n))) by Tautology
        have(thesis) by Tautology.from(lastStep)
      }
      thenHave((n ∈ ℕ) ==> (P(n) ==> P(S(n)))) by Tautology
      thenHave(thesis) by RightForall
    }

    val premise = have(P(zero) /\ ∀(n, (n ∈ ℕ) ==> (P(n) ==> P(S(n))))) by Tautology.from(base, step)
    val ind = have(∀(n, (n ∈ ℕ) ==> P(n))) by Tautology.from(induction of (Pred := P), premise)

    have(thesis) by Tautology.from(TransitiveSet.alternativeDefinition of (A := ℕ), ind)
  }

  /** Lemma: if `n ∈ ℕ`, then `n ⊆ ℕ`. */
  val `n ∈ ℕ -> n ⊆ ℕ` = Lemma((n ∈ ℕ) |- n ⊆ ℕ) {
    assume(n ∈ ℕ)
    have(thesis) by Tautology.from(TransitiveSet.elementIsSubset.of(A := ℕ, x := n), ℕTransitive, lastStep)
  }

  /** Lemma: if `n ∈ ℕ` and `k ∈ n`, then `k ∈ ℕ`. */
  val `n ∈ ℕ, k ∈ n -> k ∈ ℕ` = Lemma((n ∈ ℕ, k ∈ n) |- k ∈ ℕ) {
    have((n ∈ ℕ) |- n ⊆ ℕ) by Restate.from(`n ∈ ℕ -> n ⊆ ℕ`)
    val nSub = lastStep
    have((n ⊆ ℕ, k ∈ n) |- k ∈ ℕ) by Tautology.from(Subset.membership.of(x := n, y := ℕ, z := k))
    have(thesis) by Tautology.from(nSub, lastStep)
  }

  /** For von Neumann naturals: if `n ∈ ℕ` then the `∈_ℕ`-initial segment below `n` is exactly `n`. */
  val natInitialSegment = Theorem(
    (n ∈ ℕ) |- InitialSegment.initialSegment(n)(ℕ)(memRel) === n
  ) {
    assume(n ∈ ℕ)

    val nSubℕ = have(n ⊆ ℕ).by(Tautology.from(TransitiveSet.elementIsSubset.of(A := ℕ, x := n), ℕTransitive, lastStep))

    have(k ∈ InitialSegment.initialSegment(n)(ℕ)(memRel) <=> (k ∈ ℕ) /\ ((k, n) ∈ memRel)).by(Tautology.from(
      InitialSegment.membership.of(y := k, x := n, A := ℕ, < := memRel)
    ))
    val memInit = lastStep

    have((k, n) ∈ memRel <=> (k ∈ ℕ) /\ (n ∈ ℕ) /\ (k ∈ n)).by(Tautology.from(
      MembershipRelation.membership.of(x := k, y := n, A := ℕ)
    ))
    val memRelMem = lastStep

    val initToMem = have(k ∈ InitialSegment.initialSegment(n)(ℕ)(memRel) ==> k ∈ n).by(Tautology.from(memInit, memRelMem))

    val memToInit = have(k ∈ n ==> k ∈ InitialSegment.initialSegment(n)(ℕ)(memRel)).by(Tautology.from(
      memInit,
      memRelMem,
      Subset.membership.of(x := n, y := ℕ, z := k),
      nSubℕ,
      assume(n ∈ ℕ)
    ))

    have(k ∈ InitialSegment.initialSegment(n)(ℕ)(memRel) <=> k ∈ n).by(Tautology.from(initToMem, memToInit))
    thenHave(thesis).by(Extensionality)
  }

  /** Theorem: every element of `ℕ` is a transitive set (i.e. $n ∈ \mathbb{N} ⇒ transitiveSet(n)$). */
  val natElementsTransitive = Theorem(
    (n ∈ ℕ) |- TransitiveSet.transitiveSet(n)
  ) {
    val P = λ(n, TransitiveSet.transitiveSet(n))

    val base = have(P(zero)).by(Restate.from(TransitiveSet.emptySet))

    val step = have(∀(n, (n ∈ ℕ) ==> (P(n) ==> P(S(n))))) subproof {
      have((n ∈ ℕ) |- (P(n) ==> P(S(n)))) subproof {
        assume(n ∈ ℕ)
        assume(P(n))
        val Pn = have(P(n)) by Restate

        // transitiveSet(n) gives: ∀k. k ∈ n ==> k ⊆ n
        val nAlt = have(∀(k, k ∈ n ==> k ⊆ n)).by(Tautology.from(
          TransitiveSet.alternativeDefinition of (A := n),
          Pn
        ))

        // n ⊆ S(n)
        val nSubSucc = have(n ⊆ S(n)) subproof {
          val memSucc = have(k ∈ S(n) <=> k ∈ (n ∪ Singleton.singleton(n))) by Congruence.from(successor.definition of (x := n))
          val memUnion = have(k ∈ (n ∪ Singleton.singleton(n)) <=> (k ∈ n) \/ (k ∈ Singleton.singleton(n))) by Tautology.from(
            Union.membership of (x := n, y := Singleton.singleton(n), z := k)
          )

          have(k ∈ n |- (k ∈ n) \/ (k ∈ Singleton.singleton(n))) by Tautology
          have(k ∈ n |- k ∈ (n ∪ Singleton.singleton(n))) by Tautology.from(memUnion, lastStep)
          have(k ∈ n |- k ∈ S(n)) by Tautology.from(memSucc, lastStep)
          thenHave(k ∈ n ==> k ∈ S(n)) by Restate
          thenHave(∀(k, k ∈ n ==> k ∈ S(n))) by RightForall
          have(thesis) by Tautology.from(Subset.definition of (x := n, y := S(n)), lastStep)
        }

        // Show: ∀k. k ∈ S(n) ==> k ⊆ S(n)
        have(k ∈ S(n) ==> k ⊆ S(n)) subproof {
          assume(k ∈ S(n))

          have(k ∈ S(n) <=> k ∈ (n ∪ Singleton.singleton(n))) by Congruence.from(successor.definition of (x := n))
          val mem1 = lastStep
          have(k ∈ (n ∪ Singleton.singleton(n)) <=> (k ∈ n) \/ (k ∈ Singleton.singleton(n))) by Tautology.from(
            Union.membership of (x := n, y := Singleton.singleton(n), z := k)
          )
          val mem2 = lastStep
          val memSucc = have(k ∈ S(n) <=> (k ∈ n) \/ (k ∈ Singleton.singleton(n))) by Tautology.from(mem1, mem2)

          val caseIn = have(k ∈ n ==> k ⊆ S(n)) subproof {
            assume(k ∈ n)
            val kInN = have(k ∈ n) by Restate
            have(k ∈ n ==> k ⊆ n) by InstantiateForall(k)(nAlt)
            val kSubN = have(k ⊆ n) by Tautology.from(kInN, lastStep)

            have(k ⊆ S(n)) by Tautology.from(
              kSubN,
              nSubSucc,
              Subset.transitivity of (x := k, y := n, z := S(n))
            )
            have(thesis) by Tautology.from(lastStep)
          }

          val memSing = have(k ∈ Singleton.singleton(n) <=> (k === n)) by Tautology.from(Singleton.membership of (x := n, y := k))

          val caseEq = have(k ∈ Singleton.singleton(n) ==> k ⊆ S(n)) subproof {
            assume(k ∈ Singleton.singleton(n))
            val kInSing = have(k ∈ Singleton.singleton(n)) by Restate
            val kEqN = have(k === n) by Tautology.from(memSing, kInSing)
            val eqSub = have((k === n, n ⊆ S(n)) |- k ⊆ S(n)) by Congruence
            have(k ⊆ S(n)) by Tautology.from(kEqN, nSubSucc, eqSub)
            have(thesis) by Tautology.from(lastStep)
          }

          have(thesis) by Tautology.from(memSucc, caseIn, caseEq)
        }
        thenHave(∀(k, k ∈ S(n) ==> k ⊆ S(n))) by RightForall

        val PSn = have(P(S(n))) by Tautology.from(TransitiveSet.alternativeDefinition of (A := S(n)), lastStep)
        have(thesis) by Tautology.from(PSn)
      }
      thenHave((n ∈ ℕ) ==> (P(n) ==> P(S(n)))) by Tautology
      thenHave(thesis) by RightForall
    }

    val premise = have(P(zero) /\ ∀(n, (n ∈ ℕ) ==> (P(n) ==> P(S(n))))).by(Tautology.from(base, step))
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
        assume(A ⊆ ℕ)
        val ASubNat = have(A ⊆ ℕ) by Restate

        have(A ≠ ∅ |- ∃(m, Extrema.minimal(m)(A)(memRel))) subproof {
          assume(A ≠ ∅)
          val ANonEmpty = have(A ≠ ∅) by Restate

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
              assume(k ∈ A)
              val kInA = have(k ∈ A) by Restate

              have(∀(k, k ∈ A ==> k ∉ m)) by Restate.from(allNotIn)
              thenHave(k ∈ A ==> k ∉ m) by InstantiateForall(k)
              val kNotInM = have(k ∉ m) by Tautology.from(kInA, lastStep)

              have((k, m) ∈ memRel |- k ∈ m) by Tautology.from(MembershipRelation.membership of (x := k, y := m, A := ℕ))
              val relImpliesMem = lastStep

              have((k, m) ∈ memRel |- ()) by Tautology.from(kNotInM, relImpliesMem)
              thenHave(¬((k, m) ∈ memRel)) by RightNot
              have(thesis) by Weakening(lastStep)
            }
            thenHave(k ∈ A ==> ¬((k, m) ∈ memRel)) by Tautology
            thenHave(∀(k, k ∈ A ==> ¬((k, m) ∈ memRel))) by RightForall

            val rhs = have(m ∈ A /\ ∀(k, k ∈ A ==> ¬((k, m) ∈ memRel))) by Tautology.from(mInA, lastStep)
            have(Extrema.minimal(m)(A)(memRel)) by Tautology.from(Extrema.minimal.definition of (A := A, a := m, < := memRel), rhs)
            have(thesis) by Weakening(lastStep)
          }

          thenHave((m ∈ A) /\ ∀(k, k ∈ A ==> k ∉ m) |- ∃(m, Extrema.minimal(m)(A)(memRel))) by RightExists
          thenHave(∃(m, (m ∈ A) /\ ∀(k, k ∈ A ==> k ∉ m)) |- ∃(m, Extrema.minimal(m)(A)(memRel))) by LeftExists
          have(thesis) by Cut(foundationInstance, lastStep)
        }

        thenHave((A ≠ ∅) ==> ∃(m, Extrema.minimal(m)(A)(memRel))) by Tautology
        have(thesis) by Tautology.from(lastStep)
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

  /** Lemma: successor is never empty, hence `S(n) ≠ 0`. */
  private val succNeZero = Lemma((n ∈ ℕ) |- (S(n) =/= zero)) {
    assume(n ∈ ℕ)
    val nInSn = have(n ∈ S(n)).by(Weakening(nInSucc))
    have(S(n) === zero |- ()) subproof {
      assume(S(n) === zero)
      have(n ∈ zero) by Congruence.from(nInSn, lastStep)
      have(thesis) by Tautology.from(EmptySet.definition.of(x := n), lastStep)
    }
    thenHave(thesis) by Restate
  }

  /**
   * Lemma (successor step): if `k ∈ n` and `n ∈ ℕ` then `S(k) ∈ n` or `S(k) = n`.
   * This is the key inductive property used to show linearity of `∈` on naturals.
   */
  private val succStepInNat = Theorem(
    (k ∈ n, n ∈ ℕ) |- (S(k) ∈ n) \/ (S(k) === n)
  ) {
    // Prove by induction on n the predicate: ∀k. k ∈ n ==> (S(k) ∈ n) \/ (S(k) = n)
    val P = λ(n, ∀(k, k ∈ n ==> ((S(k) ∈ n) \/ (S(k) === n))))

    val base = have(P(zero)) subproof {
      have(k ∈ zero |- (S(k) ∈ zero) \/ (S(k) === zero)) subproof {
        assume(k ∈ zero)
        have(thesis) by Tautology.from(EmptySet.definition.of(x := k), lastStep)
      }
      thenHave(k ∈ zero ==> ((S(k) ∈ zero) \/ (S(k) === zero))) by Restate
      thenHave(∀(k, k ∈ zero ==> ((S(k) ∈ zero) \/ (S(k) === zero)))) by RightForall
      have(thesis) by Restate.from(lastStep)
    }

    val step = have(∀(n, (n ∈ ℕ) ==> (P(n) ==> P(S(n))))) subproof {
      have((n ∈ ℕ) |- (P(n) ==> P(S(n)))) subproof {
        assume(n ∈ ℕ)
        val nInℕ = have(n ∈ ℕ) by Restate
        assume(P(n))
        val Pn = have(P(n)) by Restate

        have(∀(k, k ∈ S(n) ==> ((S(k) ∈ S(n)) \/ (S(k) === S(n))))) subproof {
          have(k ∈ S(n) |- (S(k) ∈ S(n)) \/ (S(k) === S(n))) subproof {
            assume(k ∈ S(n))
            val kInSn = have(k ∈ S(n)) by Restate

            val kCases = have((k ∈ n) \/ (k === n)) by Tautology.from(succMembership.of(n := n, k := k), kInSn)

            val caseEq = have(k === n |- (S(k) ∈ S(n)) \/ (S(k) === S(n))) subproof {
              assume(k === n)
              have(S(k) === S(n)) by Congruence
              have(thesis) by Tautology.from(lastStep)
            }

            val caseIn = have(k ∈ n |- (S(k) ∈ S(n)) \/ (S(k) === S(n))) subproof {
              assume(k ∈ n)
              val kInN = have(k ∈ n) by Restate

              have(∀(k, k ∈ n ==> ((S(k) ∈ n) \/ (S(k) === n)))) by Restate.from(Pn)
              thenHave(k ∈ n ==> ((S(k) ∈ n) \/ (S(k) === n))) by InstantiateForall(k)
              val SkInNorEq = have((S(k) ∈ n) \/ (S(k) === n)) by Tautology.from(kInN, lastStep)

              val fromIn = have(S(k) ∈ n |- (S(k) ∈ S(n)) \/ (S(k) === S(n))) subproof {
                assume(S(k) ∈ n)
                val SkInN = have(S(k) ∈ n) by Restate
                // If S(k) ∈ n then S(k) ∈ S(n).
                have(S(k) ∈ S(n)) by Tautology.from(succMembership.of(n := n, k := S(k)), SkInN)
                have(thesis) by Tautology.from(lastStep)
              }

              val fromEq = have(S(k) === n |- (S(k) ∈ S(n)) \/ (S(k) === S(n))) subproof {
                assume(S(k) === n)
                // Since n ∈ S(n), by congruence we get S(k) ∈ S(n).
                val nInSn = have(n ∈ S(n)).by(Weakening(nInSucc))
                have(S(k) ∈ S(n)) by Congruence.from(nInSn, lastStep)
                have(thesis) by Tautology.from(lastStep)
              }

              val C = (S(k) ∈ S(n)) \/ (S(k) === S(n))

              val fromInImp = have((S(k) ∈ n) ==> C) subproof {
                have(S(k) ∈ n |- C) subproof {
                  val SkInN = assume(S(k) ∈ n)
                  have(C) by Tautology.from(fromIn, SkInN)
                }
                thenHave(thesis) by Restate
              }

              val fromEqImp = have((S(k) === n) ==> C) subproof {
                have(S(k) === n |- C) subproof {
                  val SkEqN = assume(S(k) === n)
                  have(C) by Tautology.from(fromEq, SkEqN)
                }
                thenHave(thesis) by Restate
              }

              have(thesis).by(Tautology.from(SkInNorEq, fromInImp, fromEqImp))
            }

            val C2 = (S(k) ∈ S(n)) \/ (S(k) === S(n))

            val caseInImp = have((k ∈ n) ==> C2) subproof {
              have(k ∈ n |- C2) subproof {
                val kInN2 = assume(k ∈ n)
                have(C2) by Tautology.from(caseIn, kInN2)
              }
              thenHave(thesis) by Restate
            }

            val caseEqImp = have((k === n) ==> C2) subproof {
              have(k === n |- C2) subproof {
                val kEqN2 = assume(k === n)
                have(C2) by Tautology.from(caseEq, kEqN2)
              }
              thenHave(thesis) by Restate
            }

            have(thesis).by(Tautology.from(kCases, caseInImp, caseEqImp))
          }
          thenHave(k ∈ S(n) ==> ((S(k) ∈ S(n)) \/ (S(k) === S(n)))) by Restate
          thenHave(∀(k, k ∈ S(n) ==> ((S(k) ∈ S(n)) \/ (S(k) === S(n))))) by RightForall
          have(thesis) by Restate.from(lastStep)
        }

        have(P(S(n))) by Restate.from(lastStep)
        thenHave(P(n) ==> P(S(n))) by Tautology
        have(thesis) by Tautology.from(lastStep)
      }
      thenHave((n ∈ ℕ) ==> (P(n) ==> P(S(n)))) by Tautology
      thenHave(thesis) by RightForall
    }

    val premise = have(P(zero) /\ ∀(n, (n ∈ ℕ) ==> (P(n) ==> P(S(n))))) by Tautology.from(base, step)
    val all = have(∀(n, (n ∈ ℕ) ==> P(n))) by Tautology.from(induction.of(Pred := P), premise)

    // Use the proved ∀n∈ℕ. P(n) at our specific n.
    assume(n ∈ ℕ)
    have((n ∈ ℕ) ==> P(n)) by InstantiateForall(n)(all)
    val Pn = have(P(n)) by Tautology.from(lastStep, have(n ∈ ℕ) by Restate)

    // Now instantiate P(n) at k and apply k ∈ n.
    have(∀(k, k ∈ n ==> ((S(k) ∈ n) \/ (S(k) === n)))) by Restate.from(Pn)
    thenHave(k ∈ n ==> ((S(k) ∈ n) \/ (S(k) === n))) by InstantiateForall(k)
    val imp = lastStep
    val kInN2 = assume(k ∈ n)
    have(thesis) by Tautology.from(imp, kInN2)
  }

  /** Lemma: if `k ∈ n` and `n ∈ ℕ`, then `S(k) ∈ S(n)`. */
  private val succMemMonotone = Lemma((k ∈ n, n ∈ ℕ) |- S(k) ∈ S(n)) {
    assume(k ∈ n)
    assume(n ∈ ℕ)
    val kInN = have(k ∈ n) by Restate
    val nInℕ = have(n ∈ ℕ) by Restate

    val stepOrEq = have((S(k) ∈ n) \/ (S(k) === n)) by Tautology.from(succStepInNat, kInN, nInℕ)

    val fromIn = have(S(k) ∈ n |- S(k) ∈ S(n)) subproof {
      assume(S(k) ∈ n)
      have(S(k) ∈ S(n)) by Tautology.from(succMembership.of(n := n, k := S(k)), have(S(k) ∈ n) by Restate)
      have(thesis).by(Restate.from(lastStep))
    }
    val fromEq = have(S(k) === n |- S(k) ∈ S(n)) subproof {
      assume(S(k) === n)
      val nInSn = have(n ∈ S(n)).by(Weakening(nInSucc))
      have(S(k) ∈ S(n)) by Congruence.from(nInSn, lastStep)
      have(thesis).by(Restate.from(lastStep))
    }

    val fromInImp = have((S(k) ∈ n) ==> (S(k) ∈ S(n))) subproof {
      have(S(k) ∈ n |- S(k) ∈ S(n)) subproof {
        val SkInN = assume(S(k) ∈ n)
        have(S(k) ∈ S(n)) by Tautology.from(fromIn, SkInN)
      }
      thenHave(thesis) by Restate
    }

    val fromEqImp = have((S(k) === n) ==> (S(k) ∈ S(n))) subproof {
      have(S(k) === n |- S(k) ∈ S(n)) subproof {
        val SkEqN = assume(S(k) === n)
        have(S(k) ∈ S(n)) by Tautology.from(fromEq, SkEqN)
      }
      thenHave(thesis) by Restate
    }

    have(thesis) by Tautology.from(stepOrEq, fromInImp, fromEqImp)
  }

  /** Theorem: any two naturals are comparable by membership (trichotomy on `∈`). */
  private val natComparability = Theorem(
    (m ∈ ℕ, n ∈ ℕ) |- (m === n) \/ (m ∈ n) \/ (n ∈ m)
  ) {
    // Induction on n with predicate: ∀m∈ℕ, m = n \/ m ∈ n \/ n ∈ m
    val Q = λ(n, ∀(m, (m ∈ ℕ) ==> ((m === n) \/ (m ∈ n) \/ (n ∈ m))))

    val base = have(Q(zero)) subproof {
      have((m ∈ ℕ) |- (m === zero) \/ (m ∈ zero) \/ (zero ∈ m)) subproof {
        assume(m ∈ ℕ)
        val mInℕ = have(m ∈ ℕ) by Restate
        val mCases = have((m === zero) \/ ∃(k, (k ∈ ℕ) /\ (m === S(k)))) by Tautology.from(natCases.of(n := m), mInℕ)

        val caseZero = have(m === zero |- (m === zero) \/ (m ∈ zero) \/ (zero ∈ m)) by Tautology

        val caseSucc = have(∃(k, (k ∈ ℕ) /\ (m === S(k))) |- (m === zero) \/ (m ∈ zero) \/ (zero ∈ m)) subproof {
          assume(∃(k, (k ∈ ℕ) /\ (m === S(k))))
          have((k ∈ ℕ) /\ (m === S(k)) |- (m === zero) \/ (m ∈ zero) \/ (zero ∈ m)) subproof {
            assume((k ∈ ℕ) /\ (m === S(k)))
            val kInℕ = have(k ∈ ℕ) by Tautology
            val mEqSk = have(m === S(k)) by Tautology

            val zeroInSk = have(zero ∈ S(k)) by Tautology.from(`n ∈ ℕ -> 0 ∈ S(n)`.of(n := k), kInℕ)
            have(zero ∈ m) by Congruence.from(zeroInSk, mEqSk)
            have(thesis) by Tautology.from(lastStep)
          }
          thenHave(∃(k, (k ∈ ℕ) /\ (m === S(k))) |- (m === zero) \/ (m ∈ zero) \/ (zero ∈ m)) by LeftExists
          have(thesis) by Restate.from(lastStep)
        }

        val goal = (m === zero) \/ (m ∈ zero) \/ (zero ∈ m)

        val caseZeroImp = have((m === zero) ==> goal) subproof {
          have(m === zero |- goal) subproof {
            val mEq0 = assume(m === zero)
            have(goal) by Tautology.from(caseZero, mEq0)
          }
          thenHave(thesis) by Restate
        }

        val caseSuccImp = have(∃(k, (k ∈ ℕ) /\ (m === S(k))) ==> goal) subproof {
          have(∃(k, (k ∈ ℕ) /\ (m === S(k))) |- goal) subproof {
            val mIsSucc = assume(∃(k, (k ∈ ℕ) /\ (m === S(k))))
            have(goal) by Tautology.from(caseSucc, mIsSucc)
          }
          thenHave(thesis) by Restate
        }

        have(thesis) by Tautology.from(mCases, caseZeroImp, caseSuccImp)
      }
      thenHave((m ∈ ℕ) ==> ((m === zero) \/ (m ∈ zero) \/ (zero ∈ m))) by Restate
      thenHave(∀(m, (m ∈ ℕ) ==> ((m === zero) \/ (m ∈ zero) \/ (zero ∈ m)))) by RightForall
      have(thesis) by Restate.from(lastStep)
    }

    val step = have(∀(n, (n ∈ ℕ) ==> (Q(n) ==> Q(S(n))))) subproof {
      have((n ∈ ℕ) |- (Q(n) ==> Q(S(n)))) subproof {
        assume(n ∈ ℕ)
        val nInℕ = have(n ∈ ℕ) by Restate
        assume(Q(n))
        val Qn = have(Q(n)) by Restate

        have((m ∈ ℕ) |- (m === S(n)) \/ (m ∈ S(n)) \/ (S(n) ∈ m)) subproof {
          assume(m ∈ ℕ)
          val mInℕ = have(m ∈ ℕ) by Restate

          val mCases = have((m === zero) \/ ∃(k, (k ∈ ℕ) /\ (m === S(k)))) by Tautology.from(natCases.of(n := m), mInℕ)

          val caseZero = have(m === zero |- (m === S(n)) \/ (m ∈ S(n)) \/ (S(n) ∈ m)) subproof {
            assume(m === zero)
            // 0 ∈ S(n)
            val zeroInSn = have(zero ∈ S(n)) by Tautology.from(`n ∈ ℕ -> 0 ∈ S(n)`.of(n := n), nInℕ)
            have(m ∈ S(n)) by Congruence.from(zeroInSn, lastStep)
            have(thesis) by Tautology.from(lastStep)
          }

          val caseSucc = have(∃(k, (k ∈ ℕ) /\ (m === S(k))) |- (m === S(n)) \/ (m ∈ S(n)) \/ (S(n) ∈ m)) subproof {
            assume(∃(k, (k ∈ ℕ) /\ (m === S(k))))

            have((k ∈ ℕ) /\ (m === S(k)) |- (m === S(n)) \/ (m ∈ S(n)) \/ (S(n) ∈ m)) subproof {
              assume((k ∈ ℕ) /\ (m === S(k)))
              val kInℕ = have(k ∈ ℕ) by Tautology
              val mEqSk = have(m === S(k)) by Tautology

              // Compare k and n using Q(n)
              have(∀(m, (m ∈ ℕ) ==> ((m === n) \/ (m ∈ n) \/ (n ∈ m)))) by Restate.from(Qn)
              thenHave((k ∈ ℕ) ==> ((k === n) \/ (k ∈ n) \/ (n ∈ k))) by InstantiateForall(k)
              val cmp = have((k === n) \/ (k ∈ n) \/ (n ∈ k)) by Tautology.from(kInℕ, lastStep)

              val eqCase = have(k === n |- (m === S(n)) \/ (m ∈ S(n)) \/ (S(n) ∈ m)) subproof {
                assume(k === n)
                have(S(k) === S(n)) by Congruence
                have(m === S(n)) by Congruence.from(mEqSk, lastStep)
                have(thesis) by Tautology.from(lastStep)
              }

              val ltCase = have(k ∈ n |- (m === S(n)) \/ (m ∈ S(n)) \/ (S(n) ∈ m)) subproof {
                assume(k ∈ n)
                val SkInSn = have(S(k) ∈ S(n)) by Tautology.from(succMemMonotone.of(k := k, n := n), have(k ∈ n) by Restate, nInℕ)
                have(m ∈ S(n)) by Congruence.from(SkInSn, mEqSk)
                have(thesis) by Tautology.from(lastStep)
              }

              val gtCase = have(n ∈ k |- (m === S(n)) \/ (m ∈ S(n)) \/ (S(n) ∈ m)) subproof {
                assume(n ∈ k)
                val SnInSk = have(S(n) ∈ S(k)) by Tautology.from(succMemMonotone.of(k := n, n := k), have(n ∈ k) by Restate, kInℕ)
                have(S(n) ∈ m) by Congruence.from(SnInSk, mEqSk)
                have(thesis) by Tautology.from(lastStep)
              }

              val goal = (m === S(n)) \/ (m ∈ S(n)) \/ (S(n) ∈ m)

              val eqImp = have((k === n) ==> goal) subproof {
                have(k === n |- goal) subproof {
                  val kEqN2 = assume(k === n)
                  have(goal) by Tautology.from(eqCase, kEqN2)
                }
                thenHave(thesis) by Restate
              }

              val ltImp = have((k ∈ n) ==> goal) subproof {
                have(k ∈ n |- goal) subproof {
                  val kInN2 = assume(k ∈ n)
                  have(goal) by Tautology.from(ltCase, kInN2)
                }
                thenHave(thesis) by Restate
              }

              val gtImp = have((n ∈ k) ==> goal) subproof {
                have(n ∈ k |- goal) subproof {
                  val nInK2 = assume(n ∈ k)
                  have(goal) by Tautology.from(gtCase, nInK2)
                }
                thenHave(thesis) by Restate
              }

              have(thesis) by Tautology.from(cmp, eqImp, ltImp, gtImp)
            }

            thenHave(∃(k, (k ∈ ℕ) /\ (m === S(k))) |- (m === S(n)) \/ (m ∈ S(n)) \/ (S(n) ∈ m)) by LeftExists
            have(thesis) by Restate.from(lastStep)
          }

          val goal2 = (m === S(n)) \/ (m ∈ S(n)) \/ (S(n) ∈ m)

          val caseZeroImp = have((m === zero) ==> goal2) subproof {
            have(m === zero |- goal2) subproof {
              val mEq0 = assume(m === zero)
              have(goal2) by Tautology.from(caseZero, mEq0)
            }
            thenHave(thesis) by Restate
          }

          val caseSuccImp = have(∃(k, (k ∈ ℕ) /\ (m === S(k))) ==> goal2) subproof {
            have(∃(k, (k ∈ ℕ) /\ (m === S(k))) |- goal2) subproof {
              val mIsSucc = assume(∃(k, (k ∈ ℕ) /\ (m === S(k))))
              have(goal2) by Tautology.from(caseSucc, mIsSucc)
            }
            thenHave(thesis) by Restate
          }

          have(thesis) by Tautology.from(mCases, caseZeroImp, caseSuccImp)
        }

        thenHave((m ∈ ℕ) ==> ((m === S(n)) \/ (m ∈ S(n)) \/ (S(n) ∈ m))) by Restate
        thenHave(∀(m, (m ∈ ℕ) ==> ((m === S(n)) \/ (m ∈ S(n)) \/ (S(n) ∈ m)))) by RightForall
        have(Q(S(n))) by Restate.from(lastStep)
        thenHave(Q(n) ==> Q(S(n))) by Tautology
        have(thesis) by Tautology.from(lastStep)
      }
      thenHave((n ∈ ℕ) ==> (Q(n) ==> Q(S(n)))) by Tautology
      thenHave(thesis) by RightForall
    }

    val premise = have(Q(zero) /\ ∀(n, (n ∈ ℕ) ==> (Q(n) ==> Q(S(n))))) by Tautology.from(base, step)
    val all = have(∀(n, (n ∈ ℕ) ==> Q(n))) by Tautology.from(induction.of(Pred := Q), premise)

    // Instantiate at our n, then at m.
    assume(n ∈ ℕ)
    have((n ∈ ℕ) ==> Q(n)) by InstantiateForall(n)(all)
    val Qn = have(Q(n)) by Tautology.from(lastStep, have(n ∈ ℕ) by Restate)

    have(∀(m, (m ∈ ℕ) ==> ((m === n) \/ (m ∈ n) \/ (n ∈ m)))) by Restate.from(Qn)
    thenHave((m ∈ ℕ) ==> ((m === n) \/ (m ∈ n) \/ (n ∈ m))) by InstantiateForall(m)
    val imp = lastStep
    val mInℕ2 = assume(m ∈ ℕ)
    have((m === n) \/ (m ∈ n) \/ (n ∈ m)) by Tautology.from(imp, mInℕ2)
    have(thesis) by Restate.from(lastStep)
  }

  /** Theorem: `∈_ℕ` is total on `ℕ`. */
  private val natMemRelTotal = Theorem(
    total(memRel)(ℕ)
  ) {
    have((m ∈ ℕ, n ∈ ℕ) |- ((m, n) ∈ memRel) \/ ((n, m) ∈ memRel) \/ (m === n)) subproof {
      assume(m ∈ ℕ)
      assume(n ∈ ℕ)
      val mInℕ = have(m ∈ ℕ) by Restate
      val nInℕ = have(n ∈ ℕ) by Restate

      val cmp = have((m === n) \/ (m ∈ n) \/ (n ∈ m)) by Tautology.from(natComparability, mInℕ, nInℕ)

      val eqCase = have(m === n |- ((m, n) ∈ memRel) \/ ((n, m) ∈ memRel) \/ (m === n)) by Tautology

      val mnCase = have(m ∈ n |- ((m, n) ∈ memRel) \/ ((n, m) ∈ memRel) \/ (m === n)) subproof {
        assume(m ∈ n)
        have((m, n) ∈ memRel) by Tautology.from(MembershipRelation.membership.of(x := m, y := n, A := ℕ), mInℕ, nInℕ, have(m ∈ n) by Restate)
        have(thesis) by Tautology.from(lastStep)
      }

      val nmCase = have(n ∈ m |- ((m, n) ∈ memRel) \/ ((n, m) ∈ memRel) \/ (m === n)) subproof {
        assume(n ∈ m)
        have((n, m) ∈ memRel) by Tautology.from(MembershipRelation.membership.of(x := n, y := m, A := ℕ), nInℕ, mInℕ, have(n ∈ m) by Restate)
        have(thesis) by Tautology.from(lastStep)
      }

      val goal = ((m, n) ∈ memRel) \/ ((n, m) ∈ memRel) \/ (m === n)

      val eqImp = have((m === n) ==> goal) subproof {
        have(m === n |- goal) subproof {
          val mEqN = assume(m === n)
          have(goal) by Tautology.from(eqCase, mEqN)
        }
        thenHave(thesis) by Restate
      }

      val mnImp = have((m ∈ n) ==> goal) subproof {
        have(m ∈ n |- goal) subproof {
          val mInN = assume(m ∈ n)
          have(goal) by Tautology.from(mnCase, mInN)
        }
        thenHave(thesis) by Restate
      }

      val nmImp = have((n ∈ m) ==> goal) subproof {
        have(n ∈ m |- goal) subproof {
          val nInM = assume(n ∈ m)
          have(goal) by Tautology.from(nmCase, nInM)
        }
        thenHave(thesis) by Restate
      }

      have(thesis) by Tautology.from(cmp, eqImp, mnImp, nmImp)
    }
    thenHave(() |- ((m ∈ ℕ) /\ (n ∈ ℕ)) ==> (((m, n) ∈ memRel) \/ ((n, m) ∈ memRel) \/ (m === n))) by Tableau
    thenHave(() |- ∀(n, ((m ∈ ℕ) /\ (n ∈ ℕ)) ==> (((m, n) ∈ memRel) \/ ((n, m) ∈ memRel) \/ (m === n)))) by RightForall
    thenHave(() |- ∀(m, ∀(n, ((m ∈ ℕ) /\ (n ∈ ℕ)) ==> (((m, n) ∈ memRel) \/ ((n, m) ∈ memRel) \/ (m === n))))) by RightForall
    val allConj = lastStep
    val disjMN = ((m, n) ∈ memRel) \/ ((n, m) ∈ memRel) \/ (m === n)

    have(∀(m, (m ∈ ℕ) ==> ∀(n, (n ∈ ℕ) ==> disjMN))) subproof {
      have((m ∈ ℕ) |- ∀(n, (n ∈ ℕ) ==> disjMN)) subproof {
        val mInℕ = assume(m ∈ ℕ)

        have((n ∈ ℕ) |- disjMN) subproof {
          val nInℕ = assume(n ∈ ℕ)

          have(∀(n, ((m ∈ ℕ) /\ (n ∈ ℕ)) ==> disjMN)).by(InstantiateForall(m)(allConj))
          thenHave(((m ∈ ℕ) /\ (n ∈ ℕ)) ==> disjMN) by InstantiateForall(n)
          have(disjMN) by Tautology.from(lastStep, mInℕ, nInℕ)
          have(thesis) by Restate.from(lastStep)
        }
        thenHave((n ∈ ℕ) ==> disjMN) by Restate
        thenHave(∀(n, (n ∈ ℕ) ==> disjMN)) by RightForall
        have(thesis) by Restate.from(lastStep)
      }
      thenHave((m ∈ ℕ) ==> ∀(n, (n ∈ ℕ) ==> disjMN)) by Restate
      thenHave(∀(m, (m ∈ ℕ) ==> ∀(n, (n ∈ ℕ) ==> disjMN))) by RightForall
      have(thesis) by Restate.from(lastStep)
    }

    thenHave(∀(m ∈ ℕ, ∀(n ∈ ℕ, disjMN))) by Restate
    thenHave(thesis) by Substitute(total.definition.of(R := memRel, X := ℕ))
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
        assume(m ∈ ℕ)
        assume(n ∈ ℕ)
        assume(k ∈ ℕ)
        val mInℕ = have(m ∈ ℕ) by Restate
        val nInℕ = have(n ∈ ℕ) by Restate
        val kInℕ = have(k ∈ ℕ) by Restate

        assume((m, n) ∈ memRel)
        val mInN = have(m ∈ n) by Tautology.from(MembershipRelation.membership.of(x := m, y := n, A := ℕ), mInℕ, nInℕ, have((m, n) ∈ memRel) by Restate)

        assume((n, k) ∈ memRel)
        val nInK = have(n ∈ k) by Tautology.from(MembershipRelation.membership.of(x := n, y := k, A := ℕ), nInℕ, kInℕ, have((n, k) ∈ memRel) by Restate)

        // k is transitive (as a natural), so from m ∈ n and n ∈ k we infer m ∈ k.
        val kTrans = have(TransitiveSet.transitiveSet(k)) by Tautology.from(natElementsTransitive.of(n := k), kInℕ)
        val mInK = have(m ∈ k) by Tautology.from(TransitiveSet.transitivity.of(x := m, y := n, A := k), kTrans, mInN, nInK)

        have((m, k) ∈ memRel) by Tautology.from(MembershipRelation.membership.of(x := m, y := k, A := ℕ), mInℕ, kInℕ, mInK)
        have(thesis) by Restate.from(lastStep)
      }
      thenHave(() |- ((m ∈ ℕ) /\ (n ∈ ℕ) /\ (k ∈ ℕ) /\ ((m, n) ∈ memRel) /\ ((n, k) ∈ memRel)) ==> ((m, k) ∈ memRel)) by Tableau
      thenHave(() |- ∀(k, ((m ∈ ℕ) /\ (n ∈ ℕ) /\ (k ∈ ℕ) /\ ((m, n) ∈ memRel) /\ ((n, k) ∈ memRel)) ==> ((m, k) ∈ memRel))) by RightForall
      thenHave(() |- ∀(n, ∀(k, ((m ∈ ℕ) /\ (n ∈ ℕ) /\ (k ∈ ℕ) /\ ((m, n) ∈ memRel) /\ ((n, k) ∈ memRel)) ==> ((m, k) ∈ memRel)))) by RightForall
      thenHave(() |- ∀(m, ∀(n, ∀(k, ((m ∈ ℕ) /\ (n ∈ ℕ) /\ (k ∈ ℕ) /\ ((m, n) ∈ memRel) /\ ((n, k) ∈ memRel)) ==> ((m, k) ∈ memRel))))) by RightForall
      val allConj = lastStep
      val relImp = (((m, n) ∈ memRel) /\ ((n, k) ∈ memRel)) ==> ((m, k) ∈ memRel)

      have(∀(m, (m ∈ ℕ) ==> ∀(n, (n ∈ ℕ) ==> ∀(k, (k ∈ ℕ) ==> relImp)))) subproof {
        have((m ∈ ℕ) |- ∀(n, (n ∈ ℕ) ==> ∀(k, (k ∈ ℕ) ==> relImp))) subproof {
          val mInℕ = assume(m ∈ ℕ)

          have((n ∈ ℕ) |- ∀(k, (k ∈ ℕ) ==> relImp)) subproof {
            val nInℕ = assume(n ∈ ℕ)

            have((k ∈ ℕ) |- relImp) subproof {
              val kInℕ = assume(k ∈ ℕ)

              have(((m, n) ∈ memRel) /\ ((n, k) ∈ memRel) |- (m, k) ∈ memRel) subproof {
                val rels = assume(((m, n) ∈ memRel) /\ ((n, k) ∈ memRel))
                val mn = have((m, n) ∈ memRel) by Tautology.from(rels)
                val nk = have((n, k) ∈ memRel) by Tautology.from(rels)

                have(∀(n, ∀(k, ((m ∈ ℕ) /\ (n ∈ ℕ) /\ (k ∈ ℕ) /\ ((m, n) ∈ memRel) /\ ((n, k) ∈ memRel)) ==> ((m, k) ∈ memRel)))).by(InstantiateForall(m)(allConj))
                thenHave(∀(k, ((m ∈ ℕ) /\ (n ∈ ℕ) /\ (k ∈ ℕ) /\ ((m, n) ∈ memRel) /\ ((n, k) ∈ memRel)) ==> ((m, k) ∈ memRel))) by InstantiateForall(n)
                thenHave(((m ∈ ℕ) /\ (n ∈ ℕ) /\ (k ∈ ℕ) /\ ((m, n) ∈ memRel) /\ ((n, k) ∈ memRel)) ==> ((m, k) ∈ memRel)) by InstantiateForall(k)

                have((m, k) ∈ memRel) by Tautology.from(lastStep, mInℕ, nInℕ, kInℕ, mn, nk)
                have(thesis) by Restate.from(lastStep)
              }
              thenHave(relImp) by Restate
              have(thesis) by Restate.from(lastStep)
            }
            thenHave((k ∈ ℕ) ==> relImp) by Restate
            thenHave(∀(k, (k ∈ ℕ) ==> relImp)) by RightForall
            have(thesis) by Restate.from(lastStep)
          }
          thenHave((n ∈ ℕ) ==> ∀(k, (k ∈ ℕ) ==> relImp)) by Restate
          thenHave(∀(n, (n ∈ ℕ) ==> ∀(k, (k ∈ ℕ) ==> relImp))) by RightForall
          have(thesis) by Restate.from(lastStep)
        }
        thenHave((m ∈ ℕ) ==> ∀(n, (n ∈ ℕ) ==> ∀(k, (k ∈ ℕ) ==> relImp))) by Restate
        thenHave(∀(m, (m ∈ ℕ) ==> ∀(n, (n ∈ ℕ) ==> ∀(k, (k ∈ ℕ) ==> relImp)))) by RightForall
        have(thesis) by Restate.from(lastStep)
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
  val addZero = Theorem(∀(m, m + zero === m)) {
    have(m + zero === m) subproof {
      val wo = have(WellOrder.wellOrder(ℕ)(memRel)).by(Restate.from(natWellOrder))

      val Fm = λ(
        x,
        λ(
          h,
          ε(
            y,
            ((x === zero) /\ (y === m)) \/
              ∃(k, (k ∈ ℕ) /\ (x === S(k)) /\ (y === S(app(h)(k))))
          )
        )
      )

      val Gm = Necessary.recursiveFunctionOn(Fm)(ℕ)(memRel)

      val spec = have(
        functionOn(Gm)(ℕ) /\
          ∀(x ∈ ℕ, app(Gm)(x) === Fm(x)(Gm ↾ InitialSegment.initialSegment(x)(ℕ)(memRel)))
      ).by(Cut(wo, Necessary.recursiveFunctionOnSpec.of(A := ℕ, R := memRel, Necessary.Func := Fm)))

      val eqAll = have(
        ∀(x ∈ ℕ, app(Gm)(x) === Fm(x)(Gm ↾ InitialSegment.initialSegment(x)(ℕ)(memRel)))
      ).by(Tautology.from(spec))

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
          ∃(k, (k ∈ ℕ) /\ (zero === S(k)) /\ (y === S(app(Gm ↾ zero)(k))))
      )

      val Fm0 = have(Fm(zero)(Gm ↾ zero) === ε(y, Q(y))).by(Restate)

      val exY = have(∃(y, Q(y))) subproof {
        val zRefl = have(zero === zero).by(Restate)
        val mRefl = have(m === m).by(Restate)
        have(Q(m)).by(Tautology.from(zRefl, mRefl))
        thenHave(thesis).by(RightExists)
      }

      val uniq = have(∀(y, Q(y) ==> (y === m))) subproof {
        have(Q(y) |- y === m) subproof {
          assume(Q(y))

          val case1 = have((zero === zero) /\ (y === m) |- y === m).by(Tautology)
          val case1Imp = have(((zero === zero) /\ (y === m)) ==> (y === m)).by(Restate.from(case1))

          val case2 = have(∃(k, (k ∈ ℕ) /\ (zero === S(k)) /\ (y === S(app(Gm ↾ zero)(k)))) |- y === m) subproof {
            assume(∃(k, (k ∈ ℕ) /\ (zero === S(k)) /\ (y === S(app(Gm ↾ zero)(k)))))

            have((k ∈ ℕ) /\ (zero === S(k)) /\ (y === S(app(Gm ↾ zero)(k))) |- ()) subproof {
              val kInℕ = have((k ∈ ℕ) /\ (zero === S(k)) /\ (y === S(app(Gm ↾ zero)(k))) |- k ∈ ℕ).by(Tautology)
              val zEqSk = have((k ∈ ℕ) /\ (zero === S(k)) /\ (y === S(app(Gm ↾ zero)(k))) |- zero === S(k)).by(Tautology)
              val SkEq0 = have((k ∈ ℕ) /\ (zero === S(k)) /\ (y === S(app(Gm ↾ zero)(k))) |- S(k) === zero).by(Congruence.from(zEqSk))
              val SkNe0 = have(k ∈ ℕ |- (S(k) =/= zero)).by(Weakening(succNeZero.of(n := k)))
              val notSkEq0 = have((k ∈ ℕ) /\ (zero === S(k)) /\ (y === S(app(Gm ↾ zero)(k))) |- ¬(S(k) === zero)).by(
                Tautology.from(SkNe0, kInℕ)
              )
              have(thesis).by(Tautology.from(SkEq0, notSkEq0))
            }
            thenHave(∃(k, (k ∈ ℕ) /\ (zero === S(k)) /\ (y === S(app(Gm ↾ zero)(k)))) |- ()).by(LeftExists)
            thenHave(thesis).by(Tautology)
          }

          val case2Imp = have(
            ∃(k, (k ∈ ℕ) /\ (zero === S(k)) /\ (y === S(app(Gm ↾ zero)(k)))) ==> (y === m)
          ).by(Restate.from(case2))

          val disj = have(
            ((zero === zero) /\ (y === m)) \/
              ∃(k, (k ∈ ℕ) /\ (zero === S(k)) /\ (y === S(app(Gm ↾ zero)(k))))
          ).by(Restate)

          have(thesis).by(Tautology.from(disj, case1Imp, case2Imp))
        }
        thenHave(Q(y) ==> (y === m)).by(Restate)
        thenHave(thesis).by(RightForall)
      }

      val epsQ = have(Q(ε(y, Q(y)))).by(Cut(exY, Quantifiers.existsEpsilon.of(x := y, P := Q)))

      val epsEq = have(ε(y, Q(y)) === m) subproof {
        have(∀(y, Q(y) ==> (y === m))).by(Restate.from(uniq))
        thenHave(Q(ε(y, Q(y))) ==> (ε(y, Q(y)) === m)).by(InstantiateForall(ε(y, Q(y))))
        have(thesis).by(Tautology.from(epsQ, lastStep))
      }

      val addDef0 = have(m + zero === app(Gm)(zero)).by(Restate.from(add.definition.of(m := m, n := zero)))

      val rhsEqM = have(Fm(zero)(Gm ↾ zero) === m).by(Congruence.from(Fm0, epsEq))

      val rec0 = have(zero ∈ ℕ |- m + zero === m).by(Congruence.from(addDef0, eq0r, rhsEqM))
      have(thesis).by(Cut(zeroInℕ, rec0))
    }
    thenHave(∀(m, m + zero === m)).by(RightForall)
    have(thesis).by(Restate.from(lastStep))
  }

  /** Theorem: recursion equation for addition at successors (requires `n ∈ ℕ`). */
  val addSucc = Theorem(∀(m, ∀(n, (n ∈ ℕ) ==> (m + S(n) === S(m + n))))) {
    have((n ∈ ℕ) ==> (m + S(n) === S(m + n))) subproof {
      val nInℕ = assume(n ∈ ℕ)

      val wo = have(WellOrder.wellOrder(ℕ)(memRel)).by(Restate.from(natWellOrder))

      val Fm = λ(
        x,
        λ(
          h,
          ε(
            y,
            ((x === zero) /\ (y === m)) \/
              ∃(k, (k ∈ ℕ) /\ (x === S(k)) /\ (y === S(app(h)(k))))
          )
        )
      )

      val Gm = Necessary.recursiveFunctionOn(Fm)(ℕ)(memRel)

      val spec = have(
        functionOn(Gm)(ℕ) /\
          ∀(x ∈ ℕ, app(Gm)(x) === Fm(x)(Gm ↾ InitialSegment.initialSegment(x)(ℕ)(memRel)))
      ).by(Cut(wo, Necessary.recursiveFunctionOnSpec.of(A := ℕ, R := memRel, Necessary.Func := Fm)))

      val GmOn = have(functionOn(Gm)(ℕ)).by(Tautology.from(spec))
      val eqAll = have(
        ∀(x ∈ ℕ, app(Gm)(x) === Fm(x)(Gm ↾ InitialSegment.initialSegment(x)(ℕ)(memRel)))
      ).by(Tautology.from(spec))

      val succClosedAll = have(∀(k, (k ∈ ℕ) ==> (S(k) ∈ ℕ))).by(Restate.from(succClosed))
      val succClosedN = have((n ∈ ℕ) ==> (S(n) ∈ ℕ)).by(InstantiateForall(n)(succClosedAll))
      val SnInℕ = have(S(n) ∈ ℕ).by(Tautology.from(nInℕ, succClosedN))

      val eqSn = have(
        S(n) ∈ ℕ |- app(Gm)(S(n)) === Fm(S(n))(Gm ↾ InitialSegment.initialSegment(S(n))(ℕ)(memRel))
      ).by(InstantiateForall(S(n))(eqAll))

      val initSn = have(S(n) ∈ ℕ |- InitialSegment.initialSegment(S(n))(ℕ)(memRel) === S(n)).by(
        Restate.from(natInitialSegment.of(n := S(n)))
      )

      val eqSnr = have(S(n) ∈ ℕ |- app(Gm)(S(n)) === Fm(S(n))(Gm ↾ S(n))).by(Substitute(initSn)(eqSn))

      val hSn = Gm ↾ S(n)

      val Q = λ(
        y,
        ((S(n) === zero) /\ (y === m)) \/
          ∃(k, (k ∈ ℕ) /\ (S(n) === S(k)) /\ (y === S(app(hSn)(k))))
      )

      val FmSn = have(Fm(S(n))(hSn) === ε(y, Q(y))).by(Restate)

      val exY = have(∃(y, Q(y))) subproof {
        val SnEqSn = have(S(n) === S(n)).by(Restate)
        val zRefl = have(S(app(hSn)(n)) === S(app(hSn)(n))).by(Restate)
        have((n ∈ ℕ) /\ (S(n) === S(n)) /\ (S(app(hSn)(n)) === S(app(hSn)(n)))).by(Tautology.from(nInℕ, SnEqSn, zRefl))
        thenHave(
          ∃(k, (k ∈ ℕ) /\ (S(n) === S(k)) /\ (S(app(hSn)(n)) === S(app(hSn)(k))))
        ).by(RightExists)
        thenHave(Q(S(app(hSn)(n)))).by(Tautology)
        thenHave(thesis).by(RightExists)
      }

      val uniq = have(∀(y, Q(y) ==> (y === S(app(hSn)(n))))) subproof {
        have(Q(y) |- y === S(app(hSn)(n))) subproof {
          assume(Q(y))

          val SnNe0 = have(S(n) =/= zero).by(Tautology.from(nInℕ, succNeZero.of(n := n)))
          val notSnEq0 = have(¬(S(n) === zero)).by(Tautology.from(SnNe0))

          val case1 = have((S(n) === zero) /\ (y === m) |- y === S(app(hSn)(n))) subproof {
            val SnEq0 = have((S(n) === zero) /\ (y === m) |- S(n) === zero).by(Tautology)
            val notSnEq0Under = have((S(n) === zero) /\ (y === m) |- ¬(S(n) === zero)).by(Weakening(notSnEq0))
            val contra = have((S(n) === zero) /\ (y === m) |- ()).by(Tautology.from(SnEq0, notSnEq0Under))
            have(thesis).by(Weakening(contra))
          }
          val case1Imp = have(((S(n) === zero) /\ (y === m)) ==> (y === S(app(hSn)(n)))).by(Restate.from(case1))

          val case2 = have(
            ∃(k, (k ∈ ℕ) /\ (S(n) === S(k)) /\ (y === S(app(hSn)(k)))) |- y === S(app(hSn)(n))
          ) subproof {
            assume(∃(k, (k ∈ ℕ) /\ (S(n) === S(k)) /\ (y === S(app(hSn)(k)))))

            have((k ∈ ℕ) /\ (S(n) === S(k)) /\ (y === S(app(hSn)(k))) |- y === S(app(hSn)(n))) subproof {
              val SnEqSk = have((k ∈ ℕ) /\ (S(n) === S(k)) /\ (y === S(app(hSn)(k))) |- S(n) === S(k)).by(Tautology)
              val yEq = have((k ∈ ℕ) /\ (S(n) === S(k)) /\ (y === S(app(hSn)(k))) |- y === S(app(hSn)(k))).by(Tautology)

              val inj = have(S(n) === S(k) |- n === k).by(
                Tautology.from(
                  succInjective.of(m := n, n := k)
                )
              )

              val nEqk = have((k ∈ ℕ) /\ (S(n) === S(k)) /\ (y === S(app(hSn)(k))) |- n === k).by(Cut(SnEqSk, inj))
              val kEqn = have((k ∈ ℕ) /\ (S(n) === S(k)) /\ (y === S(app(hSn)(k))) |- k === n).by(Congruence.from(nEqk))

              val hkEq = have((k ∈ ℕ) /\ (S(n) === S(k)) /\ (y === S(app(hSn)(k))) |- app(hSn)(k) === app(hSn)(n)).by(
                Congruence.from(kEqn)
              )

              val SkEqSn = have((k ∈ ℕ) /\ (S(n) === S(k)) /\ (y === S(app(hSn)(k))) |- S(app(hSn)(k)) === S(app(hSn)(n))).by(
                Congruence.from(hkEq)
              )

              have(thesis).by(Congruence.from(yEq, SkEqSn))
            }
            thenHave(∃(k, (k ∈ ℕ) /\ (S(n) === S(k)) /\ (y === S(app(hSn)(k)))) |- y === S(app(hSn)(n))).by(LeftExists)
          }

          val case2Imp = have(
            ∃(k, (k ∈ ℕ) /\ (S(n) === S(k)) /\ (y === S(app(hSn)(k)))) ==> (y === S(app(hSn)(n)))
          ).by(Restate.from(case2))

          val disj = have(
            ((S(n) === zero) /\ (y === m)) \/
              ∃(k, (k ∈ ℕ) /\ (S(n) === S(k)) /\ (y === S(app(hSn)(k))))
          ).by(Restate)

          have(thesis).by(Tautology.from(disj, case1Imp, case2Imp))
        }
        thenHave(Q(y) ==> (y === S(app(hSn)(n)))).by(Restate)
        thenHave(thesis).by(RightForall)
      }

      val epsQ = have(Q(ε(y, Q(y)))).by(Cut(exY, Quantifiers.existsEpsilon.of(x := y, P := Q)))

      val epsEq = have(ε(y, Q(y)) === S(app(hSn)(n))) subproof {
        have(∀(y, Q(y) ==> (y === S(app(hSn)(n))))).by(Restate.from(uniq))
        thenHave(Q(ε(y, Q(y))) ==> (ε(y, Q(y)) === S(app(hSn)(n)))).by(InstantiateForall(ε(y, Q(y))))
        have(thesis).by(Tautology.from(epsQ, lastStep))
      }

      val hSnAtN = have(app(hSn)(n) === app(Gm)(n)) subproof {
        val nSubℕ = have(n ⊆ ℕ).by(Cut(nInℕ, `n ∈ ℕ -> n ⊆ ℕ`))
        val SnSubℕ = have(S(n) ⊆ ℕ).by(Tautology.from(succSubsetℕ, nSubℕ, nInℕ))
        val nInSn = have(n ∈ S(n)).by(Weakening(nInSucc))
        val restEq = have((functionOn(Gm)(ℕ), S(n) ⊆ ℕ, n ∈ S(n)) |- app(Gm ↾ S(n))(n) === app(Gm)(n)).by(
          Restate.from(Necessary.restrictionAppSubset.of(f := Gm, A := ℕ, B := S(n), x := n))
        )
        have(thesis).by(Tautology.from(restEq, GmOn, SnSubℕ, nInSn))
      }

      val rhsEq2 = have(S(app(hSn)(n)) === S(app(Gm)(n))).by(Congruence.from(hSnAtN))
      val trans = have((ε(y, Q(y)) === S(app(hSn)(n)), S(app(hSn)(n)) === S(app(Gm)(n))) |- ε(y, Q(y)) === S(app(Gm)(n))).by(Congruence)
      val trans1 = have((ε(y, Q(y)) === S(app(hSn)(n))) |- ε(y, Q(y)) === S(app(Gm)(n))).by(Cut(rhsEq2, trans))
      val rhsEqEps = have(ε(y, Q(y)) === S(app(Gm)(n))).by(Cut(epsEq, trans1))
      val rhsEq = have(Fm(S(n))(hSn) === S(app(Gm)(n))).by(Restate.from(rhsEqEps))

      val addDefSn = have(m + S(n) === app(Gm)(S(n))).by(Restate.from(add.definition.of(m := m, n := S(n))))
      val addDefN = have(m + n === app(Gm)(n)).by(Restate.from(add.definition.of(m := m, n := n)))

      val Smn = have(S(m + n) === S(app(Gm)(n))).by(Congruence.from(addDefN))

      val recSn = have(S(n) ∈ ℕ |- m + S(n) === S(m + n)).by(Congruence.from(addDefSn, eqSnr, rhsEq, Smn))
      have(thesis).by(Tautology.from(SnInℕ, recSn))
    }

    thenHave(∀(n, (n ∈ ℕ) ==> (m + S(n) === S(m + n)))).by(RightForall)
    thenHave(thesis).by(RightForall)
  }

  /** Theorem: recursion equation for multiplication at `0` (recursion on the second argument). */
  val mulZero = Theorem(∀(m, m * zero === zero)) {
    have(m * zero === zero) subproof {
      val wo = have(WellOrder.wellOrder(ℕ)(memRel)).by(Restate.from(natWellOrder))

      val Fm = λ(
        x,
        λ(
          h,
          ε(
            y,
            ((x === zero) /\ (y === zero)) \/
              ∃(k, (k ∈ ℕ) /\ (x === S(k)) /\ (y === add(app(h)(k))(m)))
          )
        )
      )

      val Gm = Necessary.recursiveFunctionOn(Fm)(ℕ)(memRel)

      val spec = have(
        functionOn(Gm)(ℕ) /\
          ∀(x ∈ ℕ, app(Gm)(x) === Fm(x)(Gm ↾ InitialSegment.initialSegment(x)(ℕ)(memRel)))
      ).by(Cut(wo, Necessary.recursiveFunctionOnSpec.of(A := ℕ, R := memRel, Necessary.Func := Fm)))

      val eqAll = have(
        ∀(x ∈ ℕ, app(Gm)(x) === Fm(x)(Gm ↾ InitialSegment.initialSegment(x)(ℕ)(memRel)))
      ).by(Tautology.from(spec))

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
          ∃(k, (k ∈ ℕ) /\ (zero === S(k)) /\ (y === add(app(Gm ↾ zero)(k))(m)))
      )

      val Fm0 = have(Fm(zero)(Gm ↾ zero) === ε(y, Q(y))).by(Restate)

      val exY = have(∃(y, Q(y))) subproof {
        val zRefl = have(zero === zero).by(Restate)
        val zRefl2 = have(zero === zero).by(Restate)
        have(Q(zero)).by(Tautology.from(zRefl, zRefl2))
        thenHave(thesis).by(RightExists)
      }

      val uniq = have(∀(y, Q(y) ==> (y === zero))) subproof {
        have(Q(y) |- y === zero) subproof {
          assume(Q(y))

          val case1 = have((zero === zero) /\ (y === zero) |- y === zero).by(Tautology)
          val case1Imp = have(((zero === zero) /\ (y === zero)) ==> (y === zero)).by(Restate.from(case1))

          val case2 = have(∃(k, (k ∈ ℕ) /\ (zero === S(k)) /\ (y === add(app(Gm ↾ zero)(k))(m))) |- y === zero) subproof {
            assume(∃(k, (k ∈ ℕ) /\ (zero === S(k)) /\ (y === add(app(Gm ↾ zero)(k))(m))))

            have((k ∈ ℕ) /\ (zero === S(k)) /\ (y === add(app(Gm ↾ zero)(k))(m)) |- ()) subproof {
              val kInℕ = have((k ∈ ℕ) /\ (zero === S(k)) /\ (y === add(app(Gm ↾ zero)(k))(m)) |- k ∈ ℕ).by(Tautology)
              val zEqSk = have((k ∈ ℕ) /\ (zero === S(k)) /\ (y === add(app(Gm ↾ zero)(k))(m)) |- zero === S(k)).by(Tautology)
              val SkEq0 = have((k ∈ ℕ) /\ (zero === S(k)) /\ (y === add(app(Gm ↾ zero)(k))(m)) |- S(k) === zero).by(Congruence.from(zEqSk))
              val SkNe0 = have(k ∈ ℕ |- (S(k) =/= zero)).by(Weakening(succNeZero.of(n := k)))
              val notSkEq0 = have((k ∈ ℕ) /\ (zero === S(k)) /\ (y === add(app(Gm ↾ zero)(k))(m)) |- ¬(S(k) === zero)).by(
                Tautology.from(SkNe0, kInℕ)
              )
              have(thesis).by(Tautology.from(SkEq0, notSkEq0))
            }
            thenHave(∃(k, (k ∈ ℕ) /\ (zero === S(k)) /\ (y === add(app(Gm ↾ zero)(k))(m))) |- ()).by(LeftExists)
            thenHave(thesis).by(Tautology)
          }

          val case2Imp = have(
            ∃(k, (k ∈ ℕ) /\ (zero === S(k)) /\ (y === add(app(Gm ↾ zero)(k))(m))) ==> (y === zero)
          ).by(Restate.from(case2))

          val disj = have(
            ((zero === zero) /\ (y === zero)) \/
              ∃(k, (k ∈ ℕ) /\ (zero === S(k)) /\ (y === add(app(Gm ↾ zero)(k))(m)))
          ).by(Restate)

          have(thesis).by(Tautology.from(disj, case1Imp, case2Imp))
        }
        thenHave(Q(y) ==> (y === zero)).by(Restate)
        thenHave(thesis).by(RightForall)
      }

      val epsQ = have(Q(ε(y, Q(y)))).by(Cut(exY, Quantifiers.existsEpsilon.of(x := y, P := Q)))

      val epsEq = have(ε(y, Q(y)) === zero) subproof {
        have(∀(y, Q(y) ==> (y === zero))).by(Restate.from(uniq))
        thenHave(Q(ε(y, Q(y))) ==> (ε(y, Q(y)) === zero)).by(InstantiateForall(ε(y, Q(y))))
        have(thesis).by(Tautology.from(epsQ, lastStep))
      }

      val mulDef0 = have(m * zero === app(Gm)(zero)).by(Restate.from(mul.definition.of(m := m, n := zero)))

      val rhsEq0 = have(Fm(zero)(Gm ↾ zero) === zero).by(Congruence.from(Fm0, epsEq))

      val rec0 = have(zero ∈ ℕ |- m * zero === zero).by(Congruence.from(mulDef0, eq0r, rhsEq0))
      have(thesis).by(Cut(zeroInℕ, rec0))
    }
    thenHave(∀(m, m * zero === zero)).by(RightForall)
    have(thesis).by(Restate.from(lastStep))
  }


  /**
   * Let's define first a `double` function, as a first step.
   * double ∈ ℕ -> ℕ
   * double(zero) = zero
   * n ∈ ℕ => (double(S(n)) = S(S(double(n)))))
   */

  /** Doubling (defined by well-ordered recursion on `(ℕ, ∈_ℕ)`). */
  val double = DEF(
    λ(n,
      app(
        Necessary.recursiveFunctionOn(
          λ(
            x,
            λ(
              h,
              ε(
                y,
                ((x === zero) /\ (y === zero)) \/
                  ∃(k, (k ∈ ℕ) /\ (x === S(k)) /\ (y === S(S(app(h)(k)))))
              )
            )
          )
        )(ℕ)(memRel)
      )(n)
    )
  )

  /** Theorem: `double(0) = 0`. */
  val doubleZero = Theorem(double(zero) === zero) {
    val wo = have(WellOrder.wellOrder(ℕ)(memRel)).by(Restate.from(natWellOrder))

    val F = λ(
      x,
      λ(
        h,
        ε(
          y,
          ((x === zero) /\ (y === zero)) \/
            ∃(k, (k ∈ ℕ) /\ (x === S(k)) /\ (y === S(S(app(h)(k)))))
        )
      )
    )

    val G = Necessary.recursiveFunctionOn(F)(ℕ)(memRel)

    val spec = have(
      functionOn(G)(ℕ) /\
        ∀(x ∈ ℕ, app(G)(x) === F(x)(G ↾ InitialSegment.initialSegment(x)(ℕ)(memRel)))
    ).by(Cut(wo, Necessary.recursiveFunctionOnSpec.of(A := ℕ, R := memRel, Necessary.Func := F)))

    val eqAll = have(
      ∀(x ∈ ℕ, app(G)(x) === F(x)(G ↾ InitialSegment.initialSegment(x)(ℕ)(memRel)))
    ).by(Tautology.from(spec))

    val eq0 = have(
      zero ∈ ℕ |- app(G)(zero) === F(zero)(G ↾ InitialSegment.initialSegment(zero)(ℕ)(memRel))
    ).by(InstantiateForall(zero)(eqAll))

    val init0 = have(zero ∈ ℕ |- InitialSegment.initialSegment(zero)(ℕ)(memRel) === zero).by(
      Restate.from(natInitialSegment.of(n := zero))
    )

    val eq0r = have(zero ∈ ℕ |- app(G)(zero) === F(zero)(G ↾ zero)).by(Substitute(init0)(eq0))

    val Q = λ(
      y,
      ((zero === zero) /\ (y === zero)) \/
        ∃(k, (k ∈ ℕ) /\ (zero === S(k)) /\ (y === S(S(app(G ↾ zero)(k)))))
    )

    val F0 = have(F(zero)(G ↾ zero) === ε(y, Q(y))).by(Restate)

    val exY = have(∃(y, Q(y))) subproof {
      val zRefl = have(zero === zero).by(Restate)
      val zRefl2 = have(zero === zero).by(Restate)
      have(Q(zero)).by(Tautology.from(zRefl, zRefl2))
      thenHave(thesis).by(RightExists)
    }

    val uniq = have(∀(y, Q(y) ==> (y === zero))) subproof {
      have(Q(y) |- y === zero) subproof {
        assume(Q(y))

        val case1 = have((zero === zero) /\ (y === zero) |- y === zero).by(Tautology)
        val case1Imp = have(((zero === zero) /\ (y === zero)) ==> (y === zero)).by(Restate.from(case1))

        val case2 = have(∃(k, (k ∈ ℕ) /\ (zero === S(k)) /\ (y === S(S(app(G ↾ zero)(k))))) |- y === zero) subproof {
          assume(∃(k, (k ∈ ℕ) /\ (zero === S(k)) /\ (y === S(S(app(G ↾ zero)(k))))))

          have((k ∈ ℕ) /\ (zero === S(k)) /\ (y === S(S(app(G ↾ zero)(k)))) |- ()) subproof {
            val kInℕ = have((k ∈ ℕ) /\ (zero === S(k)) /\ (y === S(S(app(G ↾ zero)(k)))) |- k ∈ ℕ).by(Tautology)
            val zEqSk = have((k ∈ ℕ) /\ (zero === S(k)) /\ (y === S(S(app(G ↾ zero)(k)))) |- zero === S(k)).by(Tautology)
            val SkEq0 = have((k ∈ ℕ) /\ (zero === S(k)) /\ (y === S(S(app(G ↾ zero)(k)))) |- S(k) === zero).by(Congruence.from(zEqSk))
            val SkNe0 = have(k ∈ ℕ |- (S(k) =/= zero)).by(Weakening(succNeZero.of(n := k)))
            val notSkEq0 = have((k ∈ ℕ) /\ (zero === S(k)) /\ (y === S(S(app(G ↾ zero)(k)))) |- ¬(S(k) === zero)).by(
              Tautology.from(SkNe0, kInℕ)
            )
            have(thesis).by(Tautology.from(SkEq0, notSkEq0))
          }
          thenHave(∃(k, (k ∈ ℕ) /\ (zero === S(k)) /\ (y === S(S(app(G ↾ zero)(k))))) |- ()).by(LeftExists)
          thenHave(thesis).by(Tautology)
        }

        val case2Imp = have(
          ∃(k, (k ∈ ℕ) /\ (zero === S(k)) /\ (y === S(S(app(G ↾ zero)(k))))) ==> (y === zero)
        ).by(Restate.from(case2))

        val disj = have(
          ((zero === zero) /\ (y === zero)) \/
            ∃(k, (k ∈ ℕ) /\ (zero === S(k)) /\ (y === S(S(app(G ↾ zero)(k)))))
        ).by(Restate)

        have(thesis).by(Tautology.from(disj, case1Imp, case2Imp))
      }
      thenHave(Q(y) ==> (y === zero)).by(Restate)
      thenHave(thesis).by(RightForall)
    }

    val epsQ = have(Q(ε(y, Q(y)))).by(Cut(exY, Quantifiers.existsEpsilon.of(x := y, P := Q)))

    val epsEq = have(ε(y, Q(y)) === zero) subproof {
      have(∀(y, Q(y) ==> (y === zero))).by(Restate.from(uniq))
      thenHave(Q(ε(y, Q(y))) ==> (ε(y, Q(y)) === zero)).by(InstantiateForall(ε(y, Q(y))))
      have(thesis).by(Tautology.from(epsQ, lastStep))
    }

    val doubleDef0 = have(double(zero) === app(G)(zero)).by(Restate.from(double.definition.of(n := zero)))
    val rhsEq0 = have(F(zero)(G ↾ zero) === zero).by(Congruence.from(F0, epsEq))
    val rec0 = have(zero ∈ ℕ |- double(zero) === zero).by(Congruence.from(doubleDef0, eq0r, rhsEq0))
    have(thesis).by(Cut(zeroInℕ, rec0))
  }


  /** Theorem: `n ∈ ℕ ⇒ double(S(n)) = S(S(double(n)))`. */
  val doubleSucc = Theorem(∀(n, (n ∈ ℕ) ==> (double(S(n)) === S(S(double(n)))))) {
    have((n ∈ ℕ) ==> (double(S(n)) === S(S(double(n))))) subproof {
      val nInℕ = assume(n ∈ ℕ)

      val wo = have(WellOrder.wellOrder(ℕ)(memRel)).by(Restate.from(natWellOrder))

      val F = λ(
        x,
        λ(
          h,
          ε(
            y,
            ((x === zero) /\ (y === zero)) \/
              ∃(k, (k ∈ ℕ) /\ (x === S(k)) /\ (y === S(S(app(h)(k)))))
          )
        )
      )

      val G = Necessary.recursiveFunctionOn(F)(ℕ)(memRel)

      val spec = have(
        functionOn(G)(ℕ) /\
          ∀(x ∈ ℕ, app(G)(x) === F(x)(G ↾ InitialSegment.initialSegment(x)(ℕ)(memRel)))
      ).by(Cut(wo, Necessary.recursiveFunctionOnSpec.of(A := ℕ, R := memRel, Necessary.Func := F)))

      val GOn = have(functionOn(G)(ℕ)).by(Tautology.from(spec))
      val eqAll = have(
        ∀(x ∈ ℕ, app(G)(x) === F(x)(G ↾ InitialSegment.initialSegment(x)(ℕ)(memRel)))
      ).by(Tautology.from(spec))

      val succClosedAll = have(∀(k, (k ∈ ℕ) ==> (S(k) ∈ ℕ))).by(Restate.from(succClosed))
      val succClosedN = have((n ∈ ℕ) ==> (S(n) ∈ ℕ)).by(InstantiateForall(n)(succClosedAll))
      val SnInℕ = have(S(n) ∈ ℕ).by(Tautology.from(nInℕ, succClosedN))

      val eqSn = have(
        S(n) ∈ ℕ |- app(G)(S(n)) === F(S(n))(G ↾ InitialSegment.initialSegment(S(n))(ℕ)(memRel))
      ).by(InstantiateForall(S(n))(eqAll))

      val initSn = have(S(n) ∈ ℕ |- InitialSegment.initialSegment(S(n))(ℕ)(memRel) === S(n)).by(
        Restate.from(natInitialSegment.of(n := S(n)))
      )

      val eqSnr = have(S(n) ∈ ℕ |- app(G)(S(n)) === F(S(n))(G ↾ S(n))).by(Substitute(initSn)(eqSn))

      val hSn = G ↾ S(n)

      val Q = λ(
        y,
        ((S(n) === zero) /\ (y === zero)) \/
          ∃(k, (k ∈ ℕ) /\ (S(n) === S(k)) /\ (y === S(S(app(hSn)(k)))))
      )

      val FSn = have(F(S(n))(hSn) === ε(y, Q(y))).by(Restate)

      val exY = have(∃(y, Q(y))) subproof {
        val SnEqSn = have(S(n) === S(n)).by(Restate)
        val zRefl = have(S(S(app(hSn)(n))) === S(S(app(hSn)(n)))).by(Restate)
        have((n ∈ ℕ) /\ (S(n) === S(n)) /\ (S(S(app(hSn)(n))) === S(S(app(hSn)(n))))).by(Tautology.from(nInℕ, SnEqSn, zRefl))
        thenHave(
          ∃(k, (k ∈ ℕ) /\ (S(n) === S(k)) /\ (S(S(app(hSn)(n))) === S(S(app(hSn)(k)))))
        ).by(RightExists)
        thenHave(Q(S(S(app(hSn)(n))))).by(Tautology)
        thenHave(thesis).by(RightExists)
      }

      val uniq = have(∀(y, Q(y) ==> (y === S(S(app(hSn)(n)))))) subproof {
        have(Q(y) |- y === S(S(app(hSn)(n)))) subproof {
          assume(Q(y))

          val SnNe0 = have(S(n) =/= zero).by(Tautology.from(nInℕ, succNeZero.of(n := n)))
          val notSnEq0 = have(¬(S(n) === zero)).by(Tautology.from(SnNe0))

          val case1 = have((S(n) === zero) /\ (y === zero) |- y === S(S(app(hSn)(n)))) subproof {
            val SnEq0 = have((S(n) === zero) /\ (y === zero) |- S(n) === zero).by(Tautology)
            val notSnEq0Under = have((S(n) === zero) /\ (y === zero) |- ¬(S(n) === zero)).by(Weakening(notSnEq0))
            val contra = have((S(n) === zero) /\ (y === zero) |- ()).by(Tautology.from(SnEq0, notSnEq0Under))
            have(thesis).by(Weakening(contra))
          }
          val case1Imp = have(((S(n) === zero) /\ (y === zero)) ==> (y === S(S(app(hSn)(n))))).by(Restate.from(case1))

          val case2 = have(
            ∃(k, (k ∈ ℕ) /\ (S(n) === S(k)) /\ (y === S(S(app(hSn)(k))))) |- y === S(S(app(hSn)(n)))
          ) subproof {
            assume(∃(k, (k ∈ ℕ) /\ (S(n) === S(k)) /\ (y === S(S(app(hSn)(k))))))

            have((k ∈ ℕ) /\ (S(n) === S(k)) /\ (y === S(S(app(hSn)(k)))) |- y === S(S(app(hSn)(n)))) subproof {
              val SnEqSk = have((k ∈ ℕ) /\ (S(n) === S(k)) /\ (y === S(S(app(hSn)(k)))) |- S(n) === S(k)).by(Tautology)
              val yEq = have((k ∈ ℕ) /\ (S(n) === S(k)) /\ (y === S(S(app(hSn)(k)))) |- y === S(S(app(hSn)(k)))).by(Tautology)

              val inj = have(S(n) === S(k) |- n === k).by(
                Tautology.from(
                  succInjective.of(m := n, n := k)
                )
              )

              val nEqk = have((k ∈ ℕ) /\ (S(n) === S(k)) /\ (y === S(S(app(hSn)(k)))) |- n === k).by(Cut(SnEqSk, inj))
              val kEqn = have((k ∈ ℕ) /\ (S(n) === S(k)) /\ (y === S(S(app(hSn)(k)))) |- k === n).by(Congruence.from(nEqk))

              val hkEq = have((k ∈ ℕ) /\ (S(n) === S(k)) /\ (y === S(S(app(hSn)(k)))) |- app(hSn)(k) === app(hSn)(n)).by(
                Congruence.from(kEqn)
              )

              val SShkEq = have((k ∈ ℕ) /\ (S(n) === S(k)) /\ (y === S(S(app(hSn)(k)))) |- S(S(app(hSn)(k))) === S(S(app(hSn)(n)))).by(
                Congruence.from(hkEq)
              )

              have(thesis).by(Congruence.from(yEq, SShkEq))
            }
            thenHave(∃(k, (k ∈ ℕ) /\ (S(n) === S(k)) /\ (y === S(S(app(hSn)(k))))) |- y === S(S(app(hSn)(n)))).by(LeftExists)
          }

          val case2Imp = have(
            ∃(k, (k ∈ ℕ) /\ (S(n) === S(k)) /\ (y === S(S(app(hSn)(k))))) ==> (y === S(S(app(hSn)(n))))
          ).by(Restate.from(case2))

          val disj = have(
            ((S(n) === zero) /\ (y === zero)) \/
              ∃(k, (k ∈ ℕ) /\ (S(n) === S(k)) /\ (y === S(S(app(hSn)(k)))))
          ).by(Restate)

          have(thesis).by(Tautology.from(disj, case1Imp, case2Imp))
        }
        thenHave(Q(y) ==> (y === S(S(app(hSn)(n))))).by(Restate)
        thenHave(thesis).by(RightForall)
      }

      val epsQ = have(Q(ε(y, Q(y)))).by(Cut(exY, Quantifiers.existsEpsilon.of(x := y, P := Q)))

      val epsEq = have(ε(y, Q(y)) === S(S(app(hSn)(n)))) subproof {
        have(∀(y, Q(y) ==> (y === S(S(app(hSn)(n)))))).by(Restate.from(uniq))
        thenHave(Q(ε(y, Q(y))) ==> (ε(y, Q(y)) === S(S(app(hSn)(n))))).by(InstantiateForall(ε(y, Q(y))))
        have(thesis).by(Tautology.from(epsQ, lastStep))
      }

      val hSnAtN = have(app(hSn)(n) === app(G)(n)) subproof {
        val nSubℕ = have(n ⊆ ℕ).by(Cut(nInℕ, `n ∈ ℕ -> n ⊆ ℕ`))
        val SnSubℕ = have(S(n) ⊆ ℕ).by(Tautology.from(succSubsetℕ, nSubℕ, nInℕ))
        val nInSn = have(n ∈ S(n)).by(Weakening(nInSucc.of(n := n)))
        val restEq = have((functionOn(G)(ℕ), S(n) ⊆ ℕ, n ∈ S(n)) |- app(G ↾ S(n))(n) === app(G)(n)).by(
          Restate.from(Necessary.restrictionAppSubset.of(f := G, A := ℕ, B := S(n), x := n))
        )
        have(thesis).by(Tautology.from(restEq, GOn, SnSubℕ, nInSn))
      }

      val rhsEq2 = have(S(S(app(hSn)(n))) === S(S(app(G)(n)))).by(Congruence.from(hSnAtN))
      val trans = have((ε(y, Q(y)) === S(S(app(hSn)(n))), S(S(app(hSn)(n))) === S(S(app(G)(n)))) |- ε(y, Q(y)) === S(S(app(G)(n)))).by(Congruence)
      val trans1 = have((ε(y, Q(y)) === S(S(app(hSn)(n)))) |- ε(y, Q(y)) === S(S(app(G)(n)))).by(Cut(rhsEq2, trans))
      val rhsEqEps = have(ε(y, Q(y)) === S(S(app(G)(n)))).by(Cut(epsEq, trans1))
      val rhsEq = have(F(S(n))(hSn) === S(S(app(G)(n)))).by(Restate.from(rhsEqEps))

      val doubleDefSn = have(double(S(n)) === app(G)(S(n))).by(Restate.from(double.definition.of(n := S(n))))
      val doubleDefN = have(double(n) === app(G)(n)).by(Restate.from(double.definition.of(n := n)))
      val SSdn = have(S(S(double(n))) === S(S(app(G)(n)))).by(Congruence.from(doubleDefN))

      val recSn = have(S(n) ∈ ℕ |- double(S(n)) === S(S(double(n)))).by(Congruence.from(doubleDefSn, eqSnr, rhsEq, SSdn))
      have(thesis).by(Tautology.from(SnInℕ, recSn))
    }

    thenHave(∀(n, (n ∈ ℕ) ==> (double(S(n)) === S(S(double(n)))))).by(RightForall)
    have(thesis).by(Restate.from(lastStep))
  }
  /** Theorem: recursion equation for multiplication at successors (requires `n ∈ ℕ`). */
  val mulSucc = Theorem(∀(m, ∀(n, (n ∈ ℕ) ==> (m * S(n) === (m * n) + m)))) {
    sorry
  }

  /** Theorem: closure of addition on `ℕ`. */
  val addClosed = Theorem(∀(m, ∀(n, (m ∈ ℕ /\ n ∈ ℕ) ==> ((m + n) ∈ ℕ)))) {
    sorry
  }

  /** Theorem: closure of multiplication on `ℕ`. */
  val mulClosed = Theorem(∀(m, ∀(n, (m ∈ ℕ /\ n ∈ ℕ) ==> ((m * n) ∈ ℕ)))) {
    sorry
  }

  ///////////////////////////
  // A few derived lemmas.  //
  ///////////////////////////

  /** Lemma: `0 ∈ ℕ` (as a lemma, not just an axiom). */
  val `0 ∈ ℕ` = Lemma(zero ∈ ℕ) {
    have(thesis) by Restate.from(zeroInℕ)
  }

  /** Lemma: if `n ∈ ℕ` then `S(n) ∈ ℕ`. */
  val `n ∈ ℕ -> S(n) ∈ ℕ` = Lemma((n ∈ ℕ) |- S(n) ∈ ℕ) {
    have(∀(m, (m ∈ ℕ) ==> (S(m) ∈ ℕ))).by(Restate.from(succClosed))
    thenHave((n ∈ ℕ) ==> (S(n) ∈ ℕ)) by InstantiateForall(n)
    thenHave(thesis) by Tautology
  }
}
