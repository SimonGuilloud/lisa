package lisa.maths.Arithmetic

import lisa.maths.Arithmetic.Predef.{*, given}
import lisa.maths.Arithmetic.Syntax.{*, given}

/**
 * Parity over naturals.
 *
 * Isabelle/HOL reference: `Parity.thy` (nat instance) and basic recursion facts from `Nat.thy`.
 *
 * In this development we define parity using the recursion-defined function `NatDerived.double`.
 */
object NatParity extends lisa.Main {

  private val Pred = variable[Ind >>: Prop]

  private val a = variable[Ind]
  private val b = variable[Ind]
  private val P0 = variable[Prop]
  private val k = variable[Ind]
  private val k0 = variable[Ind]
  private val m = variable[Ind]
  private val n = variable[Ind]
  private val x = variable[Ind]

  /** Predicate: `Even(n)` defined as `∃k∈ℕ. n = double(k)`. */
  val Even = DEF(
    λ(x, ∃(k, (k ∈ ℕ) /\ (x === NatDerived.double(k))))
  )

  /** Predicate: `Odd(n)` defined as `∃k∈ℕ. n = Succ(double(k))`. */
  val Odd = DEF(
    λ(x, ∃(k, (k ∈ ℕ) /\ (x === Succ(NatDerived.double(k)))))
  )

  // -------------------------
  // Double as addition
  // -------------------------

  /** Theorem: `double(n) = n + n` (for naturals). */
  val doubleEqAddSelf = Theorem(n ∈ ℕ |- (NatDerived.double(n) === n + n)) {
    val ind = Nat.induction of (Pred := λ(n, NatDerived.double(n) === add(n)(n)))

    val base = have(NatDerived.double(0) === add(0)(0)) subproof {
      val d0 = have(NatDerived.double(0) === 0).by(Restate.from(NatDerived.doubleZero))
      val add00 = have(add(0)(0) === 0).by(Weakening(Nat.addZero.of(m := 0)))
      val rhs = have(0 === add(0)(0)).by(Congruence.from(add00))
      have(thesis).by(Congruence.from(d0, rhs))
    }

    val step = have(∀(n, (n ∈ ℕ) ==> ((NatDerived.double(n) === add(n)(n)) ==> (NatDerived.double(Succ(n)) === add(Succ(n))(Succ(n)))))) subproof {
      have((n ∈ ℕ) ==> ((NatDerived.double(n) === add(n)(n)) ==> (NatDerived.double(Succ(n)) === add(Succ(n))(Succ(n))))) subproof {
        val nInℕ = assume(n ∈ ℕ)
        val IH = assume(NatDerived.double(n) === add(n)(n))

        val dSn = have(NatDerived.double(Succ(n)) === Succ(Succ(NatDerived.double(n)))).by(
          Cut(have(n ∈ ℕ).by(Weakening(nInℕ)), NatDerived.doubleSucc.of(n := n))
        )
        val dSn2 = have(NatDerived.double(Succ(n)) === Succ(Succ(add(n)(n)))).by(Congruence.from(dSn, IH))

        val eq1 = have(Succ(n) + Succ(n) === Succ(Succ(n) + n)).by(
          Cut(have(n ∈ ℕ).by(Weakening(nInℕ)), Nat.addSucc.of(m := Succ(n), n := n))
        )
        val eq2 = have(Succ(n) + n === Succ(n + n)).by(Weakening(NatAlgebra.addSuccLeft.of(m := n, n := n)))
        val eq3 = have(Succ(Succ(n) + n) === Succ(Succ(n + n))).by(Congruence.from(eq2))
        val eq4 = have(Succ(Succ(n + n)) === Succ(n) + Succ(n)).by(Congruence.from(eq1, eq3))

        val eq4a = have(Succ(Succ(add(n)(n))) === Succ(n) + Succ(n)).by(Restate.from(eq4))
        have(NatDerived.double(Succ(n)) === add(Succ(n))(Succ(n))).by(Congruence.from(dSn2, eq4a))
        thenHave(thesis).by(Tautology)
      }
      thenHave(thesis).by(RightForall)
    }

    val allN = have(∀(n, (n ∈ ℕ) ==> (NatDerived.double(n) === add(n)(n)))).by(Tautology.from(ind, base, step))

    val imp = have((n ∈ ℕ) ==> (NatDerived.double(n) === add(n)(n))).by(InstantiateForall(n)(allN))
    val nInℕ = assume(n ∈ ℕ)
    val res = have(NatDerived.double(n) === add(n)(n)).by(Tautology.from(imp, nInℕ))
    have(thesis).by(Restate.from(res))
  }

  /** Lemma: `n ∈ ℕ ⇒ double(n) ∈ ℕ`. */
  val doubleClosed = Lemma(n ∈ ℕ |- NatDerived.double(n) ∈ ℕ) {
    val ind = Nat.induction of (Pred := λ(n, NatDerived.double(n) ∈ ℕ))

    val base = have(NatDerived.double(0) ∈ ℕ) subproof {
      val d0 = have(NatDerived.double(0) === 0).by(Restate.from(NatDerived.doubleZero))
      have(thesis).by(Congruence.from(d0, Nat.zeroInℕ))
    }

    val step = have(∀(n, (n ∈ ℕ) ==> ((NatDerived.double(n) ∈ ℕ) ==> (NatDerived.double(Succ(n)) ∈ ℕ)))) subproof {
      have((n ∈ ℕ) ==> ((NatDerived.double(n) ∈ ℕ) ==> (NatDerived.double(Succ(n)) ∈ ℕ))) subproof {
        val nInℕ = assume(n ∈ ℕ)
        val IH = assume(NatDerived.double(n) ∈ ℕ)

        val dSn = have(NatDerived.double(Succ(n)) === Succ(Succ(NatDerived.double(n)))).by(
          Cut(have(n ∈ ℕ).by(Weakening(nInℕ)), NatDerived.doubleSucc.of(n := n))
        )
        val s1 = have(Succ(NatDerived.double(n)) ∈ ℕ).by(Cut(IH, Nat.succClosed.of(n := NatDerived.double(n))))
        val s2 = have(Succ(Succ(NatDerived.double(n))) ∈ ℕ).by(Cut(s1, Nat.succClosed.of(n := Succ(NatDerived.double(n)))))
        have(NatDerived.double(Succ(n)) ∈ ℕ).by(Congruence.from(dSn, s2))
        thenHave(thesis).by(Tautology)
      }
      thenHave(thesis).by(RightForall)
    }

    val allN = have(∀(n, (n ∈ ℕ) ==> (NatDerived.double(n) ∈ ℕ))).by(Tautology.from(ind, base, step))

    val imp = have((n ∈ ℕ) ==> (NatDerived.double(n) ∈ ℕ)).by(InstantiateForall(n)(allN))
    val nInℕ = assume(n ∈ ℕ)
    val res = have(NatDerived.double(n) ∈ ℕ).by(Tautology.from(imp, nInℕ))
    have(thesis).by(Restate.from(res))
  }

  /** Lemma: `double(n) = 0` iff `n = 0` (for naturals). */
  val doubleEqZeroIff = Lemma(n ∈ ℕ |- ((NatDerived.double(n) === 0) <=> (n === 0))) {
    val nInℕ = assume(n ∈ ℕ)

    val dEq = have(NatDerived.double(n) === n + n).by(Cut(nInℕ, doubleEqAddSelf.of(n := n)))
    val iff1 = have((NatDerived.double(n) === 0) <=> (n + n === 0)).by(Congruence.from(dEq))

    val add0 = have((n + n === 0) <=> ((n === 0) /\ (n === 0))).by(Weakening(NatAlgebra.addEqZeroIff.of(m := n, n := n)))
    val iff2 = have((n + n === 0) <=> (n === 0)).by(Tautology.from(add0))

    have(thesis).by(Tautology.from(iff1, iff2))
  }

  // -------------------------
  // Even/Odd imply nat-membership
  // -------------------------

  /** Lemma: `Even(n) ⟹ n ∈ ℕ`. */
  val evenInℕ = Lemma(Even(n) |- n ∈ ℕ) {
    val ev = assume(Even(n))
    val defEven = have(Even(n) <=> ∃(k, (k ∈ ℕ) /\ (n === NatDerived.double(k)))).by(Restate.from(Even.definition of (x := n)))
    val ex = have(Even(n) |- ∃(k, (k ∈ ℕ) /\ (n === NatDerived.double(k)))).by(Tautology.from(ev, defEven))

    have(∃(k, (k ∈ ℕ) /\ (n === NatDerived.double(k))) |- n ∈ ℕ) subproof {
      assume(∃(k, (k ∈ ℕ) /\ (n === NatDerived.double(k))))

      have((k ∈ ℕ) /\ (n === NatDerived.double(k)) |- n ∈ ℕ) subproof {
        assume((k ∈ ℕ) /\ (n === NatDerived.double(k)))
        val kInℕ = have((k ∈ ℕ) /\ (n === NatDerived.double(k)) |- k ∈ ℕ).by(Tautology)
        val nEq = have((k ∈ ℕ) /\ (n === NatDerived.double(k)) |- n === NatDerived.double(k)).by(Tautology)
        val dkInℕ = have((k ∈ ℕ) /\ (n === NatDerived.double(k)) |- NatDerived.double(k) ∈ ℕ).by(Cut(kInℕ, doubleClosed.of(n := k)))
        have(thesis).by(Congruence.from(nEq, dkInℕ))
      }

      thenHave(thesis).by(LeftExists)
    }

    have(thesis).by(Cut(ex, lastStep))
  }

  /** Lemma: `Odd(n) ⟹ n ∈ ℕ`. */
  val oddInℕ = Lemma(Odd(n) |- n ∈ ℕ) {
    val od = assume(Odd(n))
    val defOdd = have(Odd(n) <=> ∃(k, (k ∈ ℕ) /\ (n === Succ(NatDerived.double(k))))).by(Restate.from(Odd.definition of (x := n)))
    val ex = have(Odd(n) |- ∃(k, (k ∈ ℕ) /\ (n === Succ(NatDerived.double(k))))).by(Tautology.from(od, defOdd))

    have(∃(k, (k ∈ ℕ) /\ (n === Succ(NatDerived.double(k)))) |- n ∈ ℕ) subproof {
      assume(∃(k, (k ∈ ℕ) /\ (n === Succ(NatDerived.double(k)))))

      have((k ∈ ℕ) /\ (n === Succ(NatDerived.double(k))) |- n ∈ ℕ) subproof {
        assume((k ∈ ℕ) /\ (n === Succ(NatDerived.double(k))))
        val kInℕ = have((k ∈ ℕ) /\ (n === Succ(NatDerived.double(k))) |- k ∈ ℕ).by(Tautology)
        val nEq = have((k ∈ ℕ) /\ (n === Succ(NatDerived.double(k))) |- n === Succ(NatDerived.double(k))).by(Tautology)
        val dkInℕ = have((k ∈ ℕ) /\ (n === Succ(NatDerived.double(k))) |- NatDerived.double(k) ∈ ℕ).by(Cut(kInℕ, doubleClosed.of(n := k)))
        val sdkInℕ = have((k ∈ ℕ) /\ (n === Succ(NatDerived.double(k))) |- Succ(NatDerived.double(k)) ∈ ℕ).by(Cut(dkInℕ, Nat.succClosed.of(n := NatDerived.double(k))))
        have(thesis).by(Congruence.from(nEq, sdkInℕ))
      }

      thenHave(thesis).by(LeftExists)
    }

    have(thesis).by(Cut(ex, lastStep))
  }

  /** Lemma: `¬Odd(0)`. */
  val oddZeroFalse = Lemma(¬(Odd(0))) {
    val defOdd0 = have(Odd(0) <=> ∃(k, (k ∈ ℕ) /\ (0 === Succ(NatDerived.double(k))))).by(Restate.from(Odd.definition of (x := 0)))
    have(∃(k, (k ∈ ℕ) /\ (0 === Succ(NatDerived.double(k)))) |- ⊥) subproof {
      assume(∃(k, (k ∈ ℕ) /\ (0 === Succ(NatDerived.double(k)))))

      have((k ∈ ℕ) /\ (0 === Succ(NatDerived.double(k))) |- ⊥) subproof {
        assume((k ∈ ℕ) /\ (0 === Succ(NatDerived.double(k))))
        val kInℕ = have((k ∈ ℕ) /\ (0 === Succ(NatDerived.double(k))) |- k ∈ ℕ).by(Tautology)
        val dkInℕ = have((k ∈ ℕ) /\ (0 === Succ(NatDerived.double(k))) |- NatDerived.double(k) ∈ ℕ).by(Cut(kInℕ, doubleClosed.of(n := k)))
        val eq0 = have((k ∈ ℕ) /\ (0 === Succ(NatDerived.double(k))) |- 0 === Succ(NatDerived.double(k))).by(Tautology)
        val ne0 = have((k ∈ ℕ) /\ (0 === Succ(NatDerived.double(k))) |- ¬(0 === Succ(NatDerived.double(k)))).by(
          Cut(dkInℕ, Nat.zeroNeSucc.of(n := NatDerived.double(k)))
        )
        have(thesis).by(Tautology.from(eq0, ne0))
      }

      thenHave(thesis).by(LeftExists)
    }

    have(thesis).by(Tautology.from(defOdd0, lastStep))
  }

  // -------------------------
  // Double algebra (Isabelle/HOL: Parity.thy style)
  // -------------------------

  /** Theorem: `double(m) + double(n) = double(m + n)` (for naturals). */
  val doubleAdd = Theorem((m ∈ ℕ, n ∈ ℕ) |- (NatDerived.double(m) + NatDerived.double(n) === NatDerived.double(m + n))) {
    val mInℕ = assume(m ∈ ℕ)
    val nInℕ = assume(n ∈ ℕ)

    val dm = have(NatDerived.double(m) === m + m).by(Tautology.from(doubleEqAddSelf.of(n := m), mInℕ))
    val dn = have(NatDerived.double(n) === n + n).by(Tautology.from(doubleEqAddSelf.of(n := n), nInℕ))

    val lhs0 = have(NatDerived.double(m) + NatDerived.double(n) === (m + m) + (n + n)).by(Congruence.from(dm, dn))

    val nnInℕ = have((n + n) ∈ ℕ).by(Tautology.from(Nat.addClosed.of(m := n, n := n), nInℕ, nInℕ))
    val assoc1 = have((m + m) + (n + n) === m + (m + (n + n))).by(Tautology.from(NatAlgebra.addAssoc.of(a := m, b := m, c := (n + n)), mInℕ, mInℕ, nnInℕ))

    val mnInℕ = have((m + n) ∈ ℕ).by(Tautology.from(Nat.addClosed.of(m := m, n := n), mInℕ, nInℕ))
    val mnnEq = have(m + (n + n) === n + (m + n)).by(Tautology.from(NatAlgebra.addLeftComm.of(a := m, b := n, c := n), mInℕ, nInℕ, nInℕ))
    val mid = have(m + (m + (n + n)) === m + (n + (m + n))).by(Congruence.from(mnnEq))

    val assoc2 = have((m + n) + (m + n) === m + (n + (m + n))).by(Tautology.from(NatAlgebra.addAssoc.of(a := m, b := n, c := (m + n)), mInℕ, nInℕ, mnInℕ))
    val assoc2sym = have(m + (n + (m + n)) === (m + n) + (m + n)).by(Congruence.from(assoc2))

    val eq1 = have(NatDerived.double(m) + NatDerived.double(n) === (m + n) + (m + n)).by(Congruence.from(lhs0, assoc1, mid, assoc2sym))

    val mnInℕ2 = have((m + n) ∈ ℕ).by(Weakening(mnInℕ))
    val dmn = have(NatDerived.double(m + n) === (m + n) + (m + n)).by(Cut(mnInℕ2, doubleEqAddSelf.of(n := (m + n))))
    val dmnSym = have((m + n) + (m + n) === NatDerived.double(m + n)).by(Congruence.from(dmn))

    have(thesis).by(Congruence.from(eq1, dmnSym))
  }

  // -------------------------
  // Parity and addition (closure lemmas)
  // -------------------------

  /** Lemma: `Even(m) ∧ Even(n) ⟹ Even(m + n)`. */
  val evenAddEven = Lemma((Even(m), Even(n)) |- Even(m + n)) {
    val em = assume(Even(m))
    val en = assume(Even(n))

    val defEvenM = have(Even(m) <=> ∃(k, (k ∈ ℕ) /\ (m === NatDerived.double(k)))).by(Restate.from(Even.definition of (x := m)))
    val defEvenN = have(Even(n) <=> ∃(k, (k ∈ ℕ) /\ (n === NatDerived.double(k)))).by(Restate.from(Even.definition of (x := n)))

    val exM = have(∃(k, (k ∈ ℕ) /\ (m === NatDerived.double(k)))).by(Tautology.from(em, defEvenM))
    val exN = have(∃(k, (k ∈ ℕ) /\ (n === NatDerived.double(k)))).by(Tautology.from(en, defEvenN))

    val step = have((∃(k, (k ∈ ℕ) /\ (m === NatDerived.double(k))), ∃(k, (k ∈ ℕ) /\ (n === NatDerived.double(k)))) |- Even(m + n)) subproof {
      assume(∃(k, (k ∈ ℕ) /\ (m === NatDerived.double(k))))
      assume(∃(k, (k ∈ ℕ) /\ (n === NatDerived.double(k))))

      have((k ∈ ℕ) /\ (m === NatDerived.double(k)) |- Even(m + n)) subproof {
        assume((k ∈ ℕ) /\ (m === NatDerived.double(k)))
        val kInℕ = have((k ∈ ℕ) /\ (m === NatDerived.double(k)) |- k ∈ ℕ).by(Tautology)
        val mEq = have((k ∈ ℕ) /\ (m === NatDerived.double(k)) |- m === NatDerived.double(k)).by(Tautology)

        have((k0 ∈ ℕ) /\ (n === NatDerived.double(k0)) |- Even(m + n)) subproof {
          assume((k0 ∈ ℕ) /\ (n === NatDerived.double(k0)))
          val k0Inℕ = have((k0 ∈ ℕ) /\ (n === NatDerived.double(k0)) |- k0 ∈ ℕ).by(Tautology)
          val nEq = have((k0 ∈ ℕ) /\ (n === NatDerived.double(k0)) |- n === NatDerived.double(k0)).by(Tautology)

          val kk0Inℕ = have((k + k0) ∈ ℕ).by(Tautology.from(Nat.addClosed.of(m := k, n := k0), kInℕ, k0Inℕ))
          val sumEq = have(m + n === NatDerived.double(k) + NatDerived.double(k0)).by(Congruence.from(mEq, nEq))
          val dAdd = have(NatDerived.double(k) + NatDerived.double(k0) === NatDerived.double(k + k0)).by(Tautology.from(doubleAdd.of(m := k, n := k0), kInℕ, k0Inℕ))
          val sumEq2 = have(m + n === NatDerived.double(k + k0)).by(Congruence.from(sumEq, dAdd))

          val conj = have((k + k0) ∈ ℕ /\ ((m + n) === NatDerived.double(k + k0))).by(Tautology.from(kk0Inℕ, sumEq2))
          val ex = thenHave(∃(k, (k ∈ ℕ) /\ ((m + n) === NatDerived.double(k)))).by(RightExists)
          val defEvenSum = have(Even(m + n) <=> ∃(k, (k ∈ ℕ) /\ ((m + n) === NatDerived.double(k)))).by(Restate.from(Even.definition of (x := (m + n))))
          have(thesis).by(Tautology.from(defEvenSum, ex))
        }

        thenHave((k0 ∈ ℕ) /\ (n === NatDerived.double(k0)) |- Even(m + n)).by(Weakening)
        thenHave(∃(k0, (k0 ∈ ℕ) /\ (n === NatDerived.double(k0))) |- Even(m + n)).by(LeftExists)
      }

      thenHave(∃(k, (k ∈ ℕ) /\ (m === NatDerived.double(k))) |- Even(m + n)).by(LeftExists)
    }

    have(thesis).by(Tautology.from(step, exM, exN))
  }

  /** Lemma: `Even(m) ∧ Odd(n) ⟹ Odd(m + n)`. */
  val evenAddOdd = Lemma((Even(m), Odd(n)) |- Odd(m + n)) {
    val em = assume(Even(m))
    val on = assume(Odd(n))

    val defEvenM = have(Even(m) <=> ∃(k, (k ∈ ℕ) /\ (m === NatDerived.double(k)))).by(Restate.from(Even.definition of (x := m)))
    val defOddN = have(Odd(n) <=> ∃(k, (k ∈ ℕ) /\ (n === Succ(NatDerived.double(k))))).by(Restate.from(Odd.definition of (x := n)))
    val exM = have(∃(k, (k ∈ ℕ) /\ (m === NatDerived.double(k)))).by(Tautology.from(em, defEvenM))
    val exN = have(∃(k, (k ∈ ℕ) /\ (n === Succ(NatDerived.double(k))))).by(Tautology.from(on, defOddN))

    val step = have((∃(k, (k ∈ ℕ) /\ (m === NatDerived.double(k))), ∃(k, (k ∈ ℕ) /\ (n === Succ(NatDerived.double(k))))) |- Odd(m + n)) subproof {
      assume(∃(k, (k ∈ ℕ) /\ (m === NatDerived.double(k))))
      assume(∃(k, (k ∈ ℕ) /\ (n === Succ(NatDerived.double(k)))))

      have((k ∈ ℕ) /\ (m === NatDerived.double(k)) |- Odd(m + n)) subproof {
        assume((k ∈ ℕ) /\ (m === NatDerived.double(k)))
        val kInℕ = have((k ∈ ℕ) /\ (m === NatDerived.double(k)) |- k ∈ ℕ).by(Tautology)
        val mEq = have((k ∈ ℕ) /\ (m === NatDerived.double(k)) |- m === NatDerived.double(k)).by(Tautology)

        have((k0 ∈ ℕ) /\ (n === Succ(NatDerived.double(k0))) |- Odd(m + n)) subproof {
          assume((k0 ∈ ℕ) /\ (n === Succ(NatDerived.double(k0))))
          val k0Inℕ = have((k0 ∈ ℕ) /\ (n === Succ(NatDerived.double(k0))) |- k0 ∈ ℕ).by(Tautology)
          val nEq = have((k0 ∈ ℕ) /\ (n === Succ(NatDerived.double(k0))) |- n === Succ(NatDerived.double(k0))).by(Tautology)

          val kk0Inℕ = have((k + k0) ∈ ℕ).by(Tautology.from(Nat.addClosed.of(m := k, n := k0), kInℕ, k0Inℕ))
          val sumEq = have(m + n === NatDerived.double(k) + Succ(NatDerived.double(k0))).by(Congruence.from(mEq, nEq))
          val rhs = have(NatDerived.double(k) + Succ(NatDerived.double(k0)) === Succ(NatDerived.double(k) + NatDerived.double(k0))).by(
            Cut(have(NatDerived.double(k0) ∈ ℕ).by(Cut(k0Inℕ, doubleClosed.of(n := k0))), Nat.addSucc.of(m := NatDerived.double(k), n := NatDerived.double(k0)))
          )
          val dAdd = have(NatDerived.double(k) + NatDerived.double(k0) === NatDerived.double(k + k0)).by(Tautology.from(doubleAdd.of(m := k, n := k0), kInℕ, k0Inℕ))
          val rhs2 = have(Succ(NatDerived.double(k) + NatDerived.double(k0)) === Succ(NatDerived.double(k + k0))).by(Congruence.from(dAdd))
          val sumEq2 = have(m + n === Succ(NatDerived.double(k + k0))).by(Congruence.from(sumEq, rhs, rhs2))

          val conj = have((k + k0) ∈ ℕ /\ ((m + n) === Succ(NatDerived.double(k + k0)))).by(Tautology.from(kk0Inℕ, sumEq2))
          val ex = thenHave(∃(k, (k ∈ ℕ) /\ ((m + n) === Succ(NatDerived.double(k))))).by(RightExists)
          val defOddSum = have(Odd(m + n) <=> ∃(k, (k ∈ ℕ) /\ ((m + n) === Succ(NatDerived.double(k))))).by(Restate.from(Odd.definition of (x := (m + n))))
          have(thesis).by(Tautology.from(defOddSum, ex))
        }

        thenHave(∃(k0, (k0 ∈ ℕ) /\ (n === Succ(NatDerived.double(k0))) ) |- Odd(m + n)).by(LeftExists)
      }

      thenHave(∃(k, (k ∈ ℕ) /\ (m === NatDerived.double(k))) |- Odd(m + n)).by(LeftExists)
    }

    have(thesis).by(Tautology.from(step, exM, exN))
  }

  /** Lemma: `Odd(m) ∧ Even(n) ⟹ Odd(m + n)`. */
  val oddAddEven = Lemma((Odd(m), Even(n)) |- Odd(m + n)) {
    val om = assume(Odd(m))
    val en = assume(Even(n))
    val mInℕ = have(m ∈ ℕ).by(Tautology.from(oddInℕ.of(n := m), om))
    val nInℕ = have(n ∈ ℕ).by(Tautology.from(evenInℕ.of(n := n), en))

    val comm = have(m + n === n + m).by(Tautology.from(NatAlgebra.addComm.of(m := m, n := n), mInℕ, nInℕ))
    val oddSwapped = have(Odd(n + m)).by(Tautology.from(evenAddOdd.of(m := n, n := m), en, om))
    have(thesis).by(Congruence.from(comm, oddSwapped))
  }

  /** Lemma: `Odd(m) ∧ Odd(n) ⟹ Even(m + n)`. */
  val oddAddOdd = Lemma((Odd(m), Odd(n)) |- Even(m + n)) {
    val om = assume(Odd(m))
    val on = assume(Odd(n))

    val defOddM = have(Odd(m) <=> ∃(k, (k ∈ ℕ) /\ (m === Succ(NatDerived.double(k))))).by(Restate.from(Odd.definition of (x := m)))
    val defOddN = have(Odd(n) <=> ∃(k, (k ∈ ℕ) /\ (n === Succ(NatDerived.double(k))))).by(Restate.from(Odd.definition of (x := n)))
    val exM = have(∃(k, (k ∈ ℕ) /\ (m === Succ(NatDerived.double(k))))).by(Tautology.from(om, defOddM))
    val exN = have(∃(k, (k ∈ ℕ) /\ (n === Succ(NatDerived.double(k))))).by(Tautology.from(on, defOddN))

    val step = have((∃(k, (k ∈ ℕ) /\ (m === Succ(NatDerived.double(k)))), ∃(k, (k ∈ ℕ) /\ (n === Succ(NatDerived.double(k))))) |- Even(m + n)) subproof {
      assume(∃(k, (k ∈ ℕ) /\ (m === Succ(NatDerived.double(k)))))
      assume(∃(k, (k ∈ ℕ) /\ (n === Succ(NatDerived.double(k)))))

      have((k ∈ ℕ) /\ (m === Succ(NatDerived.double(k))) |- Even(m + n)) subproof {
        assume((k ∈ ℕ) /\ (m === Succ(NatDerived.double(k))))
        val kInℕ = have((k ∈ ℕ) /\ (m === Succ(NatDerived.double(k))) |- k ∈ ℕ).by(Tautology)
        val mEq = have((k ∈ ℕ) /\ (m === Succ(NatDerived.double(k))) |- m === Succ(NatDerived.double(k))).by(Tautology)

        have((k0 ∈ ℕ) /\ (n === Succ(NatDerived.double(k0))) |- Even(m + n)) subproof {
          assume((k0 ∈ ℕ) /\ (n === Succ(NatDerived.double(k0))))
          val k0Inℕ = have((k0 ∈ ℕ) /\ (n === Succ(NatDerived.double(k0))) |- k0 ∈ ℕ).by(Tautology)
          val nEq = have((k0 ∈ ℕ) /\ (n === Succ(NatDerived.double(k0))) |- n === Succ(NatDerived.double(k0))).by(Tautology)

          val dk0Inℕ = have(NatDerived.double(k0) ∈ ℕ).by(Tautology.from(doubleClosed.of(n := k0), k0Inℕ))
          val sdk0Inℕ = have(Succ(NatDerived.double(k0)) ∈ ℕ).by(Tautology.from(Nat.succClosed.of(n := NatDerived.double(k0)), dk0Inℕ))
          val dkInℕ = have(NatDerived.double(k) ∈ ℕ).by(Tautology.from(doubleClosed.of(n := k), kInℕ))
          val sdkInℕ = have(Succ(NatDerived.double(k)) ∈ ℕ).by(Tautology.from(Nat.succClosed.of(n := NatDerived.double(k)), dkInℕ))

          val sumEq0 = have(m + n === Succ(NatDerived.double(k)) + Succ(NatDerived.double(k0))).by(Congruence.from(mEq, nEq))

          val abInℕ = have((k + k0) ∈ ℕ).by(Tautology.from(Nat.addClosed.of(m := k, n := k0), kInℕ, k0Inℕ))
          val dAdd = have(NatDerived.double(k) + NatDerived.double(k0) === NatDerived.double(k + k0)).by(Tautology.from(doubleAdd.of(m := k, n := k0), kInℕ, k0Inℕ))

          val succLeft = have(Succ(NatDerived.double(k)) + Succ(NatDerived.double(k0)) === Succ(NatDerived.double(k) + Succ(NatDerived.double(k0)))).by(
            Tautology.from(NatAlgebra.addSuccLeft.of(m := NatDerived.double(k), n := Succ(NatDerived.double(k0))), sdk0Inℕ)
          )
          val succRight = have(NatDerived.double(k) + Succ(NatDerived.double(k0)) === Succ(NatDerived.double(k) + NatDerived.double(k0))).by(
            Tautology.from(NatAlgebra.addSuccRight.of(m := NatDerived.double(k), n := NatDerived.double(k0)), dk0Inℕ)
          )
          val succ2 = have(Succ(NatDerived.double(k)) + Succ(NatDerived.double(k0)) === Succ(Succ(NatDerived.double(k) + NatDerived.double(k0)))).by(
            Congruence.from(succLeft, succRight)
          )

          val succ2b = have(Succ(Succ(NatDerived.double(k) + NatDerived.double(k0))) === Succ(Succ(NatDerived.double(k + k0)))).by(Congruence.from(dAdd))

          val dSucc = have(NatDerived.double(Succ(k + k0)) === Succ(Succ(NatDerived.double(k + k0)))).by(
            Tautology.from(NatDerived.doubleSucc.of(n := (k + k0)), abInℕ)
          )
          val dSuccSym = have(Succ(Succ(NatDerived.double(k + k0))) === NatDerived.double(Succ(k + k0))).by(Congruence.from(dSucc))

          val rhsEq = have(Succ(NatDerived.double(k)) + Succ(NatDerived.double(k0)) === NatDerived.double(Succ(k + k0))).by(
            Congruence.from(succ2, succ2b, dSuccSym)
          )

          val sumEq1 = have(m + n === NatDerived.double(Succ(k + k0))).by(Congruence.from(sumEq0, rhsEq))
          val skk0Inℕ = have(Succ(k + k0) ∈ ℕ).by(Tautology.from(Nat.succClosed.of(n := (k + k0)), abInℕ))

          val conj = have(Succ(k + k0) ∈ ℕ /\ ((m + n) === NatDerived.double(Succ(k + k0)))).by(Tautology.from(skk0Inℕ, sumEq1))
          val ex = thenHave(∃(k, (k ∈ ℕ) /\ ((m + n) === NatDerived.double(k)))).by(RightExists)
          val defEvenSum = have(Even(m + n) <=> ∃(k, (k ∈ ℕ) /\ ((m + n) === NatDerived.double(k)))).by(Restate.from(Even.definition of (x := (m + n))))
          have(thesis).by(Tautology.from(defEvenSum, ex))
        }

        thenHave(∃(k0, (k0 ∈ ℕ) /\ (n === Succ(NatDerived.double(k0)))) |- Even(m + n)).by(LeftExists)
      }

      thenHave(∃(k, (k ∈ ℕ) /\ (m === Succ(NatDerived.double(k)))) |- Even(m + n)).by(LeftExists)
    }

    have(thesis).by(Tautology.from(step, exM, exN))
  }

  // -------------------------
  // Parity: basic facts
  // -------------------------

  /** Lemma: `Even(0)`. */
  val evenZero = Lemma(Even(0)) {
    val d0 = have(NatDerived.double(0) === 0).by(Restate.from(NatDerived.doubleZero))
    val eq = have(0 === NatDerived.double(0)).by(Congruence.from(d0))
    val conj = have((0 ∈ ℕ) /\ (0 === NatDerived.double(0))).by(Tautology.from(Nat.zeroInℕ, eq))
    val ex = thenHave(∃(k, (k ∈ ℕ) /\ (0 === NatDerived.double(k)))).by(RightExists)

    val defEven0 = have(Even(0) <=> ∃(k, (k ∈ ℕ) /\ (0 === NatDerived.double(k)))).by(Restate.from(Even.definition of (x := 0)))
    have(thesis).by(Tautology.from(defEven0, ex))
  }

  /** Lemma: `Odd(1)` (i.e. `Odd(Succ(0))`). */
  val oddOne = Lemma(Odd(1)) {
    val d0 = have(NatDerived.double(0) === 0).by(Restate.from(NatDerived.doubleZero))
    val oneEq = have(1 === Succ(NatDerived.double(0))).by(Congruence.from(d0))
    val conj = have((0 ∈ ℕ) /\ (1 === Succ(NatDerived.double(0)))).by(Tautology.from(Nat.zeroInℕ, oneEq))
    val ex = thenHave(∃(k, (k ∈ ℕ) /\ (1 === Succ(NatDerived.double(k))))).by(RightExists)

    val defOdd1 = have(Odd(1) <=> ∃(k, (k ∈ ℕ) /\ (1 === Succ(NatDerived.double(k))))).by(Restate.from(Odd.definition of (x := 1)))
    have(thesis).by(Tautology.from(defOdd1, ex))
  }

  /** Lemma: `n ∈ ℕ ⇒ Even(double(n))`. */
  val evenDouble = Lemma(n ∈ ℕ |- Even(NatDerived.double(n))) {
    val nInℕ = assume(n ∈ ℕ)
    val refl = have(NatDerived.double(n) === NatDerived.double(n)).by(Restate)
    val conj = have((n ∈ ℕ) /\ (NatDerived.double(n) === NatDerived.double(n))).by(Tautology.from(nInℕ, refl))
    val ex = thenHave(∃(k, (k ∈ ℕ) /\ (NatDerived.double(n) === NatDerived.double(k)))).by(RightExists)

    val defEven = have(Even(NatDerived.double(n)) <=> ∃(k, (k ∈ ℕ) /\ (NatDerived.double(n) === NatDerived.double(k)))).by(
      Restate.from(Even.definition of (x := NatDerived.double(n)))
    )
    have(thesis).by(Tautology.from(defEven, ex))
  }

  /** Lemma: `n ∈ ℕ ⇒ Odd(Succ(double(n)))`. */
  val oddSuccDouble = Lemma(n ∈ ℕ |- Odd(Succ(NatDerived.double(n)))) {
    val nInℕ = assume(n ∈ ℕ)
    val refl = have(Succ(NatDerived.double(n)) === Succ(NatDerived.double(n))).by(Restate)
    val conj = have((n ∈ ℕ) /\ (Succ(NatDerived.double(n)) === Succ(NatDerived.double(n)))).by(Tautology.from(nInℕ, refl))
    val ex = thenHave(∃(k, (k ∈ ℕ) /\ (Succ(NatDerived.double(n)) === Succ(NatDerived.double(k))))).by(RightExists)

    val defOdd = have(Odd(Succ(NatDerived.double(n))) <=> ∃(k, (k ∈ ℕ) /\ (Succ(NatDerived.double(n)) === Succ(NatDerived.double(k))))).by(
      Restate.from(Odd.definition of (x := Succ(NatDerived.double(n))))
    )
    have(thesis).by(Tautology.from(defOdd, ex))
  }

  /** Lemma: `Even(n) ⟹ Odd(Succ(n))`. */
  val evenToOddSucc = Lemma(Even(n) |- Odd(Succ(n))) {
    val ev = assume(Even(n))

    val defEven = have(Even(n) <=> ∃(k, (k ∈ ℕ) /\ (n === NatDerived.double(k)))).by(Restate.from(Even.definition of (x := n)))
    val defOdd = have(Odd(Succ(n)) <=> ∃(k, (k ∈ ℕ) /\ (Succ(n) === Succ(NatDerived.double(k))))).by(
      Restate.from(Odd.definition of (x := Succ(n)))
    )

    val ex = have(Even(n) |- ∃(k, (k ∈ ℕ) /\ (n === NatDerived.double(k)))).by(Tautology.from(ev, defEven))

    val lift = have(∃(k, (k ∈ ℕ) /\ (n === NatDerived.double(k))) |- Odd(Succ(n))) subproof {
      assume(∃(k, (k ∈ ℕ) /\ (n === NatDerived.double(k))))

      have((k ∈ ℕ) /\ (n === NatDerived.double(k)) |- Odd(Succ(n))) subproof {
        assume((k ∈ ℕ) /\ (n === NatDerived.double(k)))

        val kInℕ = have((k ∈ ℕ) /\ (n === NatDerived.double(k)) |- k ∈ ℕ).by(Tautology)
        val nEqDk = have((k ∈ ℕ) /\ (n === NatDerived.double(k)) |- n === NatDerived.double(k)).by(Tautology)
        val snEq = have((k ∈ ℕ) /\ (n === NatDerived.double(k)) |- Succ(n) === Succ(NatDerived.double(k))).by(Congruence.from(nEqDk))
        val conj = have((k ∈ ℕ) /\ (n === NatDerived.double(k)) |- (k ∈ ℕ) /\ (Succ(n) === Succ(NatDerived.double(k)))).by(
          Tautology.from(kInℕ, snEq)
        )
        val ex2 = thenHave((k ∈ ℕ) /\ (n === NatDerived.double(k)) |- ∃(k, (k ∈ ℕ) /\ (Succ(n) === Succ(NatDerived.double(k))))).by(
          RightExists
        )
        have(thesis).by(Tautology.from(defOdd, ex2))
      }

      thenHave(∃(k, (k ∈ ℕ) /\ (n === NatDerived.double(k))) |- Odd(Succ(n))).by(LeftExists)
    }

    have(thesis).by(Cut(ex, lift))
  }

  /** Lemma: `Odd(n) ⟹ Even(Succ(n))`. */
  val oddToEvenSucc = Lemma(Odd(n) |- Even(Succ(n))) {
    val od = assume(Odd(n))

    val defOdd = have(Odd(n) <=> ∃(k, (k ∈ ℕ) /\ (n === Succ(NatDerived.double(k))))).by(Restate.from(Odd.definition of (x := n)))
    val defEven = have(Even(Succ(n)) <=> ∃(k, (k ∈ ℕ) /\ (Succ(n) === NatDerived.double(k)))).by(
      Restate.from(Even.definition of (x := Succ(n)))
    )

    val ex = have(Odd(n) |- ∃(k, (k ∈ ℕ) /\ (n === Succ(NatDerived.double(k))))).by(Tautology.from(od, defOdd))

    val lift = have(∃(k, (k ∈ ℕ) /\ (n === Succ(NatDerived.double(k)))) |- Even(Succ(n))) subproof {
      assume(∃(k, (k ∈ ℕ) /\ (n === Succ(NatDerived.double(k)))))

      have((k ∈ ℕ) /\ (n === Succ(NatDerived.double(k))) |- Even(Succ(n))) subproof {
        assume((k ∈ ℕ) /\ (n === Succ(NatDerived.double(k))))

        val kInℕ = have((k ∈ ℕ) /\ (n === Succ(NatDerived.double(k))) |- k ∈ ℕ).by(Tautology)
        val nEq = have((k ∈ ℕ) /\ (n === Succ(NatDerived.double(k))) |- n === Succ(NatDerived.double(k))).by(Tautology)
        val snEq = have((k ∈ ℕ) /\ (n === Succ(NatDerived.double(k))) |- Succ(n) === Succ(Succ(NatDerived.double(k)))).by(Congruence.from(nEq))

        val dkInℕ = have((k ∈ ℕ) /\ (n === Succ(NatDerived.double(k))) |- NatDerived.double(k) ∈ ℕ).by(Cut(kInℕ, doubleClosed.of(n := k)))
        val skInℕ = have((k ∈ ℕ) /\ (n === Succ(NatDerived.double(k))) |- Succ(k) ∈ ℕ).by(Cut(kInℕ, Nat.succClosed.of(n := k)))
        val rhs = Succ(Succ(NatDerived.double(k)))
        val dSucc = have((k ∈ ℕ) /\ (n === Succ(NatDerived.double(k))) |- NatDerived.double(Succ(k)) === rhs).by(
          Cut(kInℕ, NatDerived.doubleSucc.of(n := k))
        )

        val snEq2 = have((k ∈ ℕ) /\ (n === Succ(NatDerived.double(k))) |- Succ(n) === NatDerived.double(Succ(k))).by(Congruence.from(snEq, dSucc))

        val conj = have((k ∈ ℕ) /\ (n === Succ(NatDerived.double(k))) |- (Succ(k) ∈ ℕ) /\ (Succ(n) === NatDerived.double(Succ(k)))).by(
          Tautology.from(skInℕ, snEq2)
        )
        val ex2 = thenHave((k ∈ ℕ) /\ (n === Succ(NatDerived.double(k))) |- ∃(k, (k ∈ ℕ) /\ (Succ(n) === NatDerived.double(k)))).by(
          RightExists
        )
        have(thesis).by(Tautology.from(defEven, ex2))
      }

      thenHave(∃(k, (k ∈ ℕ) /\ (n === Succ(NatDerived.double(k)))) |- Even(Succ(n))).by(LeftExists)
    }

    have(thesis).by(Cut(ex, lift))
  }

  /** Theorem: Every natural is even or odd. */
  val parityExhaustive = Theorem(n ∈ ℕ |- (Even(n) \/ Odd(n))) {
    val ind = Nat.induction of (Pred := λ(n, Even(n) \/ Odd(n)))

    val base = have(Even(0) \/ Odd(0)).by(Tautology.from(evenZero))

    val step = have(∀(n, (n ∈ ℕ) ==> (((Even(n) \/ Odd(n))) ==> (Even(Succ(n)) \/ Odd(Succ(n)))))) subproof {
      have((n ∈ ℕ) ==> (((Even(n) \/ Odd(n))) ==> (Even(Succ(n)) \/ Odd(Succ(n))))) subproof {
        val nInℕ = assume(n ∈ ℕ)
        assume(Even(n) \/ Odd(n))

        val eTo = have(Even(n) |- Odd(Succ(n))).by(Weakening(evenToOddSucc.of(n := n)))
        val oTo = have(Odd(n) |- Even(Succ(n))).by(Weakening(oddToEvenSucc.of(n := n)))

        val caseE = have(Even(n) |- (Even(Succ(n)) \/ Odd(Succ(n)))).by(Tautology.from(eTo))
        val caseO = have(Odd(n) |- (Even(Succ(n)) \/ Odd(Succ(n)))).by(Tautology.from(oTo))

        have(thesis).by(Tautology.from(caseE, caseO, lastStep))
      }
      thenHave(thesis).by(RightForall)
    }

    val all = have(∀(n, (n ∈ ℕ) ==> (Even(n) \/ Odd(n)))).by(Tautology.from(ind, base, step))
    val imp = have((n ∈ ℕ) ==> (Even(n) \/ Odd(n))).by(InstantiateForall(n)(all))
    val nInℕ = assume(n ∈ ℕ)
    have(thesis).by(Tautology.from(imp, nInℕ))
  }

  // -------------------------
  // Parity: successor interaction (Isabelle/HOL `Parity.thy`: `even_Suc`)
  // -------------------------

  /** Theorem: `n ∈ ℕ ⟹ Odd(Succ(n)) <=> Even(n)`. */
  val oddSuccIffEven = Theorem(n ∈ ℕ |- (Odd(Succ(n)) <=> Even(n))) {
    val nInℕ = assume(n ∈ ℕ)

    val dir1 = have(Odd(Succ(n)) ==> Even(n)) subproof {
      assume(Odd(Succ(n)))
      val od = have(Odd(Succ(n))).by(Tautology)
      val defOdd = have(Odd(Succ(n)) <=> ∃(k, (k ∈ ℕ) /\ (Succ(n) === Succ(NatDerived.double(k))))).by(
        Restate.from(Odd.definition of (x := Succ(n)))
      )
      val ex = have(∃(k, (k ∈ ℕ) /\ (Succ(n) === Succ(NatDerived.double(k))))).by(Tautology.from(od, defOdd))

      val toEven = have(∃(k, (k ∈ ℕ) /\ (Succ(n) === Succ(NatDerived.double(k)))) |- Even(n)) subproof {
        assume(∃(k, (k ∈ ℕ) /\ (Succ(n) === Succ(NatDerived.double(k)))))

        have((k ∈ ℕ) /\ (Succ(n) === Succ(NatDerived.double(k))) |- Even(n)) subproof {
          assume((k ∈ ℕ) /\ (Succ(n) === Succ(NatDerived.double(k))))

          val kInℕ = have((k ∈ ℕ) /\ (Succ(n) === Succ(NatDerived.double(k))) |- k ∈ ℕ).by(Tautology)
          val inj = have(Succ(n) === Succ(NatDerived.double(k)) |- n === NatDerived.double(k)).by(
            Tautology.from(Nat.succInjective.of(m := n, n := NatDerived.double(k)))
          )
          val snEq = have((k ∈ ℕ) /\ (Succ(n) === Succ(NatDerived.double(k))) |- Succ(n) === Succ(NatDerived.double(k))).by(Tautology)
          val nEq = have((k ∈ ℕ) /\ (Succ(n) === Succ(NatDerived.double(k))) |- n === NatDerived.double(k)).by(Cut(snEq, inj))
          val sym = have((k ∈ ℕ) /\ (Succ(n) === Succ(NatDerived.double(k))) |- n === NatDerived.double(k)).by(Restate.from(nEq))

          val conj = have((k ∈ ℕ) /\ (Succ(n) === Succ(NatDerived.double(k))) |- (k ∈ ℕ) /\ (n === NatDerived.double(k))).by(
            Tautology.from(kInℕ, sym)
          )
          val ex2 = thenHave((k ∈ ℕ) /\ (Succ(n) === Succ(NatDerived.double(k))) |- ∃(k, (k ∈ ℕ) /\ (n === NatDerived.double(k)))).by(
            RightExists
          )
          val defEven = have(Even(n) <=> ∃(k, (k ∈ ℕ) /\ (n === NatDerived.double(k)))).by(Restate.from(Even.definition of (x := n)))
          have(thesis).by(Tautology.from(defEven, ex2))
        }

        thenHave(∃(k, (k ∈ ℕ) /\ (Succ(n) === Succ(NatDerived.double(k)))) |- Even(n)).by(LeftExists)
      }

      have(Even(n)).by(Cut(ex, toEven))
      thenHave(thesis).by(Restate)
    }

    val dir2 = have(Even(n) ==> Odd(Succ(n))).by(Restate.from(evenToOddSucc.of(n := n)))

    have(thesis).by(Tautology.from(dir1, dir2))
  }

  /** Theorem: `n ∈ ℕ ⟹ Even(Succ(n)) <=> Odd(n)`. */
  val evenSuccIffOdd = Theorem(n ∈ ℕ |- (Even(Succ(n)) <=> Odd(n))) {
    val nInℕ = assume(n ∈ ℕ)

    val dir1 = have(Odd(n) ==> Even(Succ(n))).by(Restate.from(oddToEvenSucc.of(n := n)))

    val dir2 = have(Even(Succ(n)) ==> Odd(n)) subproof {
      assume(Even(Succ(n)))
      val ev = have(Even(Succ(n))).by(Tautology)
      val defEven = have(Even(Succ(n)) <=> ∃(k, (k ∈ ℕ) /\ (Succ(n) === NatDerived.double(k)))).by(
        Restate.from(Even.definition of (x := Succ(n)))
      )
      val ex = have(∃(k, (k ∈ ℕ) /\ (Succ(n) === NatDerived.double(k)))).by(Tautology.from(ev, defEven))

      val toOdd = have(∃(k, (k ∈ ℕ) /\ (Succ(n) === NatDerived.double(k))) |- Odd(n)) subproof {
        assume(∃(k, (k ∈ ℕ) /\ (Succ(n) === NatDerived.double(k))))

        have((k ∈ ℕ) /\ (Succ(n) === NatDerived.double(k)) |- Odd(n)) subproof {
          assume((k ∈ ℕ) /\ (Succ(n) === NatDerived.double(k)))

          val kInℕ = have((k ∈ ℕ) /\ (Succ(n) === NatDerived.double(k)) |- k ∈ ℕ).by(Tautology)
          val snEq = have((k ∈ ℕ) /\ (Succ(n) === NatDerived.double(k)) |- Succ(n) === NatDerived.double(k)).by(Tautology)

          val cases = have((k ∈ ℕ) /\ (Succ(n) === NatDerived.double(k)) |- (k === 0) \/ ∃(m, (m ∈ ℕ) /\ (k === Succ(m)))).by(
            Cut(kInℕ, Nat.natCases.of(n := k))
          )

          val notK0 = have((k ∈ ℕ) /\ (Succ(n) === NatDerived.double(k)) |- ¬(k === 0)) subproof {
            assume(k === 0)
            val d0 = have(NatDerived.double(0) === 0).by(Restate.from(NatDerived.doubleZero))
            val dK0 = have(NatDerived.double(k) === 0).by(Congruence.from(lastStep, d0))
            val snEq0 = have(Succ(n) === 0).by(Congruence.from(snEq, dK0))
            val snNe0 = have(n ∈ ℕ |- (Succ(n) =/= 0)).by(Weakening(Nat.succNeZero.of(n := n)))
            val notSnEq0 = have(¬(Succ(n) === 0)).by(Tautology.from(snNe0, nInℕ))
            have(thesis).by(Tautology.from(snEq0, notSnEq0))
          }

          val succCase = have(∃(m, (m ∈ ℕ) /\ (k === Succ(m))) |- Odd(n)) subproof {
            assume(∃(m, (m ∈ ℕ) /\ (k === Succ(m))))

            have((m ∈ ℕ) /\ (k === Succ(m)) |- Odd(n)) subproof {
              assume((m ∈ ℕ) /\ (k === Succ(m)))
              val mInℕ = have((m ∈ ℕ) /\ (k === Succ(m)) |- m ∈ ℕ).by(Tautology)
              val kEqSm = have((m ∈ ℕ) /\ (k === Succ(m)) |- k === Succ(m)).by(Tautology)
              val dSucc = have((m ∈ ℕ) /\ (k === Succ(m)) |- NatDerived.double(Succ(m)) === Succ(Succ(NatDerived.double(m)))).by(
                Cut(mInℕ, NatDerived.doubleSucc.of(n := m))
              )
              val dK = have((m ∈ ℕ) /\ (k === Succ(m)) |- NatDerived.double(k) === Succ(Succ(NatDerived.double(m)))).by(
                Congruence.from(kEqSm, dSucc)
              )
              val snEq2 = have((m ∈ ℕ) /\ (k === Succ(m)) |- Succ(n) === Succ(Succ(NatDerived.double(m)))).by(
                Congruence.from(snEq, dK)
              )
              val inj = have(Succ(n) === Succ(Succ(NatDerived.double(m))) |- n === Succ(NatDerived.double(m))).by(
                Tautology.from(Nat.succInjective.of(m := n, n := Succ(NatDerived.double(m))))
              )
              val nEq = have((m ∈ ℕ) /\ (k === Succ(m)) |- n === Succ(NatDerived.double(m))).by(Cut(snEq2, inj))

              val conj = have((m ∈ ℕ) /\ (k === Succ(m)) |- (m ∈ ℕ) /\ (n === Succ(NatDerived.double(m)))).by(
                Tautology.from(mInℕ, nEq)
              )
              val ex2 = thenHave((m ∈ ℕ) /\ (k === Succ(m)) |- ∃(k, (k ∈ ℕ) /\ (n === Succ(NatDerived.double(k))))).by(
                RightExists
              )
              val defOdd = have(Odd(n) <=> ∃(k, (k ∈ ℕ) /\ (n === Succ(NatDerived.double(k))))).by(Restate.from(Odd.definition of (x := n)))
              have(thesis).by(Tautology.from(defOdd, ex2))
            }

            thenHave(∃(m, (m ∈ ℕ) /\ (k === Succ(m))) |- Odd(n)).by(LeftExists)
          }

          have(thesis).by(Tautology.from(cases, notK0, succCase))
        }

        thenHave(∃(k, (k ∈ ℕ) /\ (Succ(n) === NatDerived.double(k))) |- Odd(n)).by(LeftExists)
      }

      have(Odd(n)).by(Cut(ex, toOdd))
      thenHave(thesis).by(Restate)
    }

    have(thesis).by(Tautology.from(dir1, dir2))
  }

  // -------------------------
  // Convenience lemmas (Isabelle/HOL `Parity.thy`: `even_plus_one_iff`)
  // -------------------------

  /** Theorem: `n ∈ ℕ ⟹ Even(n + 1) <=> Odd(n)`. */
  val evenPlusOneIff = Theorem(n ∈ ℕ |- (Even(n + 1) <=> Odd(n))) {
    val nInℕ = assume(n ∈ ℕ)
    val eq = have(n + 1 === Succ(n)).by(Cut(nInℕ, NatAlgebra.addOneRight.of(n := n)))
    val iff1 = have(Even(n + 1) <=> Even(Succ(n))).by(Congruence.from(eq))
    val iff2 = have(Even(Succ(n)) <=> Odd(n)).by(Cut(nInℕ, evenSuccIffOdd.of(n := n)))
    have(thesis).by(Tautology.from(iff1, iff2))
  }

  /** Theorem: `n ∈ ℕ ⟹ Odd(n + 1) <=> Even(n)`. */
  val oddPlusOneIff = Theorem(n ∈ ℕ |- (Odd(n + 1) <=> Even(n))) {
    val nInℕ = assume(n ∈ ℕ)
    val eq = have(n + 1 === Succ(n)).by(Cut(nInℕ, NatAlgebra.addOneRight.of(n := n)))
    val iff1 = have(Odd(n + 1) <=> Odd(Succ(n))).by(Congruence.from(eq))
    val iff2 = have(Odd(Succ(n)) <=> Even(n)).by(Cut(nInℕ, oddSuccIffEven.of(n := n)))
    have(thesis).by(Tautology.from(iff1, iff2))
  }

  // -------------------------
  // Parity cases (derived)
  // -------------------------

  /** Theorem: parity case split (derived from `parityExhaustive`). */
  val parityCases = Theorem((n ∈ ℕ, Even(n) ==> P0, Odd(n) ==> P0) |- P0) {
    val nInℕ = assume(n ∈ ℕ)
    val evCase = assume(Even(n) ==> P0)
    val odCase = assume(Odd(n) ==> P0)

    val split = have(Even(n) \/ Odd(n)).by(Weakening(parityExhaustive.of(n := n)))
    have(thesis).by(Tautology.from(split, evCase, odCase))
  }

  // -------------------------
  // Even/Odd are disjoint on ℕ
  // -------------------------

  /** Theorem: `n ∈ ℕ ⟹ ¬(Even(n) ∧ Odd(n))`. */
  val evenOddDisjoint = Theorem(n ∈ ℕ |- ¬(Even(n) /\ Odd(n))) {
    val ind = Nat.induction of (Pred := λ(n, ¬(Even(n) /\ Odd(n))))

    val base = have(¬(Even(0) /\ Odd(0))) subproof {
      val ev0 = have(Even(0)).by(Tautology.from(evenZero))
      val no0 = have(¬(Odd(0))).by(Tautology.from(oddZeroFalse))
      have((Even(0) /\ Odd(0)) |- ⊥) subproof {
        assume(Even(0) /\ Odd(0))
        val od0 = have(Even(0) /\ Odd(0) |- Odd(0)).by(Tautology)
        have(thesis).by(Tautology.from(od0, no0))
      }
      thenHave(thesis).by(Restate)
    }

    val step = have(∀(n, (n ∈ ℕ) ==> (¬(Even(n) /\ Odd(n)) ==> ¬(Even(Succ(n)) /\ Odd(Succ(n)))))) subproof {
      have((n ∈ ℕ) ==> (¬(Even(n) /\ Odd(n)) ==> ¬(Even(Succ(n)) /\ Odd(Succ(n))))) subproof {
        val nInℕ = assume(n ∈ ℕ)
        val IH = assume(¬(Even(n) /\ Odd(n)))

        val iffEvenSucc = have(Even(Succ(n)) <=> Odd(n)).by(Tautology.from(evenSuccIffOdd.of(n := n), nInℕ))
        val iffOddSucc = have(Odd(Succ(n)) <=> Even(n)).by(Tautology.from(oddSuccIffEven.of(n := n), nInℕ))

        have(Even(Succ(n)) /\ Odd(Succ(n)) |- ⊥) subproof {
          assume(Even(Succ(n)) /\ Odd(Succ(n)))
          val evSn = have(Even(Succ(n)) /\ Odd(Succ(n)) |- Even(Succ(n))).by(Tautology)
          val odSn = have(Even(Succ(n)) /\ Odd(Succ(n)) |- Odd(Succ(n))).by(Tautology)

          val odN = have(Even(Succ(n)) /\ Odd(Succ(n)) |- Odd(n)).by(Tautology.from(evSn, iffEvenSucc))
          val evN = have(Even(Succ(n)) /\ Odd(Succ(n)) |- Even(n)).by(Tautology.from(odSn, iffOddSucc))
          val both = have(Even(Succ(n)) /\ Odd(Succ(n)) |- (Even(n) /\ Odd(n))).by(Tautology.from(evN, odN))
          have(thesis).by(Tautology.from(both, IH))
        }

        thenHave(thesis).by(Restate)
      }
      thenHave(thesis).by(RightForall)
    }

    val allN = have(∀(n, (n ∈ ℕ) ==> ¬(Even(n) /\ Odd(n)))).by(Tautology.from(ind, base, step))

    val imp = have((n ∈ ℕ) ==> ¬(Even(n) /\ Odd(n))).by(InstantiateForall(n)(allN))
    val nInℕ = assume(n ∈ ℕ)
    have(thesis).by(Tautology.from(imp, nInℕ))
  }

  /** Theorem: `n ∈ ℕ ⟹ (Even(n) ∨ Odd(n)) ∧ ¬(Even(n) ∧ Odd(n))`. */
  val evenOddExclusive = Theorem(n ∈ ℕ |- ((Even(n) \/ Odd(n)) /\ ¬(Even(n) /\ Odd(n)))) {
    val nInℕ = assume(n ∈ ℕ)
    val exh = have(Even(n) \/ Odd(n)).by(Tautology.from(parityExhaustive.of(n := n), nInℕ))
    val disj = have(¬(Even(n) /\ Odd(n))).by(Tautology.from(evenOddDisjoint.of(n := n), nInℕ))
    have(thesis).by(Tautology.from(exh, disj))
  }

  // -------------------------
  // Isabelle/HOL Parity.thy: even_add / odd_add
  // -------------------------

  /** Theorem (Parity.thy `even_add`): `m,n ∈ ℕ ⟹ Even(m+n) ⇔ ((Even(m) ∧ Even(n)) ∨ (Odd(m) ∧ Odd(n)))`. */
  val evenAddIff = Theorem((m ∈ ℕ, n ∈ ℕ) |- (Even(m + n) <=> (((Even(m) /\ Even(n)) \/ (Odd(m) /\ Odd(n)))))) {
    val mInℕ = assume(m ∈ ℕ)
    val nInℕ = assume(n ∈ ℕ)

    // -> direction
    val forward = have(Even(m + n) |- ((Even(m) /\ Even(n)) \/ (Odd(m) /\ Odd(n)))) subproof {
      val evSum = assume(Even(m + n))
      val splitM = have(Even(m) \/ Odd(m)).by(Tautology.from(parityExhaustive.of(n := m), mInℕ))

      val caseEvenM = have(Even(m) |- ((Even(m) /\ Even(n)) \/ (Odd(m) /\ Odd(n)))) subproof {
        val em = assume(Even(m))
        val splitN = have(Even(n) \/ Odd(n)).by(Tautology.from(parityExhaustive.of(n := n), nInℕ))

        have(Odd(n) |- ⊥) subproof {
          val on = assume(Odd(n))
          val oddSum = have(Odd(m + n)).by(Tautology.from(evenAddOdd.of(m := m, n := n), em, on))
          val mnInℕ = have((m + n) ∈ ℕ).by(Tautology.from(Nat.addClosed.of(m := m, n := n), mInℕ, nInℕ))
          val disj = have(¬(Even(m + n) /\ Odd(m + n))).by(Tautology.from(evenOddDisjoint.of(n := (m + n)), mnInℕ))
          val both = have(Even(m + n) /\ Odd(m + n)).by(Tautology.from(evSum, oddSum))
          have(thesis).by(Tautology.from(both, disj))
        }
        val notOddN = thenHave(¬(Odd(n))).by(Restate)
        val en = have(Even(n)).by(Tautology.from(splitN, notOddN))
        have(thesis).by(Tautology.from(em, en))
      }

      val caseOddM = have(Odd(m) |- ((Even(m) /\ Even(n)) \/ (Odd(m) /\ Odd(n)))) subproof {
        val om = assume(Odd(m))
        val splitN = have(Even(n) \/ Odd(n)).by(Tautology.from(parityExhaustive.of(n := n), nInℕ))

        have(Even(n) |- ⊥) subproof {
          val en = assume(Even(n))
          val oddSum = have(Odd(m + n)).by(Tautology.from(oddAddEven.of(m := m, n := n), om, en))
          val mnInℕ = have((m + n) ∈ ℕ).by(Tautology.from(Nat.addClosed.of(m := m, n := n), mInℕ, nInℕ))
          val disj = have(¬(Even(m + n) /\ Odd(m + n))).by(Tautology.from(evenOddDisjoint.of(n := (m + n)), mnInℕ))
          val both = have(Even(m + n) /\ Odd(m + n)).by(Tautology.from(evSum, oddSum))
          have(thesis).by(Tautology.from(both, disj))
        }
        val notEvenN = thenHave(¬(Even(n))).by(Restate)
        val on = have(Odd(n)).by(Tautology.from(splitN, notEvenN))
        have(thesis).by(Tautology.from(om, on))
      }

      have(thesis).by(Tautology.from(splitM, caseEvenM, caseOddM))
    }

    // <- direction
    val backward = have(((Even(m) /\ Even(n)) \/ (Odd(m) /\ Odd(n))) |- Even(m + n)) subproof {
      val split = assume((Even(m) /\ Even(n)) \/ (Odd(m) /\ Odd(n)))
      val caseEE = have((Even(m) /\ Even(n)) |- Even(m + n)).by(Tautology.from(evenAddEven.of(m := m, n := n)))
      val caseOO = have((Odd(m) /\ Odd(n)) |- Even(m + n)).by(Tautology.from(oddAddOdd.of(m := m, n := n)))
      have(thesis).by(Tautology.from(split, caseEE, caseOO))
    }

    have(thesis).by(Tautology.from(forward, backward))
  }

  /** Theorem (Parity.thy `odd_add`): `m,n ∈ ℕ ⟹ Odd(m+n) ⇔ ((Even(m) ∧ Odd(n)) ∨ (Odd(m) ∧ Even(n)))`. */
  val oddAddIff = Theorem((m ∈ ℕ, n ∈ ℕ) |- (Odd(m + n) <=> (((Even(m) /\ Odd(n)) \/ (Odd(m) /\ Even(n)))))) {
    val mInℕ = assume(m ∈ ℕ)
    val nInℕ = assume(n ∈ ℕ)

    // -> direction
    val forward = have(Odd(m + n) |- ((Even(m) /\ Odd(n)) \/ (Odd(m) /\ Even(n)))) subproof {
      val odSum = assume(Odd(m + n))
      val splitM = have(Even(m) \/ Odd(m)).by(Tautology.from(parityExhaustive.of(n := m), mInℕ))

      val caseEvenM = have(Even(m) |- ((Even(m) /\ Odd(n)) \/ (Odd(m) /\ Even(n)))) subproof {
        val em = assume(Even(m))
        val splitN = have(Even(n) \/ Odd(n)).by(Tautology.from(parityExhaustive.of(n := n), nInℕ))

        have(Even(n) |- ⊥) subproof {
          val en = assume(Even(n))
          val evSum = have(Even(m + n)).by(Tautology.from(evenAddEven.of(m := m, n := n), em, en))
          val mnInℕ = have((m + n) ∈ ℕ).by(Tautology.from(Nat.addClosed.of(m := m, n := n), mInℕ, nInℕ))
          val disj = have(¬(Even(m + n) /\ Odd(m + n))).by(Tautology.from(evenOddDisjoint.of(n := (m + n)), mnInℕ))
          val both = have(Even(m + n) /\ Odd(m + n)).by(Tautology.from(evSum, odSum))
          have(thesis).by(Tautology.from(both, disj))
        }
        val notEvenN = thenHave(¬(Even(n))).by(Restate)
        val on = have(Odd(n)).by(Tautology.from(splitN, notEvenN))
        have(thesis).by(Tautology.from(em, on))
      }

      val caseOddM = have(Odd(m) |- ((Even(m) /\ Odd(n)) \/ (Odd(m) /\ Even(n)))) subproof {
        val om = assume(Odd(m))
        val splitN = have(Even(n) \/ Odd(n)).by(Tautology.from(parityExhaustive.of(n := n), nInℕ))

        have(Odd(n) |- ⊥) subproof {
          val on = assume(Odd(n))
          val evSum = have(Even(m + n)).by(Tautology.from(oddAddOdd.of(m := m, n := n), om, on))
          val mnInℕ = have((m + n) ∈ ℕ).by(Tautology.from(Nat.addClosed.of(m := m, n := n), mInℕ, nInℕ))
          val disj = have(¬(Even(m + n) /\ Odd(m + n))).by(Tautology.from(evenOddDisjoint.of(n := (m + n)), mnInℕ))
          val both = have(Even(m + n) /\ Odd(m + n)).by(Tautology.from(evSum, odSum))
          have(thesis).by(Tautology.from(both, disj))
        }
        val notOddN = thenHave(¬(Odd(n))).by(Restate)
        val en = have(Even(n)).by(Tautology.from(splitN, notOddN))
        have(thesis).by(Tautology.from(om, en))
      }

      have(thesis).by(Tautology.from(splitM, caseEvenM, caseOddM))
    }

    // <- direction
    val backward = have(((Even(m) /\ Odd(n)) \/ (Odd(m) /\ Even(n))) |- Odd(m + n)) subproof {
      val split = assume((Even(m) /\ Odd(n)) \/ (Odd(m) /\ Even(n)))
      val caseEO = have((Even(m) /\ Odd(n)) |- Odd(m + n)).by(Tautology.from(evenAddOdd.of(m := m, n := n)))
      val caseOE = have((Odd(m) /\ Even(n)) |- Odd(m + n)).by(Tautology.from(oddAddEven.of(m := m, n := n)))
      have(thesis).by(Tautology.from(split, caseEO, caseOE))
    }

    have(thesis).by(Tautology.from(forward, backward))
  }

  // -------------------------
  // Parity and multiplication (Parity.thy: even_mult_iff)
  // -------------------------

  /** Lemma: `double(m) * n = double(m*n)` for naturals. */
  val doubleMulRight = Theorem((m ∈ ℕ, n ∈ ℕ) |- (NatDerived.double(m) * n === NatDerived.double(m * n))) {
    val mInℕ = assume(m ∈ ℕ)
    val nInℕ = assume(n ∈ ℕ)

    val dm = have(NatDerived.double(m) === m + m).by(Tautology.from(doubleEqAddSelf.of(n := m), mInℕ))
    val lhs0 = have(NatDerived.double(m) * n === (m + m) * n).by(Congruence.from(dm))

    val dist = have((m + m) * n === (m * n) + (m * n)).by(Tautology.from(NatAlgebra.mulDistribRight.of(a := m, b := m, c := n), mInℕ, mInℕ, nInℕ))
    val mnInℕ = have((m * n) ∈ ℕ).by(Tautology.from(Nat.mulClosed.of(m := m, n := n), mInℕ, nInℕ))
    val dmn = have(NatDerived.double(m * n) === (m * n) + (m * n)).by(Tautology.from(doubleEqAddSelf.of(n := (m * n)), mnInℕ))
    val rhs = have((m * n) + (m * n) === NatDerived.double(m * n)).by(Congruence.from(dmn))

    have(thesis).by(Congruence.from(lhs0, dist, rhs))
  }

  /** Lemma: `Even(m) ∧ n∈ℕ ⟹ Even(m*n)`. */
  val evenMulLeft = Lemma((Even(m), n ∈ ℕ) |- Even(m * n)) {
    val em = assume(Even(m))
    val nInℕ = assume(n ∈ ℕ)
    val defEvenM = have(Even(m) <=> ∃(k, (k ∈ ℕ) /\ (m === NatDerived.double(k)))).by(Restate.from(Even.definition of (x := m)))
    val exM = have(∃(k, (k ∈ ℕ) /\ (m === NatDerived.double(k)))).by(Tautology.from(em, defEvenM))

    have(∃(k, (k ∈ ℕ) /\ (m === NatDerived.double(k))) |- Even(m * n)) subproof {
      assume(∃(k, (k ∈ ℕ) /\ (m === NatDerived.double(k))))

      have((k ∈ ℕ) /\ (m === NatDerived.double(k)) |- Even(m * n)) subproof {
        assume((k ∈ ℕ) /\ (m === NatDerived.double(k)))
        val kInℕ = have((k ∈ ℕ) /\ (m === NatDerived.double(k)) |- k ∈ ℕ).by(Tautology)
        val mEq = have((k ∈ ℕ) /\ (m === NatDerived.double(k)) |- m === NatDerived.double(k)).by(Tautology)

        val knInℕ = have((k * n) ∈ ℕ).by(Tautology.from(Nat.mulClosed.of(m := k, n := n), kInℕ, nInℕ))
        val eq0 = have(m * n === NatDerived.double(k) * n).by(Congruence.from(mEq))
        val eq1 = have(NatDerived.double(k) * n === NatDerived.double(k * n)).by(Tautology.from(doubleMulRight.of(m := k, n := n), kInℕ, nInℕ))
        val eq2 = have(m * n === NatDerived.double(k * n)).by(Congruence.from(eq0, eq1))

        val conj = have((k * n) ∈ ℕ /\ ((m * n) === NatDerived.double(k * n))).by(Tautology.from(knInℕ, eq2))
        val ex = thenHave(∃(k, (k ∈ ℕ) /\ ((m * n) === NatDerived.double(k)))).by(RightExists)
        val defEven = have(Even(m * n) <=> ∃(k, (k ∈ ℕ) /\ ((m * n) === NatDerived.double(k)))).by(Restate.from(Even.definition of (x := (m * n))))
        have(thesis).by(Tautology.from(defEven, ex))
      }

      thenHave(thesis).by(LeftExists)
    }

    have(thesis).by(Cut(exM, lastStep))
  }

  /** Lemma: `m∈ℕ ∧ Even(n) ⟹ Even(m*n)`. */
  val evenMulRight = Lemma((m ∈ ℕ, Even(n)) |- Even(m * n)) {
    val mInℕ = assume(m ∈ ℕ)
    val en = assume(Even(n))
    val nInℕ = have(n ∈ ℕ).by(Tautology.from(evenInℕ.of(n := n), en))
    val comm = have(m * n === n * m).by(Tautology.from(NatAlgebra.mulComm.of(m := m, n := n), mInℕ, nInℕ))
    val evNm = have(Even(n * m)).by(Tautology.from(evenMulLeft.of(m := n, n := m), en, mInℕ))
    have(thesis).by(Congruence.from(comm, evNm))
  }

  /** Lemma: `Odd(m) ∧ Odd(n) ⟹ Odd(m*n)`. */
  val oddMulOdd = Lemma((Odd(m), Odd(n)) |- Odd(m * n)) {
    val om = assume(Odd(m))
    val on = assume(Odd(n))

    val defOddM = have(Odd(m) <=> ∃(k, (k ∈ ℕ) /\ (m === Succ(NatDerived.double(k))))).by(Restate.from(Odd.definition of (x := m)))
    val defOddN = have(Odd(n) <=> ∃(k, (k ∈ ℕ) /\ (n === Succ(NatDerived.double(k))))).by(Restate.from(Odd.definition of (x := n)))
    val exM = have(∃(k, (k ∈ ℕ) /\ (m === Succ(NatDerived.double(k))))).by(Tautology.from(om, defOddM))
    val exN = have(∃(k, (k ∈ ℕ) /\ (n === Succ(NatDerived.double(k))))).by(Tautology.from(on, defOddN))

    val step = have(
      (∃(k, (k ∈ ℕ) /\ (m === Succ(NatDerived.double(k)))), ∃(k0, (k0 ∈ ℕ) /\ (n === Succ(NatDerived.double(k0))))) |- Odd(m * n)
    ) subproof {
      val exmAss = assume(∃(k, (k ∈ ℕ) /\ (m === Succ(NatDerived.double(k)))))
      val exnAss = assume(∃(k0, (k0 ∈ ℕ) /\ (n === Succ(NatDerived.double(k0)))))

      have(((k ∈ ℕ) /\ (m === Succ(NatDerived.double(k))), ∃(k0, (k0 ∈ ℕ) /\ (n === Succ(NatDerived.double(k0))))) |- Odd(m * n)) subproof {
        assume((k ∈ ℕ) /\ (m === Succ(NatDerived.double(k))))
        val kInℕ = have((k ∈ ℕ) /\ (m === Succ(NatDerived.double(k))) |- k ∈ ℕ).by(Tautology)
        val mEq = have((k ∈ ℕ) /\ (m === Succ(NatDerived.double(k))) |- m === Succ(NatDerived.double(k))).by(Tautology)

        have(((k0 ∈ ℕ) /\ (n === Succ(NatDerived.double(k0))), (k ∈ ℕ) /\ (m === Succ(NatDerived.double(k)))) |- Odd(m * n)) subproof {
          assume((k0 ∈ ℕ) /\ (n === Succ(NatDerived.double(k0))))
          val k0Inℕ = have((k0 ∈ ℕ) /\ (n === Succ(NatDerived.double(k0))) |- k0 ∈ ℕ).by(Tautology)
          val nEq = have((k0 ∈ ℕ) /\ (n === Succ(NatDerived.double(k0))) |- n === Succ(NatDerived.double(k0))).by(Tautology)

          val dk0Inℕ = have(NatDerived.double(k0) ∈ ℕ).by(Tautology.from(doubleClosed.of(n := k0), k0Inℕ))

          val d0Even = have(Even(NatDerived.double(k0))).by(Tautology.from(evenDouble.of(n := k0), k0Inℕ))
          val dkInℕ = have(NatDerived.double(k) ∈ ℕ).by(Tautology.from(doubleClosed.of(n := k), kInℕ))
          val mNat = have(Succ(NatDerived.double(k)) ∈ ℕ).by(Tautology.from(Nat.succClosed.of(n := NatDerived.double(k)), dkInℕ))
          val evenPart = have(Even(Succ(NatDerived.double(k)) * NatDerived.double(k0))).by(
            Tautology.from(evenMulRight.of(m := Succ(NatDerived.double(k)), n := NatDerived.double(k0)), mNat, d0Even)
          )

          val oddPart = have(Odd(Succ(NatDerived.double(k)))).by(Tautology.from(oddSuccDouble.of(n := k), kInℕ))

          val mulRec = have(
            Succ(NatDerived.double(k)) * Succ(NatDerived.double(k0)) === (Succ(NatDerived.double(k)) * NatDerived.double(k0)) + Succ(NatDerived.double(k))
          ).by(Tautology.from(Nat.mulSucc.of(m := Succ(NatDerived.double(k)), n := NatDerived.double(k0)), dk0Inℕ))

          val rhsOdd = have(Odd((Succ(NatDerived.double(k)) * NatDerived.double(k0)) + Succ(NatDerived.double(k)))).by(
            Tautology.from(evenAddOdd.of(m := (Succ(NatDerived.double(k)) * NatDerived.double(k0)), n := Succ(NatDerived.double(k))), evenPart, oddPart)
          )

          val mmEq = have(m * n === Succ(NatDerived.double(k)) * Succ(NatDerived.double(k0))).by(Congruence.from(mEq, nEq))
          val prodEq = have(m * n === (Succ(NatDerived.double(k)) * NatDerived.double(k0)) + Succ(NatDerived.double(k))).by(Congruence.from(mmEq, mulRec))

          have(thesis).by(Congruence.from(prodEq, rhsOdd))
        }

        thenHave((
          ∃(k0, (k0 ∈ ℕ) /\ (n === Succ(NatDerived.double(k0)))),
          (k ∈ ℕ) /\ (m === Succ(NatDerived.double(k)))
        ) |- Odd(m * n)).by(LeftExists)
      }

      thenHave(thesis).by(LeftExists)
    }

    have(thesis).by(Tautology.from(step, exM, exN))
  }

  /** Theorem (Parity.thy `even_mult_iff`): `m,n∈ℕ ⟹ Even(m*n) ⇔ (Even(m) ∨ Even(n))`. */
  val evenMulIff = Theorem((m ∈ ℕ, n ∈ ℕ) |- (Even(m * n) <=> (Even(m) \/ Even(n)))) {
    val mInℕ = assume(m ∈ ℕ)
    val nInℕ = assume(n ∈ ℕ)
    val mnInℕ = have((m * n) ∈ ℕ).by(Tautology.from(Nat.mulClosed.of(m := m, n := n), mInℕ, nInℕ))

    // <- direction
    val backward = have((Even(m) \/ Even(n)) |- Even(m * n)) subproof {
      val split = assume(Even(m) \/ Even(n))
      val caseEm = have(Even(m) |- Even(m * n)).by(Tautology.from(evenMulLeft.of(m := m, n := n), nInℕ))
      val caseEn = have(Even(n) |- Even(m * n)).by(Tautology.from(evenMulRight.of(m := m, n := n), mInℕ))
      have(thesis).by(Tautology.from(split, caseEm, caseEn))
    }

    // -> direction
    val forward = have(Even(m * n) |- (Even(m) \/ Even(n))) subproof {
      val evProd = assume(Even(m * n))
      val splitM = have(Even(m) \/ Odd(m)).by(Tautology.from(parityExhaustive.of(n := m), mInℕ))

      val caseEvenM = have(Even(m) |- (Even(m) \/ Even(n))).by(Tautology)

      val caseOddM = have(Odd(m) |- (Even(m) \/ Even(n))) subproof {
        val om = assume(Odd(m))
        val splitN = have(Even(n) \/ Odd(n)).by(Tautology.from(parityExhaustive.of(n := n), nInℕ))

        have(Odd(n) |- ⊥) subproof {
          val on = assume(Odd(n))
          val odProd = have(Odd(m * n)).by(Tautology.from(oddMulOdd.of(m := m, n := n), om, on))
          val disj = have(¬(Even(m * n) /\ Odd(m * n))).by(Tautology.from(evenOddDisjoint.of(n := (m * n)), mnInℕ))
          val both = have(Even(m * n) /\ Odd(m * n)).by(Tautology.from(evProd, odProd))
          have(thesis).by(Tautology.from(both, disj))
        }
        val notOddN = thenHave(¬(Odd(n))).by(Restate)
        val en = have(Even(n)).by(Tautology.from(splitN, notOddN))
        have(thesis).by(Tautology.from(en))
      }

      have(thesis).by(Tautology.from(splitM, caseEvenM, caseOddM))
    }

    have(thesis).by(Tautology.from(forward, backward))
  }

  /** Theorem: `m,n∈ℕ ⟹ Odd(m*n) ⇔ (Odd(m) ∧ Odd(n))`. */
  val oddMulIff = Theorem((m ∈ ℕ, n ∈ ℕ) |- (Odd(m * n) <=> (Odd(m) /\ Odd(n)))) {
    val mInℕ = assume(m ∈ ℕ)
    val nInℕ = assume(n ∈ ℕ)
    val mnInℕ = have((m * n) ∈ ℕ).by(Tautology.from(Nat.mulClosed.of(m := m, n := n), mInℕ, nInℕ))

    // <- direction
    val backward = have((Odd(m) /\ Odd(n)) |- Odd(m * n)).by(Tautology.from(oddMulOdd.of(m := m, n := n)))

    // -> direction
    val forward = have(Odd(m * n) |- (Odd(m) /\ Odd(n))) subproof {
      val odProd = assume(Odd(m * n))
      val splitM = have(Even(m) \/ Odd(m)).by(Tautology.from(parityExhaustive.of(n := m), mInℕ))

      have(Even(m) |- ⊥) subproof {
        val em = assume(Even(m))
        val evProd = have(Even(m * n)).by(Tautology.from(evenMulLeft.of(m := m, n := n), em, nInℕ))
        val disj = have(¬(Even(m * n) /\ Odd(m * n))).by(Tautology.from(evenOddDisjoint.of(n := (m * n)), mnInℕ))
        val both = have(Even(m * n) /\ Odd(m * n)).by(Tautology.from(evProd, odProd))
        have(thesis).by(Tautology.from(both, disj))
      }
      val notEvenM = thenHave(¬(Even(m))).by(Restate)
      val om = have(Odd(m)).by(Tautology.from(splitM, notEvenM))

      val splitN = have(Even(n) \/ Odd(n)).by(Tautology.from(parityExhaustive.of(n := n), nInℕ))

      have(Even(n) |- ⊥) subproof {
        val en = assume(Even(n))
        val evProd = have(Even(m * n)).by(Tautology.from(evenMulRight.of(m := m, n := n), mInℕ, en))
        val disj = have(¬(Even(m * n) /\ Odd(m * n))).by(Tautology.from(evenOddDisjoint.of(n := (m * n)), mnInℕ))
        val both = have(Even(m * n) /\ Odd(m * n)).by(Tautology.from(evProd, odProd))
        have(thesis).by(Tautology.from(both, disj))
      }
      val notEvenN = thenHave(¬(Even(n))).by(Restate)
      val on = have(Odd(n)).by(Tautology.from(splitN, notEvenN))

      have(thesis).by(Tautology.from(om, on))
    }

    have(thesis).by(Tautology.from(forward, backward))
  }

  // -------------------------
  // Additional basic parity consequences (Parity.thy-inspired)
  // -------------------------

  /** Lemma: `Odd(n) ⟹ n ≠ 0`. */
  val oddNeZero = Lemma(Odd(n) |- (n =/= 0)) {
    val od = assume(Odd(n))

    have(n === 0 |- ()) subproof {
      val nEq0 = assume(n === 0)
      val od0 = have(Odd(0)).by(Congruence.from(nEq0, od))
      have(thesis).by(Tautology.from(od0, oddZeroFalse))
    }
    thenHave(thesis).by(Restate)
  }

  /** Lemma: `n∈ℕ ∧ Odd(n) ⟹ ¬Even(n)`. */
  val oddImplNotEven = Lemma((n ∈ ℕ, Odd(n)) |- ¬(Even(n))) {
    val nInℕ = assume(n ∈ ℕ)
    val on = assume(Odd(n))
    val disj = have(¬(Even(n) /\ Odd(n))).by(Tautology.from(evenOddDisjoint.of(n := n), nInℕ))

    have(Even(n) |- ()) subproof {
      val en = assume(Even(n))
      val both = have(Even(n) /\ Odd(n)).by(Tautology.from(en, on))
      have(thesis).by(Tautology.from(both, disj))
    }
    thenHave(thesis).by(Restate)
  }

  /** Lemma: `n∈ℕ ∧ Even(n) ⟹ ¬Odd(n)`. */
  val evenImplNotOdd = Lemma((n ∈ ℕ, Even(n)) |- ¬(Odd(n))) {
    val nInℕ = assume(n ∈ ℕ)
    val en = assume(Even(n))
    val disj = have(¬(Even(n) /\ Odd(n))).by(Tautology.from(evenOddDisjoint.of(n := n), nInℕ))

    have(Odd(n) |- ()) subproof {
      val on = assume(Odd(n))
      val both = have(Even(n) /\ Odd(n)).by(Tautology.from(en, on))
      have(thesis).by(Tautology.from(both, disj))
    }
    thenHave(thesis).by(Restate)
  }

  /** Lemma: `¬Even(1)`. */
  val notEvenOne = Lemma(¬(Even(1))) {
    val od1 = have(Odd(1)).by(Tautology.from(oddOne))
    val disj = have(¬(Even(1) /\ Odd(1))).by(Tautology.from(evenOddDisjoint.of(n := 1), Nat.oneInℕ))

    have(Even(1) |- ()) subproof {
      val ev1 = assume(Even(1))
      val both = have(Even(1) /\ Odd(1)).by(Tautology.from(ev1, od1))
      have(thesis).by(Tautology.from(both, disj))
    }
    thenHave(thesis).by(Restate)
  }

  /** Theorem: `n∈ℕ ⟹ Even(n) ⇔ ¬Odd(n)` (using exhaustiveness + disjointness). */
  val evenIffNotOdd = Theorem(n ∈ ℕ |- (Even(n) <=> ¬(Odd(n)))) {
    val nInℕ = assume(n ∈ ℕ)
    val exh = have(Even(n) \/ Odd(n)).by(Tautology.from(parityExhaustive.of(n := n), nInℕ))
    val disj = have(¬(Even(n) /\ Odd(n))).by(Tautology.from(evenOddDisjoint.of(n := n), nInℕ))

    val forward = have(Even(n) |- ¬(Odd(n))).by(Tautology.from(evenImplNotOdd.of(n := n), nInℕ))

    val backward = have(¬(Odd(n)) |- Even(n)) subproof {
      val notOdd = assume(¬(Odd(n)))
      have(Odd(n) |- ()) subproof {
        val on = assume(Odd(n))
        have(thesis).by(Tautology.from(on, notOdd))
      }
      val notOdd2 = thenHave(¬(Odd(n))).by(Restate)
      have(thesis).by(Tautology.from(exh, notOdd2))
    }

    have(thesis).by(Tautology.from(forward, backward))
  }

  /** Theorem: `n∈ℕ ⟹ Odd(n) ⇔ ¬Even(n)` (using exhaustiveness + disjointness). */
  val oddIffNotEven = Theorem(n ∈ ℕ |- (Odd(n) <=> ¬(Even(n)))) {
    val nInℕ = assume(n ∈ ℕ)
    val exh = have(Even(n) \/ Odd(n)).by(Tautology.from(parityExhaustive.of(n := n), nInℕ))

    val forward = have(Odd(n) |- ¬(Even(n))).by(Tautology.from(oddImplNotEven.of(n := n), nInℕ))

    val backward = have(¬(Even(n)) |- Odd(n)) subproof {
      val notEven = assume(¬(Even(n)))
      have(Even(n) |- ()) subproof {
        val en = assume(Even(n))
        have(thesis).by(Tautology.from(en, notEven))
      }
      val notEven2 = thenHave(¬(Even(n))).by(Restate)
      have(thesis).by(Tautology.from(exh, notEven2))
    }

    have(thesis).by(Tautology.from(forward, backward))
  }
}
