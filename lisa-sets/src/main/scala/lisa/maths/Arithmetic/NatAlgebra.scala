package lisa.maths.Arithmetic

import lisa.maths.Arithmetic.Predef.{*, given}
import lisa.maths.Arithmetic.Syntax.{*, given}

/**
 * Basic algebraic properties of addition/multiplication on `Nat.ℕ`.
 *
 * This file mirrors the early arithmetic facts typically used pervasively in Isabelle/HOL's `Nat.thy`,
 * but stated for Lisa's set-theoretic naturals.
 */
object NatAlgebra extends lisa.Main {

  private val Pred = variable[Ind >>: Prop]

  private val a = variable[Ind]
  private val b = variable[Ind]
  private val c = variable[Ind]
  private val i = variable[Ind]
  private val k = variable[Ind]
  private val m = variable[Ind]
  private val n = variable[Ind]

  /** Left neutral element: `0 + n = n` for naturals (Isabelle/HOL `Nat.thy`: `add_0`). */
  val addZeroLeft = Theorem(n ∈ ℕ |- (0 + n === n)) {
    val P = λ(n, 0 + n === n)
    val ind = Nat.induction of (Pred := P)

    val base = have(P(0)).by(Restate.from(Nat.addZero.of(m := 0)))

    val step = have(∀(n, (n ∈ ℕ) ==> (P(n) ==> P(Succ(n))))) subproof {
      have((n ∈ ℕ) ==> (P(n) ==> P(Succ(n)))) subproof {
        val nInℕ = assume(n ∈ ℕ)
        val IH = assume(P(n))

        val eq1 = have(0 + Succ(n) === Succ(0 + n)).by(Tautology.from(Nat.addSucc.of(m := 0, n := n), nInℕ))
        val eq2 = have(Succ(0 + n) === Succ(n)).by(Congruence.from(IH))
        val goalEq = have(0 + Succ(n) === Succ(n)).by(Congruence.from(eq1, eq2))
        have(P(Succ(n))).by(Restate.from(goalEq))
      }
      thenHave(thesis).by(RightForall)
    }

    val allP = have(∀(n, (n ∈ ℕ) ==> P(n))).by(Tautology.from(ind, base, step))
    val imp = have((n ∈ ℕ) ==> P(n)).by(InstantiateForall(n)(allP))
    have(thesis).by(Tautology.from(imp))
  }

  /** Right neutral element: `m + 0 = m` for naturals (Isabelle/HOL `Nat.thy`: `add_0_right`). */
  val addZeroRight = Theorem(m ∈ ℕ |- (m + 0 === m)) {
    have(thesis) by Weakening(Nat.addZero.of(m := m))
  }

  /** Successor on the left: `Succ(m) + n = Succ(m + n)` for naturals `n` (Isabelle/HOL `Nat.thy`: `add_Suc`). */
  val addSuccLeft = Theorem(n ∈ ℕ |- (Succ(m) + n === Succ(m + n))) {
    val P = λ(n, Succ(m) + n === Succ(m + n))
    val ind = Nat.induction of (Pred := P)

    val base = have(P(0)) subproof {
      val eq1 = have(Succ(m) + 0 === Succ(m)).by(Restate.from(Nat.addZero.of(m := Succ(m))))
      val eq2 = have(m + 0 === m).by(Restate.from(Nat.addZero.of(m := m)))
      val eq3 = have(Succ(m + 0) === Succ(m)).by(Congruence.from(eq2))
      val eq3sym = have(Succ(m) === Succ(m + 0)).by(Congruence.from(eq3))
      val goalEq = have(Succ(m) + 0 === Succ(m + 0)).by(Congruence.from(eq1, eq3sym))
      have(P(0)).by(Restate.from(goalEq))
    }

    val step = have(∀(n, (n ∈ ℕ) ==> (P(n) ==> P(Succ(n))))) subproof {
      have((n ∈ ℕ) ==> (P(n) ==> P(Succ(n)))) subproof {
        val nInℕ = assume(n ∈ ℕ)
        val IH = assume(P(n))

        val eq1 = have(Succ(m) + Succ(n) === Succ(Succ(m) + n)).by(Tautology.from(Nat.addSucc.of(m := Succ(m), n := n), nInℕ))
        val eq2 = have(Succ(Succ(m) + n) === Succ(Succ(m + n))).by(Congruence.from(IH))

        val eq3 = have(m + Succ(n) === Succ(m + n)).by(Tautology.from(Nat.addSucc.of(m := m, n := n), nInℕ))
        val eq4 = have(Succ(m + Succ(n)) === Succ(Succ(m + n))).by(Congruence.from(eq3))
        val eq4sym = have(Succ(Succ(m + n)) === Succ(m + Succ(n))).by(Congruence.from(eq4))

        val goalEq = have(Succ(m) + Succ(n) === Succ(m + Succ(n))).by(Congruence.from(eq1, eq2, eq4sym))
        have(P(Succ(n))).by(Restate.from(goalEq))
      }
      thenHave(thesis).by(RightForall)
    }

    val allP = have(∀(n, (n ∈ ℕ) ==> P(n))).by(Tautology.from(ind, base, step))
    val imp = have((n ∈ ℕ) ==> P(n)).by(InstantiateForall(n)(allP))
    have(thesis).by(Tautology.from(imp))
  }

  /** Successor on the right: `m + Succ(n) = Succ(m + n)` for naturals `n` (Isabelle/HOL `Nat.thy`: `add_Suc`). */
  val addSuccRight = Theorem(n ∈ ℕ |- (m + Succ(n) === Succ(m + n))) {
    have(thesis) by Restate.from(Nat.addSucc.of(m := m, n := n))
  }

  /** Commutativity of addition on naturals (Isabelle/HOL: `add.commute`). */
  val addComm = Theorem((m ∈ ℕ, n ∈ ℕ) |- (m + n === n + m)) {
    val ind = Nat.induction of (Pred := λ(n, (m ∈ ℕ) ==> (m + n === n + m)))

    val base0 = have(∀(m, (m ∈ ℕ) ==> (m + 0 === 0 + m))) subproof {
      have((m ∈ ℕ) ==> (m + 0 === 0 + m)) subproof {
        val mInℕ = assume(m ∈ ℕ)
        val eq1 = have(m + 0 === m).by(Restate.from(Nat.addZero.of(m := m)))
        val eq2 = have(0 + m === m).by(Cut(mInℕ, addZeroLeft.of(n := m)))
        val eq2sym = have(m === 0 + m).by(Congruence.from(eq2))
        have(m + 0 === 0 + m).by(Congruence.from(eq1, eq2sym))
      }
      thenHave(thesis).by(RightForall)
    }

    val base = have((m ∈ ℕ) ==> (m + 0 === 0 + m)) subproof {
      val mInℕ = assume(m ∈ ℕ)
      val eq1 = have(m + 0 === m).by(Restate.from(Nat.addZero.of(m := m)))
      val eq2 = have(0 + m === m).by(Cut(mInℕ, addZeroLeft.of(n := m)))
      val eq2sym = have(m === 0 + m).by(Congruence.from(eq2))
      have(m + 0 === 0 + m).by(Congruence.from(eq1, eq2sym))
    }

    val step0 = have(∀(n, (n ∈ ℕ) ==> (∀(m, (m ∈ ℕ) ==> (m + n === n + m)) ==> ∀(m, (m ∈ ℕ) ==> (m + Succ(n) === Succ(n) + m))))) subproof {
      have((n ∈ ℕ) ==> (∀(m, (m ∈ ℕ) ==> (m + n === n + m)) ==> ∀(m, (m ∈ ℕ) ==> (m + Succ(n) === Succ(n) + m)))) subproof {
        val nInℕ = assume(n ∈ ℕ)
        val IH = assume(∀(m, (m ∈ ℕ) ==> (m + n === n + m)))

        have(∀(m, (m ∈ ℕ) ==> (m + Succ(n) === Succ(n) + m))) subproof {
          have((m ∈ ℕ) ==> (m + Succ(n) === Succ(n) + m)) subproof {
            val mInℕ = assume(m ∈ ℕ)

            val ihMImp = have((m ∈ ℕ) ==> (m + n === n + m)).by(InstantiateForall(m)(IH))
            val ihM = have(m + n === n + m).by(Tautology.from(ihMImp, mInℕ))

            val eq1 = have(m + Succ(n) === Succ(m + n)).by(Cut(have(n ∈ ℕ).by(Weakening(nInℕ)), Nat.addSucc.of(m := m, n := n)))

            val eq2 = have(Succ(m + n) === Succ(n + m)).by(Congruence.from(ihM))

            val eq3 = have(Succ(n) + m === Succ(n + m)).by(Weakening(addSuccLeft.of(m := n, n := m)))
            val eq3sym = have(Succ(n + m) === Succ(n) + m).by(Congruence.from(eq3))

            val mid = have(m + Succ(n) === Succ(n + m)).by(Congruence.from(eq1, eq2))
            have(m + Succ(n) === Succ(n) + m).by(Congruence.from(mid, eq3sym))
          }
          thenHave(thesis).by(RightForall)
        }
      }
      thenHave(thesis).by(RightForall)
    }

    val step = have(∀(n, (n ∈ ℕ) ==> (((m ∈ ℕ) ==> (m + n === n + m)) ==> ((m ∈ ℕ) ==> (m + Succ(n) === Succ(n) + m))))) subproof {
      have((n ∈ ℕ) ==> (((m ∈ ℕ) ==> (m + n === n + m)) ==> ((m ∈ ℕ) ==> (m + Succ(n) === Succ(n) + m)))) subproof {
        val nInℕ = assume(n ∈ ℕ)
        val IH = assume((m ∈ ℕ) ==> (m + n === n + m))

        have((m ∈ ℕ) ==> (m + Succ(n) === Succ(n) + m)) subproof {
          val mInℕ = assume(m ∈ ℕ)

          val ihM = have(m + n === n + m).by(Tautology.from(IH, mInℕ))

          val eq1 = have(m + Succ(n) === Succ(m + n)).by(Cut(have(n ∈ ℕ).by(Weakening(nInℕ)), Nat.addSucc.of(m := m, n := n)))

          val eq2 = have(Succ(m + n) === Succ(n + m)).by(Congruence.from(ihM))

          val eq3 = have(Succ(n) + m === Succ(n + m)).by(Weakening(addSuccLeft.of(m := n, n := m)))
          val eq3sym = have(Succ(n + m) === Succ(n) + m).by(Congruence.from(eq3))

          val mid = have(m + Succ(n) === Succ(n + m)).by(Congruence.from(eq1, eq2))
          have(m + Succ(n) === Succ(n) + m).by(Congruence.from(mid, eq3sym))
        }
      }
      thenHave(thesis).by(RightForall)
    }

    val allP = have(∀(n, (n ∈ ℕ) ==> ((m ∈ ℕ) ==> (m + n === n + m)))).by(Tautology.from(ind, base, step))

    val mInℕ = assume(m ∈ ℕ)
    val nInℕ = assume(n ∈ ℕ)

    val PnImp = have((n ∈ ℕ) ==> ((m ∈ ℕ) ==> (m + n === n + m))).by(InstantiateForall(n)(allP))
    val imp = have((m ∈ ℕ) ==> (m + n === n + m)).by(Tautology.from(PnImp, nInℕ))
    val res = have(m + n === n + m).by(Tautology.from(imp, mInℕ))
    have(thesis).by(Restate.from(res))
  }

  /** Add-one on the right: `n + 1 = Succ(n)` for naturals (Isabelle/HOL `Nat.thy`: `Suc_eq_plus1`, by symmetry). */
  val addOneRight = Theorem(n ∈ ℕ |- (n + 1 === Succ(n))) {
    assume(n ∈ ℕ)

    val eq1 = have(n + Succ(0) === Succ(n + 0)).by(Cut(have(0 ∈ ℕ).by(Weakening(Nat.zeroInℕ)), Nat.addSucc.of(m := n, n := 0)))

    val eq2 = have(n + 0 === n).by(Restate.from(Nat.addZero.of(m := n)))
      val eq3 = have(Succ(n + 0) === Succ(n)).by(Congruence.from(eq2))

      val trans = have((n + Succ(0) === Succ(n + 0), Succ(n + 0) === Succ(n)) |- (n + Succ(0) === Succ(n))).by(Congruence)
      val t1 = have(n + Succ(0) === Succ(n + 0) |- (n + Succ(0) === Succ(n))).by(Cut(eq3, trans))
      val res = have(n + Succ(0) === Succ(n)).by(Cut(eq1, t1))
      have(thesis).by(Restate.from(res))
  }

  /** Left zero for multiplication: `0 * n = 0` for naturals (Isabelle/HOL `Nat.thy`: `mult_0`). */
  val mulZeroLeft = Theorem(n ∈ ℕ |- (0 * n === 0)) {
    val P = λ(n, 0 * n === 0)
    val ind = Nat.induction of (Pred := P)

    val base = have(P(0)).by(Restate.from(Nat.mulZero.of(m := 0)))

    val step = have(∀(n, (n ∈ ℕ) ==> (P(n) ==> P(Succ(n))))) subproof {
      have((n ∈ ℕ) ==> (P(n) ==> P(Succ(n)))) subproof {
        val nInℕ = assume(n ∈ ℕ)
        val IH = assume(P(n))

        val eq1 = have(0 * Succ(n) === (0 * n) + 0).by(Cut(have(n ∈ ℕ).by(Weakening(nInℕ)), Nat.mulSucc.of(m := 0, n := n)))

        val eq2 = have((0 * n) + 0 === (0 * n)).by(Restate.from(Nat.addZero.of(m := 0 * n)))
        val eq3 = have(0 * n === 0).by(Restate.from(IH))

        val trans = have((0 * Succ(n) === (0 * n) + 0, (0 * n) + 0 === (0 * n), (0 * n) === 0) |- (0 * Succ(n) === 0)).by(Congruence)
        val t1 = have((0 * Succ(n) === (0 * n) + 0, (0 * n) + 0 === (0 * n)) |- (0 * Succ(n) === 0)).by(Cut(eq3, trans))
        val t2 = have(0 * Succ(n) === (0 * n) + 0 |- (0 * Succ(n) === 0)).by(Cut(eq2, t1))
        have(P(Succ(n))).by(Cut(eq1, t2))
      }
      thenHave(thesis).by(RightForall)
    }

    val allP = have(∀(n, (n ∈ ℕ) ==> P(n))).by(Tautology.from(ind, base, step))
    val imp = have((n ∈ ℕ) ==> P(n)).by(InstantiateForall(n)(allP))
    val nInℕ = assume(n ∈ ℕ)
    val res = have(P(n)).by(Tautology.from(imp, nInℕ))
    have(thesis).by(Restate.from(res))
  }

  /** Right zero for multiplication: `m * 0 = 0` for naturals (Isabelle/HOL `Nat.thy`: `mult_0_right`). */
  val mulZeroRight = Theorem(m ∈ ℕ |- (m * 0 === 0)) {
    have(thesis) by Weakening(Nat.mulZero.of(m := m))
  }

  /** Successor on the right for multiplication: `m * Succ(n) = m*n + m` for naturals `n` (Isabelle/HOL `Nat.thy`: `mult_Suc`). */
  val mulSuccRight = Theorem(n ∈ ℕ |- (m * Succ(n) === (m * n) + m)) {
    have(thesis) by Restate.from(Nat.mulSucc.of(m := m, n := n))
  }

  /** Right one for multiplication: `m * 1 = m` for naturals (Isabelle/HOL: `mult_one`). */
  val mulOneRight = Theorem(m ∈ ℕ |- (m * 1 === m)) {
    val mInℕ = assume(m ∈ ℕ)

    val eq1 = have(m * Succ(0) === (m * 0) + m).by(Cut(have(0 ∈ ℕ).by(Weakening(Nat.zeroInℕ)), Nat.mulSucc.of(m := m, n := 0)))

    val eq2 = have(m * 0 === 0).by(Restate.from(Nat.mulZero.of(m := m)))
    val eq3 = have((m * 0) + m === 0 + m).by(Congruence.from(eq2))

    val eq4 = have(0 + m === m).by(Cut(mInℕ, addZeroLeft.of(n := m)))

    val trans = have((m * Succ(0) === (m * 0) + m, (m * 0) + m === 0 + m, 0 + m === m) |- (m * Succ(0) === m)).by(Congruence)
    val t1 = have((m * Succ(0) === (m * 0) + m, (m * 0) + m === 0 + m) |- (m * Succ(0) === m)).by(Cut(eq4, trans))
    val t2 = have(m * Succ(0) === (m * 0) + m |- (m * Succ(0) === m)).by(Cut(eq3, t1))
    val res = have(m * Succ(0) === m).by(Cut(eq1, t2))
    have(thesis).by(Restate.from(res))
  }

  /** Left one for multiplication: `1 * n = n` for naturals (Isabelle/HOL: `one_mult`). */
  val mulOneLeft = Theorem(n ∈ ℕ |- (1 * n === n)) {
    val P = λ(n, 1 * n === n)
    val ind = Nat.induction of (Pred := P)

    val base = have(P(0)).by(Restate.from(Nat.mulZero.of(m := 1)))

    val step = have(∀(n, (n ∈ ℕ) ==> (P(n) ==> P(Succ(n))))) subproof {
      have((n ∈ ℕ) ==> (P(n) ==> P(Succ(n)))) subproof {
        val nInℕ = assume(n ∈ ℕ)
        val IH = assume(P(n))

        val eq1 = have(1 * Succ(n) === (1 * n) + 1).by(Cut(have(n ∈ ℕ).by(Weakening(nInℕ)), Nat.mulSucc.of(m := 1, n := n)))

        val eq2 = have((1 * n) + 1 === n + 1).by(Congruence.from(IH))

        val eq3 = have(n + 1 === Succ(n)).by(Cut(have(n ∈ ℕ).by(Weakening(nInℕ)), addOneRight.of(n := n)))

        val trans = have((1 * Succ(n) === (1 * n) + 1, (1 * n) + 1 === n + 1, n + 1 === Succ(n)) |- (1 * Succ(n) === Succ(n))).by(Congruence)
        val t1 = have((1 * Succ(n) === (1 * n) + 1, (1 * n) + 1 === n + 1) |- (1 * Succ(n) === Succ(n))).by(Cut(eq3, trans))
        val t2 = have(1 * Succ(n) === (1 * n) + 1 |- (1 * Succ(n) === Succ(n))).by(Cut(eq2, t1))
        have(P(Succ(n))).by(Cut(eq1, t2))
      }
      thenHave(thesis).by(RightForall)
    }

    val allP = have(∀(n, (n ∈ ℕ) ==> P(n))).by(Tautology.from(ind, base, step))
    val imp = have((n ∈ ℕ) ==> P(n)).by(InstantiateForall(n)(allP))
    val nInℕ = assume(n ∈ ℕ)
    val res = have(P(n)).by(Tautology.from(imp, nInℕ))
    have(thesis).by(Restate.from(res))
  }

  /** Associativity of addition on naturals (Isabelle/HOL: `add.assoc`). */
  val addAssoc = Theorem((a ∈ ℕ, b ∈ ℕ, c ∈ ℕ) |- ((a + b) + c === a + (b + c))) {
    val aInℕ = assume(a ∈ ℕ)
    val bInℕ = assume(b ∈ ℕ)
    val cInℕ = assume(c ∈ ℕ)

    val t = variable[Ind]
    val P = λ(t, ((a + b) + t) === a + (b + t))
    val ind = Nat.induction of (Pred := P)

    val base = have(P(0)) subproof {
      val eq1 = have((a + b) + 0 === (a + b)).by(Restate.from(Nat.addZero.of(m := a + b)))
      val eq2 = have(b + 0 === b).by(Restate.from(Nat.addZero.of(m := b)))
      val eq3 = have(a + (b + 0) === a + b).by(Congruence.from(eq2))
      val eq3sym = have(a + b === a + (b + 0)).by(Congruence.from(eq3))
      have((a + b) + 0 === a + (b + 0)).by(Congruence.from(eq1, eq3sym))
    }

    val step = have(∀(n, (n ∈ ℕ) ==> (P(n) ==> P(Succ(n))))) subproof {
      have((n ∈ ℕ) ==> (P(n) ==> P(Succ(n)))) subproof {
        val nInℕ = assume(n ∈ ℕ)
        val IH = assume(P(n))

        val succIH = have(Succ((a + b) + n) === Succ(a + (b + n))).by(Congruence.from(IH))

        val eqL = have((a + b) + Succ(n) === Succ((a + b) + n)).by(Cut(have(n ∈ ℕ).by(Weakening(nInℕ)), Nat.addSucc.of(m := a + b, n := n)))

        val eqB = have(b + Succ(n) === Succ(b + n)).by(Cut(have(n ∈ ℕ).by(Weakening(nInℕ)), Nat.addSucc.of(m := b, n := n)))
        val eqR1 = have(a + (b + Succ(n)) === a + Succ(b + n)).by(Congruence.from(eqB))

        val bnInℕ = have((b + n) ∈ ℕ).by(Tautology.from(Nat.addClosed.of(m := b, n := n), bInℕ, nInℕ))
        val eqR2 = have(a + Succ(b + n) === Succ(a + (b + n))).by(Cut(bnInℕ, Nat.addSucc.of(m := a, n := b + n)))

        val eqR = have(a + (b + Succ(n)) === Succ(a + (b + n))).by(Congruence.from(eqR1, eqR2))
        val eqRsym = have(Succ(a + (b + n)) === a + (b + Succ(n))).by(Congruence.from(eqR))

        val trans = have(
          (
            ((a + b) + Succ(n)) === Succ((a + b) + n),
            Succ((a + b) + n) === Succ(a + (b + n)),
            Succ(a + (b + n)) === a + (b + Succ(n))
          ) |- (((a + b) + Succ(n)) === a + (b + Succ(n)))
        ).by(Congruence)

        val t1 = have(
          (
            ((a + b) + Succ(n)) === Succ((a + b) + n),
            Succ((a + b) + n) === Succ(a + (b + n))
          ) |- (((a + b) + Succ(n)) === a + (b + Succ(n)))
        ).by(Cut(eqRsym, trans))
        val t2 = have(((a + b) + Succ(n)) === Succ((a + b) + n) |- (((a + b) + Succ(n)) === a + (b + Succ(n)))).by(Cut(succIH, t1))
        have(((a + b) + Succ(n)) === a + (b + Succ(n))).by(Cut(eqL, t2))
      }
      thenHave(thesis).by(RightForall)
    }

    val allP = have(∀(t, (t ∈ ℕ) ==> P(t))).by(Tautology.from(ind, base, step))
    val imp = have((c ∈ ℕ) ==> P(c)).by(InstantiateForall(c)(allP))
    val res = have(P(c)).by(Tautology.from(imp, cInℕ))
    have(thesis).by(Restate.from(res))
  }

  /** Left distributivity of multiplication over addition on naturals: `a * (b + c) = a*b + a*c` (Isabelle/HOL: `distrib_left`). */
  val mulDistribLeft = Theorem((a ∈ ℕ, b ∈ ℕ, c ∈ ℕ) |- (a * (b + c) === (a * b) + (a * c))) {
    val aInℕ = assume(a ∈ ℕ)
    val bInℕ = assume(b ∈ ℕ)
    val cInℕ = assume(c ∈ ℕ)

    val t = variable[Ind]
    val P = λ(t, a * (b + t) === (a * b) + (a * t))
    val ind = Nat.induction of (Pred := P)

    val base = have(P(0)) subproof {
      val eqB0 = have(b + 0 === b).by(Restate.from(Nat.addZero.of(m := b)))
      val lhsEq = have(a * (b + 0) === a * b).by(Congruence.from(eqB0))

      val eqA0 = have(a * 0 === 0).by(Restate.from(Nat.mulZero.of(m := a)))
      val rhs0 = have((a * b) + (a * 0) === (a * b) + 0).by(Congruence.from(eqA0))
      val rhs1 = have((a * b) + 0 === (a * b)).by(Restate.from(Nat.addZero.of(m := (a * b))))

      val trans = have(((a * b) + (a * 0) === (a * b) + 0, (a * b) + 0 === (a * b)) |- ((a * b) + (a * 0) === (a * b))).by(Congruence)
      val rhsTo = have((a * b) + (a * 0) === (a * b) + 0 |- (a * b) + (a * 0) === (a * b)).by(Cut(rhs1, trans))
      val rhsEq = have((a * b) + (a * 0) === (a * b)).by(Cut(rhs0, rhsTo))
      val rhsEqSym = have((a * b) === (a * b) + (a * 0)).by(Congruence.from(rhsEq))

      val goalTrans = have((a * (b + 0) === a * b, a * b === (a * b) + (a * 0)) |- (a * (b + 0) === (a * b) + (a * 0))).by(Congruence)
      val lhsTo = have(a * (b + 0) === a * b |- a * (b + 0) === (a * b) + (a * 0)).by(Cut(rhsEqSym, goalTrans))
      have(P(0)).by(Cut(lhsEq, lhsTo))
    }

    val step = have(∀(t, (t ∈ ℕ) ==> (P(t) ==> P(Succ(t))))) subproof {
      have((t ∈ ℕ) ==> (P(t) ==> P(Succ(t)))) subproof {
        val tInℕ = assume(t ∈ ℕ)
        val IH = assume(P(t))

        val eqAdd = have(b + Succ(t) === Succ(b + t)).by(Cut(have(t ∈ ℕ).by(Weakening(tInℕ)), Nat.addSucc.of(m := b, n := t)))
        val lhs0 = have(a * (b + Succ(t)) === a * Succ(b + t)).by(Congruence.from(eqAdd))

        val btInℕ = have((b + t) ∈ ℕ).by(Tautology.from(Nat.addClosed.of(m := b, n := t), bInℕ, tInℕ))
        val eqMul1 = have(a * Succ(b + t) === (a * (b + t)) + a).by(Cut(btInℕ, Nat.mulSucc.of(m := a, n := (b + t))))
        val eqMul1Sub = have(a * Succ(b + t) === ((a * b) + (a * t)) + a).by(Congruence.from(eqMul1, IH))

        val eqMul2 = have(a * Succ(t) === (a * t) + a).by(Cut(have(t ∈ ℕ).by(Weakening(tInℕ)), Nat.mulSucc.of(m := a, n := t)))
        val rhs0 = have((a * b) + (a * Succ(t)) === (a * b) + ((a * t) + a)).by(Congruence.from(eqMul2))

        val abInℕ = have((a * b) ∈ ℕ).by(Tautology.from(Nat.mulClosed.of(m := a, n := b), aInℕ, bInℕ))
        val atInℕ = have((a * t) ∈ ℕ).by(Tautology.from(Nat.mulClosed.of(m := a, n := t), aInℕ, tInℕ))
        val assoc = have(((a * b) + (a * t)) + a === (a * b) + ((a * t) + a)).by(
          Tautology.from(addAssoc.of(a := (a * b), b := (a * t), c := a), abInℕ, atInℕ, aInℕ)
        )

        val trans = have(
          (
            a * (b + Succ(t)) === a * Succ(b + t),
            a * Succ(b + t) === ((a * b) + (a * t)) + a,
            ((a * b) + (a * t)) + a === (a * b) + ((a * t) + a),
            (a * b) + (a * Succ(t)) === (a * b) + ((a * t) + a)
          ) |- (a * (b + Succ(t)) === (a * b) + (a * Succ(t)))
        ).by(Congruence)

        val t1 = have(
          (
            a * (b + Succ(t)) === a * Succ(b + t),
            a * Succ(b + t) === ((a * b) + (a * t)) + a,
            ((a * b) + (a * t)) + a === (a * b) + ((a * t) + a)
          ) |- (a * (b + Succ(t)) === (a * b) + (a * Succ(t)))
        ).by(Cut(rhs0, trans))

        val t2 = have(
          (
            a * (b + Succ(t)) === a * Succ(b + t),
            a * Succ(b + t) === ((a * b) + (a * t)) + a
          ) |- (a * (b + Succ(t)) === (a * b) + (a * Succ(t)))
        ).by(Cut(assoc, t1))

        val t3 = have(a * (b + Succ(t)) === a * Succ(b + t) |- (a * (b + Succ(t)) === (a * b) + (a * Succ(t)))).by(Cut(eqMul1Sub, t2))
        val t4 = have(a * (b + Succ(t)) === (a * b) + (a * Succ(t))).by(Cut(lhs0, t3))
        have(P(Succ(t))).by(Restate.from(t4))
      }
      thenHave(thesis).by(RightForall)
    }

    val allP = have(∀(t, (t ∈ ℕ) ==> P(t))).by(Tautology.from(ind, base, step))
    val imp = have((c ∈ ℕ) ==> P(c)).by(InstantiateForall(c)(allP))
    val res = have(P(c)).by(Tautology.from(imp, cInℕ))
    have(thesis).by(Restate.from(res))
  }

  /** Associativity of multiplication on naturals (Isabelle/HOL: `mult.assoc`). */
  val mulAssoc = Theorem((a ∈ ℕ, b ∈ ℕ, c ∈ ℕ) |- (((a * b) * c) === (a * (b * c)))) {
    val aInℕ = assume(a ∈ ℕ)
    val bInℕ = assume(b ∈ ℕ)
    val cInℕ = assume(c ∈ ℕ)

    val t = variable[Ind]
    val P = λ(t, (a * b) * t === a * (b * t))
    val ind = Nat.induction of (Pred := P)

    val base = have(P(0)) subproof {
      val lhs = have((a * b) * 0 === 0).by(Restate.from(Nat.mulZero.of(m := (a * b))))
      val eqB0 = have(b * 0 === 0).by(Restate.from(Nat.mulZero.of(m := b)))
      val rhs0 = have(a * (b * 0) === a * 0).by(Congruence.from(eqB0))
      val rhs = have(a * 0 === 0).by(Restate.from(Nat.mulZero.of(m := a)))

      val rhsTo = have((a * (b * 0) === a * 0, a * 0 === 0) |- (a * (b * 0) === 0)).by(Congruence)
      val rhsEq = have(a * (b * 0) === 0).by(Cut(rhs0, have(a * (b * 0) === a * 0 |- a * (b * 0) === 0).by(Cut(rhs, rhsTo))))
      val rhsEqSym = have(0 === a * (b * 0)).by(Congruence.from(rhsEq))

      val goalTrans = have(((a * b) * 0 === 0, 0 === a * (b * 0)) |- ((a * b) * 0 === a * (b * 0))).by(Congruence)
      val lhsTo = have((a * b) * 0 === 0 |- (a * b) * 0 === a * (b * 0)).by(Cut(rhsEqSym, goalTrans))
      have(P(0)).by(Cut(lhs, lhsTo))
    }

    val step = have(∀(t, (t ∈ ℕ) ==> (P(t) ==> P(Succ(t))))) subproof {
      have((t ∈ ℕ) ==> (P(t) ==> P(Succ(t)))) subproof {
        val tInℕ = assume(t ∈ ℕ)
        val IH = assume(P(t))

        val eqL = have((a * b) * Succ(t) === ((a * b) * t) + (a * b)).by(Cut(have(t ∈ ℕ).by(Weakening(tInℕ)), Nat.mulSucc.of(m := (a * b), n := t)))
        val eqLSub = have((a * b) * Succ(t) === (a * (b * t)) + (a * b)).by(Congruence.from(eqL, IH))

        val btInℕ = have((b * t) ∈ ℕ).by(Tautology.from(Nat.mulClosed.of(m := b, n := t), bInℕ, tInℕ))
        val eqBt = have(b * Succ(t) === (b * t) + b).by(Cut(have(t ∈ ℕ).by(Weakening(tInℕ)), Nat.mulSucc.of(m := b, n := t)))
        val rhs0 = have(a * (b * Succ(t)) === a * ((b * t) + b)).by(Congruence.from(eqBt))

        val dist = have(a * ((b * t) + b) === (a * (b * t)) + (a * b)).by(
          Tautology.from(mulDistribLeft.of(a := a, b := (b * t), c := b), aInℕ, btInℕ, bInℕ)
        )
        val rhsEq = have(a * (b * Succ(t)) === (a * (b * t)) + (a * b)).by(Congruence.from(rhs0, dist))
        val rhsEqSym = have((a * (b * t)) + (a * b) === a * (b * Succ(t))).by(Congruence.from(rhsEq))

        val goalTrans = have(((a * b) * Succ(t) === (a * (b * t)) + (a * b), (a * (b * t)) + (a * b) === a * (b * Succ(t))) |- ((a * b) * Succ(t) === a * (b * Succ(t)))).by(Congruence)
        val lhsTo = have((a * b) * Succ(t) === (a * (b * t)) + (a * b) |- (a * b) * Succ(t) === a * (b * Succ(t))).by(Cut(rhsEqSym, goalTrans))
        have(P(Succ(t))).by(Cut(eqLSub, lhsTo))
      }
      thenHave(thesis).by(RightForall)
    }

    val allP = have(∀(t, (t ∈ ℕ) ==> P(t))).by(Tautology.from(ind, base, step))
    val imp = have((c ∈ ℕ) ==> P(c)).by(InstantiateForall(c)(allP))
    val res = have(P(c)).by(Tautology.from(imp, cInℕ))
    have(thesis).by(Restate.from(res))
  }

  /** Successor on the left of multiplication (Isabelle/HOL `Nat.thy`: `mult_Suc`). */
  val mulSuccLeft = Theorem((m ∈ ℕ, n ∈ ℕ) |- (Succ(m) * n === n + (m * n))) {
    val mInℕ = assume(m ∈ ℕ)
    val nInℕ = assume(n ∈ ℕ)

    val t = variable[Ind]
    val P = λ(t, Succ(m) * t === t + (m * t))
    val ind = Nat.induction of (Pred := P)

    val base = have(P(0)) subproof {
      val lhs = have(Succ(m) * 0 === 0).by(Restate.from(Nat.mulZero.of(m := Succ(m))))
      val m0 = have(m * 0 === 0).by(Restate.from(Nat.mulZero.of(m := m)))
      val m0Inℕ = have((m * 0) ∈ ℕ).by(Tautology.from(Nat.mulClosed.of(m := m, n := 0), mInℕ, Nat.zeroInℕ))
      val rhs0 = have(0 + (m * 0) === (m * 0)).by(Cut(m0Inℕ, addZeroLeft.of(n := (m * 0))))

      val rhsTo = have((0 + (m * 0) === (m * 0), (m * 0) === 0) |- (0 + (m * 0) === 0)).by(Congruence)
      val rhsEq0 = have(0 + (m * 0) === 0).by(Cut(rhs0, have(0 + (m * 0) === (m * 0) |- 0 + (m * 0) === 0).by(Cut(m0, rhsTo))))
      val rhsEq0Sym = have(0 === 0 + (m * 0)).by(Congruence.from(rhsEq0))

      val goalTrans = have((Succ(m) * 0 === 0, 0 === 0 + (m * 0)) |- (Succ(m) * 0 === 0 + (m * 0))).by(Congruence)
      val lhsTo = have(Succ(m) * 0 === 0 |- Succ(m) * 0 === 0 + (m * 0)).by(Cut(rhsEq0Sym, goalTrans))
      have(P(0)).by(Cut(lhs, lhsTo))
    }

    val step = have(∀(t, (t ∈ ℕ) ==> (P(t) ==> P(Succ(t))))) subproof {
      have((t ∈ ℕ) ==> (P(t) ==> P(Succ(t)))) subproof {
        val tInℕ = assume(t ∈ ℕ)
        val IH = assume(P(t))

        val mulSn = have(Succ(m) * Succ(t) === (Succ(m) * t) + Succ(m)).by(Cut(have(t ∈ ℕ).by(Weakening(tInℕ)), Nat.mulSucc.of(m := Succ(m), n := t)))
        val addSm = have((Succ(m) * t) + Succ(m) === Succ((Succ(m) * t) + m)).by(Cut(have(m ∈ ℕ).by(Weakening(mInℕ)), Nat.addSucc.of(m := (Succ(m) * t), n := m)))
        val lhsS = have(Succ(m) * Succ(t) === Succ((Succ(m) * t) + m)).by(Congruence.from(mulSn, addSm))

        val IHsub = have(Succ((Succ(m) * t) + m) === Succ(((t + (m * t)) + m))).by(Congruence.from(IH))

        val mtInℕ = have((m * t) ∈ ℕ).by(Tautology.from(Nat.mulClosed.of(m := m, n := t), mInℕ, tInℕ))
        val tnInℕ = have(t ∈ ℕ).by(Weakening(tInℕ))
        val tmtInℕ = have((t + (m * t)) ∈ ℕ).by(Tautology.from(Nat.addClosed.of(m := t, n := (m * t)), tnInℕ, mtInℕ))
        val leftInℕ = have(((t + (m * t)) + m) ∈ ℕ).by(Tautology.from(Nat.addClosed.of(m := (t + (m * t)), n := m), tmtInℕ, mInℕ))

        val mulRt = have(m * Succ(t) === (m * t) + m).by(Cut(have(t ∈ ℕ).by(Weakening(tInℕ)), Nat.mulSucc.of(m := m, n := t)))
        val StInℕ = have(Succ(t) ∈ ℕ).by(Cut(tnInℕ, Nat.succClosed.of(n := t)))
        val mStInℕ = have((m * Succ(t)) ∈ ℕ).by(
          Tautology.from(Nat.mulClosed.of(m := m, n := Succ(t)), mInℕ, StInℕ)
        )

        val rhsComm0 = have(Succ(t) + (m * Succ(t)) === (m * Succ(t)) + Succ(t)).by(
          Tautology.from(addComm.of(m := Succ(t), n := (m * Succ(t))), StInℕ, mStInℕ)
        )

        val rhsSucc = have((m * Succ(t)) + Succ(t) === Succ((m * Succ(t)) + t)).by(Cut(have(t ∈ ℕ).by(Weakening(tInℕ)), Nat.addSucc.of(m := (m * Succ(t)), n := t)))
        val rhs1 = have(Succ(t) + (m * Succ(t)) === Succ((m * Succ(t)) + t)).by(Congruence.from(rhsComm0, rhsSucc))

        val rhsSub = have(Succ((m * Succ(t)) + t) === Succ((((m * t) + m) + t))).by(Congruence.from(mulRt))
        val rhsS = have(Succ(t) + (m * Succ(t)) === Succ((((m * t) + m) + t))).by(Congruence.from(rhs1, rhsSub))

        val mnInℕ = have((m * t) ∈ ℕ).by(Restate.from(mtInℕ))
        val commNm = have(t + (m * t) === (m * t) + t).by(Tautology.from(addComm.of(m := t, n := (m * t)), tnInℕ, mnInℕ))
        val eq1 = have((t + (m * t)) + m === ((m * t) + t) + m).by(Congruence.from(commNm))

        val assoc1 = have(((m * t) + t) + m === (m * t) + (t + m)).by(
          Tautology.from(addAssoc.of(a := (m * t), b := t, c := m), mnInℕ, tnInℕ, mInℕ)
        )
        val commTm = have(t + m === m + t).by(Tautology.from(addComm.of(m := t, n := m), tnInℕ, mInℕ))
        val eq2 = have((m * t) + (t + m) === (m * t) + (m + t)).by(Congruence.from(commTm))
        val assoc2 = have(((m * t) + m) + t === (m * t) + (m + t)).by(
          Tautology.from(addAssoc.of(a := (m * t), b := m, c := t), mnInℕ, mInℕ, tnInℕ)
        )
        val assoc2Sym = have((m * t) + (m + t) === ((m * t) + m) + t).by(Congruence.from(assoc2))

        val transIn = have(
          (
            (t + (m * t)) + m === ((m * t) + t) + m,
            ((m * t) + t) + m === (m * t) + (t + m),
            (m * t) + (t + m) === (m * t) + (m + t),
            (m * t) + (m + t) === ((m * t) + m) + t
          ) |- ((t + (m * t)) + m === ((m * t) + m) + t)
        ).by(Congruence)

        val t1 = have(
          (
            (t + (m * t)) + m === ((m * t) + t) + m,
            ((m * t) + t) + m === (m * t) + (t + m),
            (m * t) + (t + m) === (m * t) + (m + t)
          ) |- ((t + (m * t)) + m === ((m * t) + m) + t)
        ).by(Cut(assoc2Sym, transIn))

        val t2 = have(
          (
            (t + (m * t)) + m === ((m * t) + t) + m,
            ((m * t) + t) + m === (m * t) + (t + m)
          ) |- ((t + (m * t)) + m === ((m * t) + m) + t)
        ).by(Cut(eq2, t1))

        val t3 = have(
          ((t + (m * t)) + m === ((m * t) + t) + m) |- ((t + (m * t)) + m === ((m * t) + m) + t)
        ).by(
          Cut(assoc1, t2)
        )
        val inEq = have((t + (m * t)) + m === ((m * t) + m) + t).by(Cut(eq1, t3))

        val goalSucc = have(Succ(((t + (m * t)) + m)) === Succ((((m * t) + m) + t))).by(Congruence.from(inEq))
        val goalTrans = have((Succ(m) * Succ(t) === Succ(((t + (m * t)) + m)), Succ(((t + (m * t)) + m)) === Succ((((m * t) + m) + t))) |- (Succ(m) * Succ(t) === Succ((((m * t) + m) + t)))).by(Congruence)

        val lhsTo = have(Succ(m) * Succ(t) === Succ(((t + (m * t)) + m)) |- Succ(m) * Succ(t) === Succ((((m * t) + m) + t))).by(Cut(goalSucc, goalTrans))
        val lhsSsub = have(Succ(m) * Succ(t) === Succ(((t + (m * t)) + m))).by(Congruence.from(lhsS, IHsub))
        val lhsEq = have(Succ(m) * Succ(t) === Succ((((m * t) + m) + t))).by(Cut(lhsSsub, lhsTo))

        val rhsEqSym = have(Succ((((m * t) + m) + t)) === Succ(t) + (m * Succ(t))).by(Congruence.from(rhsS))
        val finalTrans = have((Succ(m) * Succ(t) === Succ((((m * t) + m) + t)), Succ((((m * t) + m) + t)) === Succ(t) + (m * Succ(t))) |- (Succ(m) * Succ(t) === Succ(t) + (m * Succ(t)))).by(Congruence)
        have(P(Succ(t))).by(Cut(lhsEq, have(Succ(m) * Succ(t) === Succ((((m * t) + m) + t)) |- Succ(m) * Succ(t) === Succ(t) + (m * Succ(t))).by(Cut(rhsEqSym, finalTrans))))
      }
      thenHave(thesis).by(RightForall)
    }

    val allP = have(∀(t, (t ∈ ℕ) ==> P(t))).by(Tautology.from(ind, base, step))

    val imp = have((n ∈ ℕ) ==> P(n)).by(InstantiateForall(n)(allP))
    val res = have(P(n)).by(Tautology.from(imp, nInℕ))
    have(thesis).by(Restate.from(res))
  }

  /** Commutativity of multiplication on naturals (Isabelle/HOL: `mult.commute`). */
  val mulComm = Theorem((m ∈ ℕ, n ∈ ℕ) |- (m * n === n * m)) {
    val mInℕ = assume(m ∈ ℕ)
    val nInℕ = assume(n ∈ ℕ)

    val t = variable[Ind]
    val P = λ(t, m * t === t * m)
    val ind = Nat.induction of (Pred := P)

    val base = have(P(0)) subproof {
      val lhs = have(m * 0 === 0).by(Restate.from(Nat.mulZero.of(m := m)))
      val rhs = have(0 * m === 0).by(Tautology.from(mulZeroLeft.of(n := m), mInℕ))
      val rhsSym = have(0 === 0 * m).by(Congruence.from(rhs))
      val trans = have((m * 0 === 0, 0 === 0 * m) |- (m * 0 === 0 * m)).by(Congruence)
      have(P(0)).by(Cut(lhs, have(m * 0 === 0 |- m * 0 === 0 * m).by(Cut(rhsSym, trans))))
    }

    val step = have(∀(t, (t ∈ ℕ) ==> (P(t) ==> P(Succ(t))))) subproof {
      have((t ∈ ℕ) ==> (P(t) ==> P(Succ(t)))) subproof {
        val tInℕ = assume(t ∈ ℕ)
        val IH = assume(P(t))

        val lhs0 = have(m * Succ(t) === (m * t) + m).by(Cut(have(t ∈ ℕ).by(Weakening(tInℕ)), Nat.mulSucc.of(m := m, n := t)))
        val lhs1 = have(m * Succ(t) === (t * m) + m).by(Congruence.from(lhs0, IH))
        val tmInℕ = have((t * m) ∈ ℕ).by(Tautology.from(Nat.mulClosed.of(m := t, n := m), tInℕ, mInℕ))
        val comm = have((t * m) + m === m + (t * m)).by(Tautology.from(addComm.of(m := (t * m), n := m), tmInℕ, mInℕ))
        val lhs2 = have(m * Succ(t) === m + (t * m)).by(Congruence.from(lhs1, comm))

        val rhs = have(Succ(t) * m === m + (t * m)).by(Tautology.from(mulSuccLeft.of(m := t, n := m), tInℕ, mInℕ))
        val rhsSym = have(m + (t * m) === Succ(t) * m).by(Congruence.from(rhs))

        val trans = have((m * Succ(t) === m + (t * m), m + (t * m) === Succ(t) * m) |- (m * Succ(t) === Succ(t) * m)).by(Congruence)
        have(P(Succ(t))).by(Cut(lhs2, have(m * Succ(t) === m + (t * m) |- m * Succ(t) === Succ(t) * m).by(Cut(rhsSym, trans))))
      }
      thenHave(thesis).by(RightForall)
    }

    val allP = have(∀(t, (t ∈ ℕ) ==> P(t))).by(Tautology.from(ind, base, step))

    val imp = have((n ∈ ℕ) ==> P(n)).by(InstantiateForall(n)(allP))
    val res = have(P(n)).by(Tautology.from(imp, nInℕ))
    have(thesis).by(Restate.from(res))
  }

  /** Right distributivity of multiplication over addition (Isabelle/HOL `Nat.thy`: `add_mult_distrib`). */
  val mulDistribRight = Theorem((a ∈ ℕ, b ∈ ℕ, c ∈ ℕ) |- (((a + b) * c) === (a * c) + (b * c))) {
    val aInℕ = assume(a ∈ ℕ)
    val bInℕ = assume(b ∈ ℕ)
    val cInℕ = assume(c ∈ ℕ)

    val abInℕ = have((a + b) ∈ ℕ).by(Tautology.from(Nat.addClosed.of(m := a, n := b), aInℕ, bInℕ))
    val comm1 = have((a + b) * c === c * (a + b)).by(
      Tautology.from(mulComm.of(m := (a + b), n := c), abInℕ, cInℕ)
    )
    val dist = have(c * (a + b) === (c * a) + (c * b)).by(Tautology.from(mulDistribLeft.of(a := c, b := a, c := b), cInℕ, aInℕ, bInℕ))

    val commA = have(c * a === a * c).by(Tautology.from(mulComm.of(m := c, n := a), cInℕ, aInℕ))
    val commB = have(c * b === b * c).by(Tautology.from(mulComm.of(m := c, n := b), cInℕ, bInℕ))
    val rhs = have((c * a) + (c * b) === (a * c) + (b * c)).by(Congruence.from(commA, commB))

    val trans = have(((a + b) * c === c * (a + b), c * (a + b) === (c * a) + (c * b), (c * a) + (c * b) === (a * c) + (b * c)) |- (((a + b) * c) === (a * c) + (b * c))).by(Congruence)
    val t1 = have(((a + b) * c === c * (a + b), c * (a + b) === (c * a) + (c * b)) |- ((a + b) * c === (a * c) + (b * c))).by(Cut(rhs, trans))
    val t2 = have((a + b) * c === c * (a + b) |- ((a + b) * c === (a * c) + (b * c))).by(Cut(dist, t1))
    have(thesis).by(Cut(comm1, t2))
  }

  /** Left cancellation for addition on naturals (Isabelle/HOL: `add_left_cancel`). */
  val addLeftCancel = Theorem((a ∈ ℕ, b ∈ ℕ, c ∈ ℕ, a + b === a + c) |- (b === c)) {
    val all = assume(a ∈ ℕ /\ b ∈ ℕ /\ c ∈ ℕ /\ (a + b === a + c))
    val aInℕ = have(a ∈ ℕ).by(Tautology.from(all))
    val bInℕ = have(b ∈ ℕ).by(Tautology.from(all))
    val cInℕ = have(c ∈ ℕ).by(Tautology.from(all))
    val eq = have(a + b === a + c).by(Tautology.from(all))

    val x = variable[Ind]
    val P = λ(x, (x + b === x + c) ==> (b === c))
    val ind = Nat.induction of (Pred := P)

    val base = have(P(0)) subproof {
      have((0 + b === 0 + c) ==> (b === c)) subproof {
        val eq0 = assume(0 + b === 0 + c)
        val zb = have(0 + b === b).by(Cut(have(b ∈ ℕ).by(Weakening(bInℕ)), addZeroLeft.of(n := b)))
        val zc = have(0 + c === c).by(Cut(have(c ∈ ℕ).by(Weakening(cInℕ)), addZeroLeft.of(n := c)))
        val zbSym = have(b === 0 + b).by(Congruence.from(zb))

        val trans = have((b === 0 + b, 0 + b === 0 + c, 0 + c === c) |- (b === c)).by(Congruence)
        val t1 = have((0 + b === 0 + c, 0 + c === c) |- (b === c)).by(Cut(zbSym, trans))
        val t2 = have(0 + b === 0 + c |- (b === c)).by(Cut(zc, t1))
        val bc = have(b === c).by(Cut(eq0, t2))
        have(thesis).by(Restate.from(bc))
      }
      have(P(0)).by(Restate.from(lastStep))
    }

    val step = have(∀(x, (x ∈ ℕ) ==> (P(x) ==> P(Succ(x))))) subproof {
      have((x ∈ ℕ) ==> (P(x) ==> P(Succ(x)))) subproof {
        val xInℕ = assume(x ∈ ℕ)
        val IH = assume(P(x))

        have((Succ(x) + b === Succ(x) + c) ==> (b === c)) subproof {
          assume(Succ(x) + b === Succ(x) + c)

          val sb = have(Succ(x) + b === Succ(x + b)).by(Cut(have(b ∈ ℕ).by(Weakening(bInℕ)), addSuccLeft.of(m := x, n := b)))
          val sc = have(Succ(x) + c === Succ(x + c)).by(Cut(have(c ∈ ℕ).by(Weakening(cInℕ)), addSuccLeft.of(m := x, n := c)))

          val sEq = have(Succ(x + b) === Succ(x + c)).by(Congruence.from(sb, sc, lastStep))
          val inj = have(Succ(x + b) === Succ(x + c) |- (x + b === x + c)).by(Tautology.from(Nat.succInjective.of(m := (x + b), n := (x + c))))
          val xbEq = have(x + b === x + c).by(Cut(sEq, inj))

          val IHapp = have((x + b === x + c) ==> (b === c)).by(Weakening(IH))
          have(b === c).by(Tautology.from(IHapp, xbEq))
        }
        have(P(Succ(x))).by(Restate.from(lastStep))
      }
      thenHave(thesis).by(RightForall)
    }

    val allP = have(∀(x, (x ∈ ℕ) ==> P(x))).by(Tautology.from(ind, base, step))
    val imp = have((a ∈ ℕ) ==> P(a)).by(InstantiateForall(a)(allP))
    val Pa = have(P(a)).by(Tautology.from(imp))
    val PaImp = have((a + b === a + c) ==> (b === c)).by(Tautology.from(Pa))
    have(thesis).by(Tautology.from(PaImp, eq))
  }

  /** Right cancellation for addition on naturals (Isabelle/HOL: `add_right_cancel`). */
  val addRightCancel = Theorem((a ∈ ℕ, b ∈ ℕ, c ∈ ℕ, b + a === c + a) |- (b === c)) {
    val aInℕ = assume(a ∈ ℕ)
    val bInℕ = assume(b ∈ ℕ)
    val cInℕ = assume(c ∈ ℕ)
    val eq = assume(b + a === c + a)

    val ba = have(b + a === a + b).by(Tautology.from(addComm.of(m := b, n := a), bInℕ, aInℕ))
    val ca = have(c + a === a + c).by(Tautology.from(addComm.of(m := c, n := a), cInℕ, aInℕ))
    val aEq = have(a + b === a + c).by(Congruence.from(ba, ca, eq))

    have(thesis).by(Tautology.from(addLeftCancel.of(a := a, b := b, c := c), aInℕ, bInℕ, cInℕ, aEq))
  }

  /** If `m + n = m` then `n = 0` (Isabelle/HOL `Nat.thy`: `add_eq_self_zero`). */
  val addEqSelfZero = Theorem((m ∈ ℕ, n ∈ ℕ, m + n === m) |- (n === 0)) {
    val all = assume(m ∈ ℕ /\ n ∈ ℕ /\ (m + n === m))
    val mInℕ = have(m ∈ ℕ).by(Tautology.from(all))
    val nInℕ = have(n ∈ ℕ).by(Tautology.from(all))
    val eq = have(m + n === m).by(Tautology.from(all))

    val x = variable[Ind]
    val P = λ(x, (x + n === x) ==> (n === 0))
    val ind = Nat.induction of (Pred := P)

    val base = have(P(0)) subproof {
      have((0 + n === 0) ==> (n === 0)) subproof {
        val eq0 = assume(0 + n === 0)
        val zn = have(0 + n === n).by(Cut(have(n ∈ ℕ).by(Weakening(nInℕ)), addZeroLeft.of(n := n)))
        val znSym = have(n === 0 + n).by(Congruence.from(zn))
        val trans = have((n === 0 + n, 0 + n === 0) |- (n === 0)).by(Congruence)
        val t1 = have(0 + n === 0 |- (n === 0)).by(Cut(znSym, trans))
        have(n === 0).by(Cut(eq0, t1))
      }
      have(P(0)).by(Restate.from(lastStep))
    }

    val step = have(∀(x, (x ∈ ℕ) ==> (P(x) ==> P(Succ(x))))) subproof {
      have((x ∈ ℕ) ==> (P(x) ==> P(Succ(x)))) subproof {
        val xInℕ = assume(x ∈ ℕ)
        val IH = assume(P(x))

        have((Succ(x) + n === Succ(x)) ==> (n === 0)) subproof {
          val eqS = assume(Succ(x) + n === Succ(x))

          val sxn = have(Succ(x) + n === Succ(x + n)).by(Cut(have(n ∈ ℕ).by(Weakening(nInℕ)), addSuccLeft.of(m := x, n := n)))
          val sEq = have(Succ(x + n) === Succ(x)).by(Congruence.from(sxn, eqS))
          val inj = have(Succ(x + n) === Succ(x) |- (x + n === x)).by(Tautology.from(Nat.succInjective.of(m := (x + n), n := x)))
          val xnEq = have(x + n === x).by(Cut(sEq, inj))

          val IHapp = have((x + n === x) ==> (n === 0)).by(Weakening(IH))
          have(n === 0).by(Tautology.from(IHapp, xnEq))
        }
        have(P(Succ(x))).by(Restate.from(lastStep))
      }
      thenHave(thesis).by(RightForall)
    }

    val allP = have(∀(x, (x ∈ ℕ) ==> P(x))).by(Tautology.from(ind, base, step))
    val imp = have((m ∈ ℕ) ==> P(m)).by(InstantiateForall(m)(allP))
    val Pm = have(P(m)).by(Tautology.from(imp))
    val PmImp = have((m + n === m) ==> (n === 0)).by(Tautology.from(Pm))
    have(thesis).by(Tautology.from(PmImp, eq))
  }

  /** If `m + n = n` then `m = 0` (Isabelle/HOL: `add_eq_self_zero` + `add.commute`). */
  val addEqSelfZeroLeft = Theorem((m ∈ ℕ, n ∈ ℕ, m + n === n) |- (m === 0)) {
    val mInℕ = assume(m ∈ ℕ)
    val nInℕ = assume(n ∈ ℕ)
    val eq = assume(m + n === n)

    val comm = have(n + m === m + n).by(Tautology.from(addComm.of(m := n, n := m), nInℕ, mInℕ))
    val nmEq = have(n + m === n).by(Congruence.from(comm, eq))
    have(thesis).by(Tautology.from(addEqSelfZero.of(m := n, n := m), nInℕ, mInℕ, nmEq))
  }

  /** Closure helper: if `a,b,c ∈ ℕ` then `a + (b + c) ∈ ℕ` (Isabelle/HOL: by typing of `+` on `nat`). */
  val addClosed3 = Theorem((a ∈ ℕ, b ∈ ℕ, c ∈ ℕ) |- ((a + (b + c)) ∈ ℕ)) {
    val aInℕ = assume(a ∈ ℕ)
    val bInℕ = assume(b ∈ ℕ)
    val cInℕ = assume(c ∈ ℕ)
    val bcInℕ = have((b + c) ∈ ℕ).by(Tautology.from(Nat.addClosed.of(m := b, n := c), bInℕ, cInℕ))
    have(thesis).by(Tautology.from(Nat.addClosed.of(m := a, n := (b + c)), aInℕ, bcInℕ))
  }

  /** Closure helper: if `a,b,c ∈ ℕ` then `a * (b * c) ∈ ℕ` (Isabelle/HOL: by typing of `*` on `nat`). */
  val mulClosed3 = Theorem((a ∈ ℕ, b ∈ ℕ, c ∈ ℕ) |- ((a * (b * c)) ∈ ℕ)) {
    val aInℕ = assume(a ∈ ℕ)
    val bInℕ = assume(b ∈ ℕ)
    val cInℕ = assume(c ∈ ℕ)
    val bcInℕ = have((b * c) ∈ ℕ).by(Tautology.from(Nat.mulClosed.of(m := b, n := c), bInℕ, cInℕ))
    have(thesis).by(Tautology.from(Nat.mulClosed.of(m := a, n := (b * c)), aInℕ, bcInℕ))
  }

  /** Convenience: `Succ(m) * n ∈ ℕ` under `m,n ∈ ℕ` (Isabelle/HOL: by typing; derived from `mult_Suc`). */
  val mulSuccLeftClosed = Theorem((m ∈ ℕ, n ∈ ℕ) |- ((Succ(m) * n) ∈ ℕ)) {
    val mInℕ = assume(m ∈ ℕ)
    val nInℕ = assume(n ∈ ℕ)
    val SmInℕ = have(Succ(m) ∈ ℕ).by(Tautology.from(Nat.succClosed.of(n := m), mInℕ))
    have(thesis).by(Tautology.from(Nat.mulClosed.of(m := Succ(m), n := n), SmInℕ, nInℕ))
  }

  /** Characterization of addition equal to zero (Isabelle/HOL `Nat.thy`: `add_is_0`). */
  val addEqZeroIff = Theorem((m ∈ ℕ, n ∈ ℕ) |- ((m + n === 0) <=> ((m === 0) /\ (n === 0)))) {
    val both = assume(m ∈ ℕ /\ n ∈ ℕ)

    val `==>` = have((m ∈ ℕ /\ n ∈ ℕ /\ (m + n === 0)) |- ((m === 0) /\ (n === 0))) subproof {
      val all = assume(m ∈ ℕ /\ n ∈ ℕ /\ (m + n === 0))
      val mInℕ = have(m ∈ ℕ).by(Tautology.from(all))
      val nInℕ = have(n ∈ ℕ).by(Tautology.from(all))
      val eq = have(m + n === 0).by(Tautology.from(all))

      val mCases = have((m === 0) \/ ∃(k, (k ∈ ℕ) /\ (m === Succ(k)))).by(Cut(mInℕ, Nat.natCases.of(n := m)))
      val case0Imp = have((m === 0) ==> (m === 0)).by(Restate)

      val instK = have((k ∈ ℕ) /\ (m === Succ(k)) |- m === 0) subproof {
        val conj = assume((k ∈ ℕ) /\ (m === Succ(k)))
        val kInℕ = have(k ∈ ℕ).by(Tautology.from(conj))
        val mEqSk = have(m === Succ(k)).by(Tautology.from(conj))

        val eqW = have(m + n === 0).by(Weakening(eq))
        val nInℕW = have(n ∈ ℕ).by(Weakening(nInℕ))

        val SknEq0 = have(Succ(k) + n === 0).by(Congruence.from(mEqSk, eqW))
        val SknEq = have(Succ(k) + n === Succ(k + n)).by(Cut(nInℕW, addSuccLeft.of(m := k, n := n)))
        val SnEq0 = have(Succ(k + n) === 0).by(Congruence.from(SknEq, SknEq0))

        val knInℕ = have((k + n) ∈ ℕ).by(
          Tautology.from(Nat.addClosed.of(m := k, n := n), kInℕ, nInℕW)
        )
        val SnNe0 = have(Succ(k + n) =/= 0).by(Cut(knInℕ, Nat.succNeZero.of(n := (k + n))))
        val notSnEq0 = have(¬(Succ(k + n) === 0)).by(Tautology.from(SnNe0))
        val contra = have((k ∈ ℕ) /\ (m === Succ(k)) |- ()).by(Tautology.from(SnEq0, notSnEq0))
        have(thesis).by(Tautology.from(contra))
      }

      val caseS = have(∃(k, (k ∈ ℕ) /\ (m === Succ(k))) |- m === 0).by(LeftExists(instK))

      val caseSImp = have(∃(k, (k ∈ ℕ) /\ (m === Succ(k))) ==> (m === 0)).by(Restate.from(caseS))
      val m0 = have(m === 0).by(Tautology.from(mCases, case0Imp, caseSImp))

      val znEq0 = have(0 + n === 0).by(Congruence.from(m0, eq))
      val znEqn = have(0 + n === n).by(Cut(nInℕ, addZeroLeft.of(n := n)))
      val znEqnSym = have(n === 0 + n).by(Congruence.from(znEqn))

      val n0 = have(n === 0).by(Congruence.from(znEqnSym, znEq0))

      have(thesis).by(Tautology.from(m0, n0))
    }

    val `<==` = have((m ∈ ℕ /\ n ∈ ℕ /\ ((m === 0) /\ (n === 0))) |- (m + n === 0)) subproof {
      val all = assume(m ∈ ℕ /\ n ∈ ℕ /\ ((m === 0) /\ (n === 0)))
      val conj = have((m === 0) /\ (n === 0)).by(Tautology.from(all))
      val m0 = have(m === 0).by(Tautology.from(conj))
      val n0 = have(n === 0).by(Tautology.from(conj))

      val mnEqm0 = have(m + n === m + 0).by(Congruence.from(n0))
      val mn0Eqm = have(m + 0 === m).by(Restate.from(Nat.addZero.of(m := m)))
      val mnEqm = have(m + n === m).by(Congruence.from(mnEqm0, mn0Eqm))
      have(m + n === 0).by(Congruence.from(mnEqm, m0))
    }

    val imp1 = have((m ∈ ℕ /\ n ∈ ℕ) |- ((m + n === 0) ==> ((m === 0) /\ (n === 0)))).by(Restate.from(`==>`))
    val imp2 = have((m ∈ ℕ /\ n ∈ ℕ) |- (((m === 0) /\ (n === 0)) ==> (m + n === 0))).by(Restate.from(`<==`))
    have(thesis).by(Tautology.from(imp1, imp2))
  }

  /** Characterization of multiplication equal to zero (Isabelle/HOL `Nat.thy`: `mult_is_0`). */
  val mulEqZeroIff = Theorem((m ∈ ℕ, n ∈ ℕ) |- ((m * n === 0) <=> ((m === 0) \/ (n === 0)))) {
    val both = assume(m ∈ ℕ /\ n ∈ ℕ)

    val `==>` = have((m ∈ ℕ /\ n ∈ ℕ /\ (m * n === 0)) |- ((m === 0) \/ (n === 0))) subproof {
      val all = assume(m ∈ ℕ /\ n ∈ ℕ /\ (m * n === 0))
      val mInℕ = have(m ∈ ℕ).by(Tautology.from(all))
      val nInℕ = have(n ∈ ℕ).by(Tautology.from(all))
      val eq = have(m * n === 0).by(Tautology.from(all))

      val nCases = have((n === 0) \/ ∃(k, (k ∈ ℕ) /\ (n === Succ(k)))).by(Cut(nInℕ, Nat.natCases.of(n := n)))

      val case0 = have((n === 0) |- ((m === 0) \/ (n === 0))).by(Tautology)
      val case0Imp = have((n === 0) ==> ((m === 0) \/ (n === 0))).by(Restate.from(case0))

      val instK = have((k ∈ ℕ) /\ (n === Succ(k)) |- ((m === 0) \/ (n === 0))) subproof {
        val hk = assume((k ∈ ℕ) /\ (n === Succ(k)))
        val kInℕ = have(k ∈ ℕ).by(Tautology.from(hk))
        val nEqSk = have(n === Succ(k)).by(Tautology.from(hk))

        val eqW = have(m * n === 0).by(Weakening(eq))
        val mInℕW = have(m ∈ ℕ).by(Weakening(mInℕ))

        val mkEq0 = have(m * Succ(k) === 0).by(Congruence.from(nEqSk, eqW))
        val mkEq = have(m * Succ(k) === (m * k) + m).by(Cut(kInℕ, mulSuccRight.of(m := m, n := k)))
        val addEq0 = have((m * k) + m === 0).by(Congruence.from(mkEq, mkEq0))

        val mkInℕ = have((m * k) ∈ ℕ).by(Tautology.from(Nat.mulClosed.of(m := m, n := k), mInℕW, kInℕ))
        val iff = have(((m * k) + m === 0) <=> (((m * k) === 0) /\ (m === 0))).by(
          Tautology.from(addEqZeroIff.of(m := (m * k), n := m), mkInℕ, mInℕW)
        )
        val conj = have(((m * k) === 0) /\ (m === 0)).by(Tautology.from(iff, addEq0))
        val m0 = have(m === 0).by(Tautology.from(conj))
        have(thesis).by(Tautology.from(m0))
      }

      val caseS = have(∃(k, (k ∈ ℕ) /\ (n === Succ(k))) |- ((m === 0) \/ (n === 0))).by(LeftExists(instK))

      val caseSImp = have(∃(k, (k ∈ ℕ) /\ (n === Succ(k))) ==> ((m === 0) \/ (n === 0))).by(Restate.from(caseS))
      have(thesis).by(Tautology.from(nCases, case0Imp, caseSImp))
    }

    val `<==` = have((m ∈ ℕ /\ n ∈ ℕ /\ ((m === 0) \/ (n === 0))) |- (m * n === 0)) subproof {
      val all = assume(m ∈ ℕ /\ n ∈ ℕ /\ ((m === 0) \/ (n === 0)))
      val mInℕ = have(m ∈ ℕ).by(Tautology.from(all))
      val nInℕ = have(n ∈ ℕ).by(Tautology.from(all))
      val disj = have((m === 0) \/ (n === 0)).by(Tautology.from(all))

      val caseM0 = have((n ∈ ℕ /\ (m === 0)) |- (m * n === 0)) subproof {
        val nm = assume(n ∈ ℕ /\ (m === 0))
        val nNat = have(n ∈ ℕ).by(Tautology.from(nm))
        val m0 = have(m === 0).by(Tautology.from(nm))
        val eq0 = have(0 * n === 0).by(Cut(nNat, mulZeroLeft.of(n := n)))
        have(m * n === 0).by(Congruence.from(m0, eq0))
      }
      val impM0 = have(n ∈ ℕ |- ((m === 0) ==> (m * n === 0))).by(Restate.from(caseM0))
      val impM0InCtx = have((m ∈ ℕ /\ n ∈ ℕ /\ ((m === 0) \/ (n === 0))) |- ((m === 0) ==> (m * n === 0))).by(Cut(nInℕ, impM0))

      val caseN0 = have((m ∈ ℕ /\ (n === 0)) |- (m * n === 0)) subproof {
        val mn = assume(m ∈ ℕ /\ (n === 0))
        val mNat = have(m ∈ ℕ).by(Tautology.from(mn))
        val n0 = have(n === 0).by(Tautology.from(mn))
        val eq0 = have(m * 0 === 0).by(Cut(mNat, mulZeroRight.of(m := m)))
        have(m * n === 0).by(Congruence.from(n0, eq0))
      }
      val impN0 = have(m ∈ ℕ |- ((n === 0) ==> (m * n === 0))).by(Restate.from(caseN0))
      val impN0InCtx = have((m ∈ ℕ /\ n ∈ ℕ /\ ((m === 0) \/ (n === 0))) |- ((n === 0) ==> (m * n === 0))).by(Cut(mInℕ, impN0))

      have(thesis).by(Tautology.from(disj, impM0InCtx, impN0InCtx))
    }

    val imp1 = have((m ∈ ℕ /\ n ∈ ℕ) |- ((m * n === 0) ==> ((m === 0) \/ (n === 0)))).by(Restate.from(`==>`))
    val imp2 = have((m ∈ ℕ /\ n ∈ ℕ) |- (((m === 0) \/ (n === 0)) ==> (m * n === 0))).by(Restate.from(`<==`))
    have(thesis).by(Tautology.from(imp1, imp2))
  }

  /** Left projection of `addEqZeroIff` (Isabelle/HOL `Nat.thy`: `add_is_0`, forward direction). */
  val addEqZeroLeft = Theorem((m ∈ ℕ, n ∈ ℕ, m + n === 0) |- (m === 0)) {
    val mInℕ = assume(m ∈ ℕ)
    val nInℕ = assume(n ∈ ℕ)
    val eq = assume(m + n === 0)

    val iff = have((m + n === 0) <=> ((m === 0) /\ (n === 0))).by(Tautology.from(addEqZeroIff, mInℕ, nInℕ))
    val conj = have((m === 0) /\ (n === 0)).by(Tautology.from(iff, eq))
    have(thesis).by(Tautology.from(conj))
  }

  /** Right projection of `addEqZeroIff` (Isabelle/HOL `Nat.thy`: `add_is_0`, forward direction). */
  val addEqZeroRight = Theorem((m ∈ ℕ, n ∈ ℕ, m + n === 0) |- (n === 0)) {
    val mInℕ = assume(m ∈ ℕ)
    val nInℕ = assume(n ∈ ℕ)
    val eq = assume(m + n === 0)

    val iff = have((m + n === 0) <=> ((m === 0) /\ (n === 0))).by(Tautology.from(addEqZeroIff, mInℕ, nInℕ))
    val conj = have((m === 0) /\ (n === 0)).by(Tautology.from(iff, eq))
    have(thesis).by(Tautology.from(conj))
  }

  /** If the left addend is nonzero, the sum is nonzero (Isabelle/HOL `Nat.thy`: `add_is_0`, contrapositive). */
  val addNeZeroLeft = Theorem((m ∈ ℕ, n ∈ ℕ, m =/= 0) |- (m + n =/= 0)) {
    val mInℕ = assume(m ∈ ℕ)
    val nInℕ = assume(n ∈ ℕ)
    val mNe0 = assume(m =/= 0)
    val notm0 = have(¬(m === 0)).by(Tautology.from(mNe0))

    have(m + n === 0 |- ()) subproof {
      val eq = assume(m + n === 0)
      val m0 = have(m === 0).by(Tautology.from(addEqZeroLeft, mInℕ, nInℕ, eq))
      have(thesis).by(Tautology.from(m0, notm0))
    }
    thenHave(¬(m + n === 0)) by RightNot
    thenHave(thesis).by(Restate)
  }

  /** If the right addend is nonzero, the sum is nonzero (Isabelle/HOL `Nat.thy`: `add_is_0`, contrapositive). */
  val addNeZeroRight = Theorem((m ∈ ℕ, n ∈ ℕ, n =/= 0) |- (m + n =/= 0)) {
    val mInℕ = assume(m ∈ ℕ)
    val nInℕ = assume(n ∈ ℕ)
    val nNe0 = assume(n =/= 0)
    val notn0 = have(¬(n === 0)).by(Tautology.from(nNe0))

    have(m + n === 0 |- ()) subproof {
      val eq = assume(m + n === 0)
      val n0 = have(n === 0).by(Tautology.from(addEqZeroRight, mInℕ, nInℕ, eq))
      have(thesis).by(Tautology.from(n0, notn0))
    }
    thenHave(¬(m + n === 0)) by RightNot
    thenHave(thesis).by(Restate)
  }

  /** If the product is nonzero, both factors are nonzero (Isabelle/HOL `Nat.thy`: `mult_is_0`, contrapositive). */
  val mulNeZeroBoth = Theorem((m ∈ ℕ, n ∈ ℕ, m * n =/= 0) |- ((m =/= 0) /\ (n =/= 0))) {
    val mInℕ = assume(m ∈ ℕ)
    val nInℕ = assume(n ∈ ℕ)
    val mnNe0 = assume(m * n =/= 0)
    val notmn0 = have(¬(m * n === 0)).by(Tautology.from(mnNe0))

    val iff = have((m * n === 0) <=> ((m === 0) \/ (n === 0))).by(Tautology.from(mulEqZeroIff, mInℕ, nInℕ))
    val contra = have(((m === 0) \/ (n === 0)) ==> (m * n === 0)).by(Tautology.from(iff))
    val notDisj = have(¬((m === 0) \/ (n === 0))).by(Tautology.from(notmn0, contra))

    val notm0 = have(¬(m === 0)).by(Tautology.from(notDisj))
    val notn0 = have(¬(n === 0)).by(Tautology.from(notDisj))
    val mNe0 = have(m =/= 0).by(Restate.from(notm0))
    val nNe0 = have(n =/= 0).by(Restate.from(notn0))
    have(thesis).by(Tautology.from(mNe0, nNe0))
  }

  /** If both factors are nonzero, the product is nonzero (Isabelle/HOL `Nat.thy`: `mult_not_zero`). */
  val mulNeZero = Theorem((m ∈ ℕ, n ∈ ℕ, m =/= 0, n =/= 0) |- (m * n =/= 0)) {
    val mInℕ = assume(m ∈ ℕ)
    val nInℕ = assume(n ∈ ℕ)
    val mNe0 = assume(m =/= 0)
    val nNe0 = assume(n =/= 0)
    val notm0 = have(¬(m === 0)).by(Tautology.from(mNe0))
    val notn0 = have(¬(n === 0)).by(Tautology.from(nNe0))

    val notDisj = have(¬((m === 0) \/ (n === 0))).by(Tautology.from(notm0, notn0))
    val iff = have((m * n === 0) <=> ((m === 0) \/ (n === 0))).by(Tautology.from(mulEqZeroIff, mInℕ, nInℕ))
    val notmn0 = have(¬(m * n === 0)).by(Tautology.from(iff, notDisj))
    have(thesis).by(Restate.from(notmn0))
  }

  /** Nonzero sum characterization (Isabelle/HOL `Nat.thy`: negation of `add_is_0`). */
  val addNeZeroIff = Theorem((m ∈ ℕ, n ∈ ℕ) |- ((m + n =/= 0) <=> ((m =/= 0) \/ (n =/= 0)))) {
    val mInℕ = assume(m ∈ ℕ)
    val nInℕ = assume(n ∈ ℕ)
    val iff0 = have((m + n === 0) <=> ((m === 0) /\ (n === 0))).by(Tautology.from(addEqZeroIff, mInℕ, nInℕ))

    val notIff = have(¬(m + n === 0) <=> ¬((m === 0) /\ (n === 0))).by(Tautology.from(iff0))
    val deMorgan = have(¬((m === 0) /\ (n === 0)) <=> (¬(m === 0) \/ ¬(n === 0))).by(Tautology)
    val rhs = have(¬(m + n === 0) <=> (¬(m === 0) \/ ¬(n === 0))).by(Tautology.from(notIff, deMorgan))

    have(thesis).by(Restate.from(rhs))
  }

  /** Nonzero product characterization (Isabelle/HOL `Nat.thy`: negation of `mult_is_0`). */
  val mulNeZeroIff = Theorem((m ∈ ℕ, n ∈ ℕ) |- ((m * n =/= 0) <=> ((m =/= 0) /\ (n =/= 0)))) {
    val mInℕ = assume(m ∈ ℕ)
    val nInℕ = assume(n ∈ ℕ)
    val iff0 = have((m * n === 0) <=> ((m === 0) \/ (n === 0))).by(Tautology.from(mulEqZeroIff, mInℕ, nInℕ))

    val notIff = have(¬(m * n === 0) <=> ¬((m === 0) \/ (n === 0))).by(Tautology.from(iff0))
    val deMorgan = have(¬((m === 0) \/ (n === 0)) <=> (¬(m === 0) /\ ¬(n === 0))).by(Tautology)
    val rhs = have(¬(m * n === 0) <=> (¬(m === 0) /\ ¬(n === 0))).by(Tautology.from(notIff, deMorgan))

    have(thesis).by(Restate.from(rhs))
  }

  /** Characterization of `m * n = m` (Isabelle/HOL `Nat.thy`: `mult_eq_self`). */
  val mulEqSelfIff = Theorem((m ∈ ℕ, n ∈ ℕ) |- ((m * n === m) <=> ((m === 0) \/ (n === Succ(0))))) {
    val both = assume(m ∈ ℕ /\ n ∈ ℕ)
    val mInℕ = have(m ∈ ℕ).by(Tautology.from(both))
    val nInℕ = have(n ∈ ℕ).by(Tautology.from(both))

    val `==>` = have((m ∈ ℕ /\ n ∈ ℕ /\ (m * n === m)) |- ((m === 0) \/ (n === Succ(0)))) subproof {
      val all = assume(m ∈ ℕ /\ n ∈ ℕ /\ (m * n === m))
      val mIn = have(m ∈ ℕ).by(Tautology.from(all))
      val nIn = have(n ∈ ℕ).by(Tautology.from(all))
      val eq = have(m * n === m).by(Tautology.from(all))

      val nCases = have((n === 0) \/ ∃(k, (k ∈ ℕ) /\ (n === Succ(k)))).by(Cut(nIn, Nat.natCases.of(n := n)))

      val case0 = have(n === 0 |- ((m === 0) \/ (n === Succ(0)))) subproof {
        val n0 = assume(n === 0)

        val m0 = have(m === 0) subproof {
          val mnEq = have(m * n === m * 0).by(Congruence.from(n0))
          val m0Eq0 = have(m * 0 === 0).by(Restate.from(Nat.mulZero.of(m := m)))
          val mnEq0 = have(m * n === 0).by(Congruence.from(mnEq, m0Eq0))
          val mEq0 = have(m === 0).by(Congruence.from(eq, mnEq0))
          have(thesis).by(Restate.from(mEq0))
        }

        have(thesis).by(Tautology.from(m0))
      }
      val case0Imp = have((n === 0) ==> ((m === 0) \/ (n === Succ(0)))).by(Restate.from(case0))

      val instK = have((k ∈ ℕ) /\ (n === Succ(k)) |- ((m === 0) \/ (n === Succ(0)))) subproof {
        val hk = assume((k ∈ ℕ) /\ (n === Succ(k)))
        val kInℕ = have(k ∈ ℕ).by(Tautology.from(hk))
        val nEqSk = have(n === Succ(k)).by(Tautology.from(hk))

          val mnEq = have(m * n === m * Succ(k)).by(Congruence.from(nEqSk))
          val mkEq = have(m * Succ(k) === (m * k) + m).by(Cut(kInℕ, mulSuccRight.of(m := m, n := k)))
          val mnEqAdd = have(m * n === (m * k) + m).by(Congruence.from(mnEq, mkEq))

          val mkInℕ = have((m * k) ∈ ℕ).by(Tautology.from(Nat.mulClosed.of(m := m, n := k), mIn, kInℕ))
          val comm = have((m * k) + m === m + (m * k)).by(Tautology.from(addComm.of(m := (m * k), n := m), mkInℕ, mIn))

          val eq2 = have(m + (m * k) === m).by(Congruence.from(comm, mnEqAdd, eq))

          val mk0 = have((m * k) === 0).by(Tautology.from(addEqSelfZero.of(m := m, n := (m * k)), mIn, mkInℕ, eq2))

          val iffMk0 = have((m * k === 0) <=> ((m === 0) \/ (k === 0))).by(Tautology.from(mulEqZeroIff.of(m := m, n := k), mIn, kInℕ))
          val disj0 = have((m === 0) \/ (k === 0)).by(Tautology.from(iffMk0, mk0))

          val n1Fromk0 = have(k === 0 |- (n === Succ(0))) subproof {
            val k0 = assume(k === 0)
            val skEq = have(Succ(k) === Succ(0)).by(Congruence.from(k0))
            have(thesis).by(Congruence.from(nEqSk, skEq))
          }
          val n1Fromk0Imp = have((k === 0) ==> (n === Succ(0))).by(Restate.from(n1Fromk0))

        have(thesis).by(Tautology.from(disj0, n1Fromk0Imp))
      }

      val caseS = have(∃(k, (k ∈ ℕ) /\ (n === Succ(k))) |- ((m === 0) \/ (n === Succ(0)))).by(LeftExists(instK))

      val caseSImp = have(∃(k, (k ∈ ℕ) /\ (n === Succ(k))) ==> ((m === 0) \/ (n === Succ(0)))).by(Restate.from(caseS))
      have(thesis).by(Tautology.from(nCases, case0Imp, caseSImp))
    }

    val `<==` = have((m ∈ ℕ /\ n ∈ ℕ /\ ((m === 0) \/ (n === Succ(0)))) |- (m * n === m)) subproof {
      val all = assume(m ∈ ℕ /\ n ∈ ℕ /\ ((m === 0) \/ (n === Succ(0))))
      val mIn = have(m ∈ ℕ).by(Tautology.from(all))
      val nIn = have(n ∈ ℕ).by(Tautology.from(all))
      val disj = have((m === 0) \/ (n === Succ(0))).by(Tautology.from(all))

      val caseM0 = have((n ∈ ℕ /\ (m === 0)) |- (m * n === m)) subproof {
        val nm = assume(n ∈ ℕ /\ (m === 0))
        val nNat = have(n ∈ ℕ).by(Tautology.from(nm))
        val m0 = have(m === 0).by(Tautology.from(nm))
        val zn0 = have(0 * n === 0).by(Tautology.from(mulZeroLeft.of(n := n), nNat))
        val mn0 = have(m * n === 0).by(Congruence.from(m0, zn0))
        have(thesis).by(Congruence.from(mn0, m0))
      }
      val impM0 = have(n ∈ ℕ |- ((m === 0) ==> (m * n === m))).by(Restate.from(caseM0))
      val caseM0Imp = have((m === 0) ==> (m * n === m)).by(Cut(nIn, impM0))

      val caseN1 = have((m ∈ ℕ /\ (n === Succ(0))) |- (m * n === m)) subproof {
        val mn = assume(m ∈ ℕ /\ (n === Succ(0)))
        val mNat = have(m ∈ ℕ).by(Tautology.from(mn))
        val n1 = have(n === Succ(0)).by(Tautology.from(mn))
        val m1 = have(m * Succ(0) === m).by(Cut(mNat, mulOneRight.of(m := m)))
        have(thesis).by(Congruence.from(n1, m1))
      }
      val impN1 = have(m ∈ ℕ |- ((n === Succ(0)) ==> (m * n === m))).by(Restate.from(caseN1))
      val caseN1Imp = have((n === Succ(0)) ==> (m * n === m)).by(Cut(mIn, impN1))

      have(thesis).by(Tautology.from(disj, caseM0Imp, caseN1Imp))
    }

    val imp1 = have((m ∈ ℕ /\ n ∈ ℕ) |- ((m * n === m) ==> ((m === 0) \/ (n === Succ(0))))).by(Restate.from(`==>`))
    val imp2 = have((m ∈ ℕ /\ n ∈ ℕ) |- (((m === 0) \/ (n === Succ(0))) ==> (m * n === m))).by(Restate.from(`<==`))
    have(thesis).by(Tautology.from(imp1, imp2))
  }

  /** Characterization of `m + n = m` (Isabelle/HOL `Nat.thy`: `add_right_cancel` + `add_eq_self_zero`). */
  val addEqSelfIff = Theorem((m ∈ ℕ, n ∈ ℕ) |- ((m + n === m) <=> (n === 0))) {
    val both = assume(m ∈ ℕ /\ n ∈ ℕ)
    val mInℕ = have(m ∈ ℕ).by(Tautology.from(both))
    val nInℕ = have(n ∈ ℕ).by(Tautology.from(both))

    val `==>` = have((m ∈ ℕ /\ n ∈ ℕ /\ (m + n === m)) |- (n === 0)) subproof {
      val all = assume(m ∈ ℕ /\ n ∈ ℕ /\ (m + n === m))
      val mIn = have(m ∈ ℕ).by(Tautology.from(all))
      val nIn = have(n ∈ ℕ).by(Tautology.from(all))
      val eq = have(m + n === m).by(Tautology.from(all))

      have(thesis).by(Tautology.from(addEqSelfZero.of(m := m, n := n), mIn, nIn, eq))
    }

    val `<==` = have((m ∈ ℕ /\ n ∈ ℕ /\ (n === 0)) |- (m + n === m)) subproof {
      val all = assume(m ∈ ℕ /\ n ∈ ℕ /\ (n === 0))
      val mIn = have(m ∈ ℕ).by(Tautology.from(all))
      val n0 = have(n === 0).by(Tautology.from(all))

      val mnEq = have(m + n === m + 0).by(Congruence.from(n0))
      val m0Eq = have(m + 0 === m).by(Cut(mIn, addZeroRight.of(m := m)))
      have(thesis).by(Congruence.from(mnEq, m0Eq))
    }

    val imp1 = have((m ∈ ℕ /\ n ∈ ℕ) |- ((m + n === m) ==> (n === 0))).by(Restate.from(`==>`))
    val imp2 = have((m ∈ ℕ /\ n ∈ ℕ) |- ((n === 0) ==> (m + n === m))).by(Restate.from(`<==`))
    have(thesis).by(Tautology.from(imp1, imp2))
  }

  /** Characterization of `m + n = n` (Isabelle/HOL `Nat.thy`: `add_left_cancel` + `add_eq_self_zero`). */
  val addEqSelfIffLeft = Theorem((m ∈ ℕ, n ∈ ℕ) |- ((m + n === n) <=> (m === 0))) {
    val both = assume(m ∈ ℕ /\ n ∈ ℕ)
    val mInℕ = have(m ∈ ℕ).by(Tautology.from(both))
    val nInℕ = have(n ∈ ℕ).by(Tautology.from(both))

    val `==>` = have((m ∈ ℕ /\ n ∈ ℕ /\ (m + n === n)) |- (m === 0)) subproof {
      val all = assume(m ∈ ℕ /\ n ∈ ℕ /\ (m + n === n))
      val mIn = have(m ∈ ℕ).by(Tautology.from(all))
      val nIn = have(n ∈ ℕ).by(Tautology.from(all))
      val eq = have(m + n === n).by(Tautology.from(all))

      have(thesis).by(Tautology.from(addEqSelfZeroLeft.of(m := m, n := n), mIn, nIn, eq))
    }

    val `<==` = have((m ∈ ℕ /\ n ∈ ℕ /\ (m === 0)) |- (m + n === n)) subproof {
      val all = assume(m ∈ ℕ /\ n ∈ ℕ /\ (m === 0))
      val nIn = have(n ∈ ℕ).by(Tautology.from(all))
      val m0 = have(m === 0).by(Tautology.from(all))

      val mnEq = have(m + n === 0 + n).by(Congruence.from(m0))
      val znEq = have(0 + n === n).by(Cut(nIn, addZeroLeft.of(n := n)))
      have(thesis).by(Congruence.from(mnEq, znEq))
    }

    val imp1 = have((m ∈ ℕ /\ n ∈ ℕ) |- ((m + n === n) ==> (m === 0))).by(Restate.from(`==>`))
    val imp2 = have((m ∈ ℕ /\ n ∈ ℕ) |- ((m === 0) ==> (m + n === n))).by(Restate.from(`<==`))
    have(thesis).by(Tautology.from(imp1, imp2))
  }

  /** Left-commutativity of addition: `a + (b + c) = b + (a + c)` (Isabelle/HOL `Nat.thy`: `add_left_comm`). */
  val addLeftComm = Theorem((a ∈ ℕ, b ∈ ℕ, c ∈ ℕ) |- (a + (b + c) === b + (a + c))) {
    val abc = assume(a ∈ ℕ /\ b ∈ ℕ /\ c ∈ ℕ)
    val aInℕ = have(a ∈ ℕ).by(Tautology.from(abc))
    val bInℕ = have(b ∈ ℕ).by(Tautology.from(abc))
    val cInℕ = have(c ∈ ℕ).by(Tautology.from(abc))

    val ab = have(a ∈ ℕ /\ b ∈ ℕ).by(Tautology.from(aInℕ, bInℕ))
    val bc = have(b ∈ ℕ /\ c ∈ ℕ).by(Tautology.from(bInℕ, cInℕ))
    val ac = have(a ∈ ℕ /\ c ∈ ℕ).by(Tautology.from(aInℕ, cInℕ))

    val assoc1 = have((a + b) + c === a + (b + c)).by(Tautology.from(addAssoc.of(a := a, b := b, c := c), aInℕ, bInℕ, cInℕ))
    val assoc1sym = have(a + (b + c) === (a + b) + c).by(Congruence.from(assoc1))
    val commAB = have(a + b === b + a).by(Tautology.from(addComm.of(m := a, n := b), aInℕ, bInℕ))
    val cong1 = have((a + b) + c === (b + a) + c).by(Congruence.from(commAB))
    val assoc2 = have((b + a) + c === b + (a + c)).by(Tautology.from(addAssoc.of(a := b, b := a, c := c), bInℕ, aInℕ, cInℕ))

    val mid1 = have(a + (b + c) === (b + a) + c).by(Congruence.from(assoc1sym, cong1))
    have(thesis).by(Congruence.from(mid1, assoc2))
  }

  /** Left-commutativity of multiplication: `a * (b * c) = b * (a * c)` (Isabelle/HOL `Nat.thy`: `mult_left_comm`). */
  val mulLeftComm = Theorem((a ∈ ℕ, b ∈ ℕ, c ∈ ℕ) |- (a * (b * c) === b * (a * c))) {
    val abc = assume(a ∈ ℕ /\ b ∈ ℕ /\ c ∈ ℕ)
    val aInℕ = have(a ∈ ℕ).by(Tautology.from(abc))
    val bInℕ = have(b ∈ ℕ).by(Tautology.from(abc))
    val cInℕ = have(c ∈ ℕ).by(Tautology.from(abc))

    val assoc1 = have((a * b) * c === a * (b * c)).by(Tautology.from(mulAssoc.of(a := a, b := b, c := c), aInℕ, bInℕ, cInℕ))
    val assoc1sym = have(a * (b * c) === (a * b) * c).by(Congruence.from(assoc1))
    val commAB = have(a * b === b * a).by(Tautology.from(mulComm.of(m := a, n := b), aInℕ, bInℕ))
    val cong1 = have((a * b) * c === (b * a) * c).by(Congruence.from(commAB))
    val assoc2 = have((b * a) * c === b * (a * c)).by(Tautology.from(mulAssoc.of(a := b, b := a, c := c), bInℕ, aInℕ, cInℕ))

    val mid1 = have(a * (b * c) === (b * a) * c).by(Congruence.from(assoc1sym, cong1))
    have(thesis).by(Congruence.from(mid1, assoc2))
  }

  /** If the product is zero and the left factor is nonzero, the right factor is zero (Isabelle/HOL `Nat.thy`: `mult_eq_0_iff` corollary). */
  val mulEqZeroRightFromLeftNeZero = Theorem((m ∈ ℕ, n ∈ ℕ, m * n === 0, m =/= 0) |- (n === 0)) {
    val mInℕ = assume(m ∈ ℕ)
    val nInℕ = assume(n ∈ ℕ)
    val eq = assume(m * n === 0)
    val mNe0 = assume(m =/= 0)
    val notm0 = have(¬(m === 0)).by(Tautology.from(mNe0))

    val iff = have((m * n === 0) <=> ((m === 0) \/ (n === 0))).by(Tautology.from(mulEqZeroIff, mInℕ, nInℕ))
    val disj = have((m === 0) \/ (n === 0)).by(Tautology.from(iff, eq))
    have(thesis).by(Tautology.from(disj, notm0))
  }

  /** If the product is zero and the right factor is nonzero, the left factor is zero (Isabelle/HOL `Nat.thy`: `mult_eq_0_iff` corollary). */
  val mulEqZeroLeftFromRightNeZero = Theorem((m ∈ ℕ, n ∈ ℕ, m * n === 0, n =/= 0) |- (m === 0)) {
    val mInℕ = assume(m ∈ ℕ)
    val nInℕ = assume(n ∈ ℕ)
    val eq = assume(m * n === 0)
    val nNe0 = assume(n =/= 0)
    val notn0 = have(¬(n === 0)).by(Tautology.from(nNe0))

    val iff = have((m * n === 0) <=> ((m === 0) \/ (n === 0))).by(Tautology.from(mulEqZeroIff, mInℕ, nInℕ))
    val disj = have((m === 0) \/ (n === 0)).by(Tautology.from(iff, eq))
    have(thesis).by(Tautology.from(disj, notn0))
  }

  /** Characterization of `m * n = n` (Isabelle/HOL `Nat.thy`: `mult_eq_self`, by commutativity). */
  val mulEqSelfRightIff = Theorem((m ∈ ℕ, n ∈ ℕ) |- ((m * n === n) <=> ((n === 0) \/ (m === Succ(0))))) {
    val both = assume(m ∈ ℕ /\ n ∈ ℕ)
    val mInℕ = have(m ∈ ℕ).by(Tautology.from(both))
    val nInℕ = have(n ∈ ℕ).by(Tautology.from(both))

    val comm = have(m * n === n * m).by(Tautology.from(mulComm.of(m := m, n := n), mInℕ, nInℕ))
    val commSym = have(n * m === m * n).by(Congruence.from(comm))

    val iffNM = have((n * m === n) <=> ((n === 0) \/ (m === Succ(0)))).by(Tautology.from(mulEqSelfIff.of(m := n, n := m), nInℕ, mInℕ))

    val `==>` = have((m ∈ ℕ /\ n ∈ ℕ /\ (m * n === n)) |- ((n === 0) \/ (m === Succ(0)))) subproof {
      val all = assume(m ∈ ℕ /\ n ∈ ℕ /\ (m * n === n))
      val eq = have(m * n === n).by(Tautology.from(all))
      val eq2 = have(n * m === n).by(Congruence.from(commSym, eq))
      have(thesis).by(Tautology.from(iffNM, eq2))
    }

    val `<==` = have((m ∈ ℕ /\ n ∈ ℕ /\ ((n === 0) \/ (m === Succ(0)))) |- (m * n === n)) subproof {
      val all = assume(m ∈ ℕ /\ n ∈ ℕ /\ ((n === 0) \/ (m === Succ(0))))
      val disj = have((n === 0) \/ (m === Succ(0))).by(Tautology.from(all))

      val nmEq = have(n * m === n).by(Tautology.from(iffNM, disj))
      val mnEq = have(m * n === n * m).by(Weakening(comm))
      have(thesis).by(Congruence.from(mnEq, nmEq))
    }

    val imp1 = have((m ∈ ℕ /\ n ∈ ℕ) |- ((m * n === n) ==> ((n === 0) \/ (m === Succ(0))))).by(Restate.from(`==>`))
    val imp2 = have((m ∈ ℕ /\ n ∈ ℕ) |- (((n === 0) \/ (m === Succ(0))) ==> (m * n === n))).by(Restate.from(`<==`))
    have(thesis).by(Tautology.from(imp1, imp2))
  }

  /** Characterization of addition equal to one (Isabelle/HOL `Nat.thy`: `add_eq_1`). */
  val addEqOneIff = Theorem((m ∈ ℕ, n ∈ ℕ) |- ((m + n === Succ(0)) <=> (((m === 0) /\ (n === Succ(0))) \/ ((m === Succ(0)) /\ (n === 0))))) {
    val both = assume(m ∈ ℕ /\ n ∈ ℕ)

    val `==>` = have((m ∈ ℕ /\ n ∈ ℕ /\ (m + n === Succ(0))) |- (((m === 0) /\ (n === Succ(0))) \/ ((m === Succ(0)) /\ (n === 0)))) subproof {
      val all = assume(m ∈ ℕ /\ n ∈ ℕ /\ (m + n === Succ(0)))
      val mInℕ = have(m ∈ ℕ).by(Tautology.from(all))
      val nInℕ = have(n ∈ ℕ).by(Tautology.from(all))
      val eq = have(m + n === Succ(0)).by(Tautology.from(all))

      val mCases = have((m === 0) \/ ∃(k, (k ∈ ℕ) /\ (m === Succ(k)))).by(Cut(mInℕ, Nat.natCases.of(n := m)))

      val case0 = have((m === 0) |- (((m === 0) /\ (n === Succ(0))) \/ ((m === Succ(0)) /\ (n === 0)))) subproof {
        val m0 = assume(m === 0)
        val mnEq = have(m + n === 0 + n).by(Congruence.from(m0))
        val nIn = have(n ∈ ℕ).by(Weakening(nInℕ))
        val znEq = have(0 + n === n).by(Cut(nIn, addZeroLeft.of(n := n)))
        val mnEqn = have(m + n === n).by(Congruence.from(mnEq, znEq))
        val n1 = have(n === Succ(0)).by(Congruence.from(eq, mnEqn))
        have(thesis).by(Tautology.from(m0, n1))
      }
      val case0Imp = have((m === 0) ==> (((m === 0) /\ (n === Succ(0))) \/ ((m === Succ(0)) /\ (n === 0)))).by(Restate.from(case0))

      val instK = have((k ∈ ℕ) /\ (m === Succ(k)) |- (((m === 0) /\ (n === Succ(0))) \/ ((m === Succ(0)) /\ (n === 0)))) subproof {
        val hk = assume((k ∈ ℕ) /\ (m === Succ(k)))
        val kInℕ = have(k ∈ ℕ).by(Tautology.from(hk))
        val mEqSk = have(m === Succ(k)).by(Tautology.from(hk))

        val eqW = have(m + n === Succ(0)).by(Weakening(eq))
        val nInℕW = have(n ∈ ℕ).by(Weakening(nInℕ))

          val snEq1 = have(Succ(k) + n === Succ(0)).by(Congruence.from(mEqSk, eqW))
          val snEq = have(Succ(k) + n === Succ(k + n)).by(Cut(nInℕW, addSuccLeft.of(m := k, n := n)))
          val sknEq1 = have(Succ(k + n) === Succ(0)).by(Congruence.from(snEq, snEq1))

          val iffInj = have((Succ(k + n) === Succ(0)) <=> ((k + n) === 0)).by(Restate.from(Nat.succInjective.of(m := (k + n), n := 0)))
          val kn0 = have((k + n) === 0).by(Tautology.from(iffInj, sknEq1))

          val iff0 = have((k + n === 0) <=> ((k === 0) /\ (n === 0))).by(Tautology.from(addEqZeroIff.of(m := k, n := n), kInℕ, nInℕW))
          val conj0 = have((k === 0) /\ (n === 0)).by(Tautology.from(iff0, kn0))
          val k0 = have(k === 0).by(Tautology.from(conj0))
          val n0 = have(n === 0).by(Tautology.from(conj0))

          val sk0 = have(Succ(k) === Succ(0)).by(Congruence.from(k0))
          val m1 = have(m === Succ(0)).by(Congruence.from(mEqSk, sk0))
        have(thesis).by(Tautology.from(m1, n0))
      }

      val caseS = have(∃(k, (k ∈ ℕ) /\ (m === Succ(k))) |- (((m === 0) /\ (n === Succ(0))) \/ ((m === Succ(0)) /\ (n === 0)))).by(LeftExists(instK))
      val caseSImp = have(∃(k, (k ∈ ℕ) /\ (m === Succ(k))) ==> (((m === 0) /\ (n === Succ(0))) \/ ((m === Succ(0)) /\ (n === 0)))).by(Restate.from(caseS))

      have(thesis).by(Tautology.from(mCases, case0Imp, caseSImp))
    }

    val `<==` = have((m ∈ ℕ /\ n ∈ ℕ /\ (((m === 0) /\ (n === Succ(0))) \/ ((m === Succ(0)) /\ (n === 0)))) |- (m + n === Succ(0))) subproof {
      val all = assume(m ∈ ℕ /\ n ∈ ℕ /\ (((m === 0) /\ (n === Succ(0))) \/ ((m === Succ(0)) /\ (n === 0))))
      val mInℕ = have(m ∈ ℕ).by(Tautology.from(all))
      val nInℕ = have(n ∈ ℕ).by(Tautology.from(all))
      val disj = have(((m === 0) /\ (n === Succ(0))) \/ ((m === Succ(0)) /\ (n === 0))).by(Tautology.from(all))

      val caseL = have((m === 0) /\ (n === Succ(0)) |- (m + n === Succ(0))) subproof {
        val conj = assume((m === 0) /\ (n === Succ(0)))
        val m0 = have(m === 0).by(Tautology.from(conj))
        val n1 = have(n === Succ(0)).by(Tautology.from(conj))

        val mnEq = have(m + n === 0 + n).by(Congruence.from(m0))
        val nIn = have(n ∈ ℕ).by(Weakening(nInℕ))
        val znEq = have(0 + n === n).by(Cut(nIn, addZeroLeft.of(n := n)))
        val mnEqn = have(m + n === n).by(Congruence.from(mnEq, znEq))
        have(thesis).by(Congruence.from(mnEqn, n1))
      }
      val caseLImp = have(((m === 0) /\ (n === Succ(0))) ==> (m + n === Succ(0))).by(Restate.from(caseL))

      val caseR = have((m === Succ(0)) /\ (n === 0) |- (m + n === Succ(0))) subproof {
        val conj = assume((m === Succ(0)) /\ (n === 0))
        val m1 = have(m === Succ(0)).by(Tautology.from(conj))
        val n0 = have(n === 0).by(Tautology.from(conj))

        val mnEq = have(m + n === m + 0).by(Congruence.from(n0))
        val mIn = have(m ∈ ℕ).by(Weakening(mInℕ))
        val m0Eq = have(m + 0 === m).by(Cut(mIn, addZeroRight.of(m := m)))
        val mnEqm = have(m + n === m).by(Congruence.from(mnEq, m0Eq))
        have(thesis).by(Congruence.from(mnEqm, m1))
      }
      val caseRImp = have(((m === Succ(0)) /\ (n === 0)) ==> (m + n === Succ(0))).by(Restate.from(caseR))

      have(thesis).by(Tautology.from(disj, caseLImp, caseRImp))
    }

    val imp1 = have((m ∈ ℕ /\ n ∈ ℕ) |- ((m + n === Succ(0)) ==> (((m === 0) /\ (n === Succ(0))) \/ ((m === Succ(0)) /\ (n === 0))))).by(Restate.from(`==>`))
    val imp2 = have((m ∈ ℕ /\ n ∈ ℕ) |- ((((m === 0) /\ (n === Succ(0))) \/ ((m === Succ(0)) /\ (n === 0))) ==> (m + n === Succ(0)))).by(Restate.from(`<==`))
    have(thesis).by(Tautology.from(imp1, imp2))
  }
}