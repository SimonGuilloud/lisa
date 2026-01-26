package lisa.maths.Arithmetic
import lisa.maths.Arithmetic.Predef.{*, given}
import lisa.maths.Arithmetic.Syntax.{*, given}

/**
 * Interaction between the arithmetic order on naturals and arithmetic.
 *
 * Order is defined arithmetically in `Nat`:
 * - `m <= n` : `∃c∈ℕ. n = m + c`
 * - `m < n` : `∃c∈ℕ. c ≠ 0 ∧ n = m + c`
 */
object NatOrderAlgebra extends lisa.Main {

  private val a = variable[Ind]
  private val b = variable[Ind]
  private val c = variable[Ind]
  private val d = variable[Ind]
  private val m = variable[Ind]
  private val n = variable[Ind]
  private val k = variable[Ind]
  private val leW = variable[Ind]

  /** Theorem: right monotonicity of addition for `<=`. */
  val addMonoRight = Theorem((m ∈ ℕ, n ∈ ℕ, k ∈ ℕ, m <= n) |- ((m + k) <= (n + k))) {
    val mInℕ = assume(m ∈ ℕ)
    val nInℕ = assume(n ∈ ℕ)
    val kInℕ = assume(k ∈ ℕ)
    val mLeN = assume(m <= n)

    val inst = have(((leW ∈ ℕ) /\ (n === m + leW)) |- ((m + k) <= (n + k))) subproof {
      val conj = assume((leW ∈ ℕ) /\ (n === m + leW))
      val leWInℕ = have(leW ∈ ℕ).by(Tautology.from(conj))
      val nEq = have(n === m + leW).by(Tautology.from(conj))

      val nPlus = have((n + k) === ((m + leW) + k)).by(Congruence.from(nEq))

      val assoc1 = have(((m + leW) + k) === (m + (leW + k))).by(
        Tautology.from(NatAlgebra.addAssoc.of(a := m, b := leW, c := k), mInℕ, leWInℕ, kInℕ)
      )
      val comm = have((leW + k) === (k + leW)).by(Tautology.from(NatAlgebra.addComm.of(m := leW, n := k), leWInℕ, kInℕ))
      val cong = have((m + (leW + k)) === (m + (k + leW))).by(Congruence.from(comm))

      val assoc2 = have(((m + k) + leW) === (m + (k + leW))).by(
        Tautology.from(NatAlgebra.addAssoc.of(a := m, b := k, c := leW), mInℕ, kInℕ, leWInℕ)
      )
      val assoc2r = have((m + (k + leW)) === ((m + k) + leW)).by(Congruence.from(assoc2))
      val rhsEq = have(((m + leW) + k) === ((m + k) + leW)).by(Congruence.from(assoc1, cong, assoc2r))

      val eq = have((n + k) === ((m + k) + leW)).by(Congruence.from(nPlus, rhsEq))
      val w = variable[Ind]
      val leDef = have(((m + k) <= (n + k)) <=> ∃(w, (w ∈ ℕ) /\ ((n + k) === (m + k) + w))).by(
        Restate.from(Nat.le.definition.of(m := (m + k), n := (n + k)))
      )

      val rhs = have((leW ∈ ℕ) /\ ((n + k) === (m + k) + leW)).by(Tautology.from(leWInℕ, eq))
      val ex = have(∃(w, (w ∈ ℕ) /\ ((n + k) === (m + k) + w))).by(RightExists(rhs))
      have(thesis).by(Tautology.from(leDef, ex))
    }

    val leDefMn = have((m <= n) <=> ∃(leW, (leW ∈ ℕ) /\ (n === m + leW))).by(Restate.from(Nat.le.definition.of(m := m, n := n)))
    val exMn = have(∃(leW, (leW ∈ ℕ) /\ (n === m + leW))).by(Tautology.from(leDefMn, mLeN))
    val fromEx = have(∃(leW, (leW ∈ ℕ) /\ (n === m + leW)) |- ((m + k) <= (n + k))).by(LeftExists(inst))
    have(thesis).by(Cut(exMn, fromEx))
  }

  /** Theorem: left monotonicity of addition for `<=`. */
  val addMonoLeft = Theorem((m ∈ ℕ, n ∈ ℕ, k ∈ ℕ, m <= n) |- ((k + m) <= (k + n))) {
    val mInℕ = assume(m ∈ ℕ)
    val nInℕ = assume(n ∈ ℕ)
    val kInℕ = assume(k ∈ ℕ)
    val mLeN = assume(m <= n)

    val inst = have(((leW ∈ ℕ) /\ (n === m + leW)) |- ((k + m) <= (k + n))) subproof {
      val conj = assume((leW ∈ ℕ) /\ (n === m + leW))
      val leWInℕ = have(leW ∈ ℕ).by(Tautology.from(conj))
      val nEq = have(n === m + leW).by(Tautology.from(conj))

      val kPlus = have((k + n) === (k + (m + leW))).by(Congruence.from(nEq))
      val assoc = have((k + (m + leW)) === ((k + m) + leW)).by(
        Tautology.from(NatAlgebra.addAssoc.of(a := k, b := m, c := leW), kInℕ, mInℕ, leWInℕ)
      )
      val eq = have((k + n) === ((k + m) + leW)).by(Congruence.from(kPlus, assoc))

      val w = variable[Ind]
      val leDef = have(((k + m) <= (k + n)) <=> ∃(w, (w ∈ ℕ) /\ ((k + n) === (k + m) + w))).by(
        Restate.from(Nat.le.definition.of(m := (k + m), n := (k + n)))
      )

      val rhs = have((leW ∈ ℕ) /\ ((k + n) === (k + m) + leW)).by(Tautology.from(leWInℕ, eq))
      val ex = have(∃(w, (w ∈ ℕ) /\ ((k + n) === (k + m) + w))).by(RightExists(rhs))
      have(thesis).by(Tautology.from(leDef, ex))
    }

    val leDefMn = have((m <= n) <=> ∃(leW, (leW ∈ ℕ) /\ (n === m + leW))).by(Restate.from(Nat.le.definition.of(m := m, n := n)))
    val exMn = have(∃(leW, (leW ∈ ℕ) /\ (n === m + leW))).by(Tautology.from(leDefMn, mLeN))
    val fromEx = have(∃(leW, (leW ∈ ℕ) /\ (n === m + leW)) |- ((k + m) <= (k + n))).by(LeftExists(inst))
    have(thesis).by(Cut(exMn, fromEx))
  }

  /** Lemma: addition is monotone in both arguments (for `<=`). */
  val addMonoBoth = Lemma((a ∈ ℕ, b ∈ ℕ, c ∈ ℕ, d ∈ ℕ, a <= b, c <= d) |- ((a + c) <= (b + d))) {
    val aInℕ = assume(a ∈ ℕ)
    val bInℕ = assume(b ∈ ℕ)
    val cInℕ = assume(c ∈ ℕ)
    val dInℕ = assume(d ∈ ℕ)
    val aLeB = assume(a <= b)
    val cLeD = assume(c <= d)

    val acInℕ = have((a + c) ∈ ℕ).by(Tautology.from(Nat.addClosed.of(m := a, n := c), aInℕ, cInℕ))
    val bcInℕ = have((b + c) ∈ ℕ).by(Tautology.from(Nat.addClosed.of(m := b, n := c), bInℕ, cInℕ))
    val bdInℕ = have((b + d) ∈ ℕ).by(Tautology.from(Nat.addClosed.of(m := b, n := d), bInℕ, dInℕ))

    val acLeBc = have((a + c) <= (b + c)).by(Tautology.from(addMonoRight.of(m := a, n := b, k := c), aInℕ, bInℕ, cInℕ, aLeB))
    val bcLeBd = have((b + c) <= (b + d)).by(Tautology.from(addMonoLeft.of(m := c, n := d, k := b), cInℕ, dInℕ, bInℕ, cLeD))

    have(thesis).by(Tautology.from(NatOrder.leTrans.of(m := (a + c), n := (b + c), k := (b + d)), acInℕ, bcInℕ, bdInℕ, acLeBc, bcLeBd))
  }

  /** Theorem: right cancellation of addition for `<=` (Isabelle/HOL: `add_le_cancel_right`). */
  val addLeCancelRight = Theorem((m ∈ ℕ, n ∈ ℕ, k ∈ ℕ, (m + k) <= (n + k)) |- (m <= n)) {
    val mInℕ = assume(m ∈ ℕ)
    val nInℕ = assume(n ∈ ℕ)
    val kInℕ = assume(k ∈ ℕ)
    val hyp = assume((m + k) <= (n + k))

    val inst = have(((leW ∈ ℕ) /\ ((n + k) === (m + k) + leW)) |- (m <= n)) subproof {
      val conj = assume((leW ∈ ℕ) /\ ((n + k) === (m + k) + leW))
      val leWInℕ = have(leW ∈ ℕ).by(Tautology.from(conj))
      val eq0 = have((n + k) === (m + k) + leW).by(Tautology.from(conj))

      val mcInℕ = have((m + leW) ∈ ℕ).by(Tautology.from(Nat.addClosed.of(m := m, n := leW), mInℕ, leWInℕ))

      val assoc1 = have(((m + k) + leW) === (m + (k + leW))).by(
        Tautology.from(NatAlgebra.addAssoc.of(a := m, b := k, c := leW), mInℕ, kInℕ, leWInℕ)
      )
      val comm = have((k + leW) === (leW + k)).by(Tautology.from(NatAlgebra.addComm.of(m := k, n := leW), kInℕ, leWInℕ))
      val cong = have((m + (k + leW)) === (m + (leW + k))).by(Congruence.from(comm))
      val assoc2 = have(((m + leW) + k) === (m + (leW + k))).by(
        Tautology.from(NatAlgebra.addAssoc.of(a := m, b := leW, c := k), mInℕ, leWInℕ, kInℕ)
      )
      val assoc2r = have((m + (leW + k)) === ((m + leW) + k)).by(Congruence.from(assoc2))
      val rhsEq = have(((m + k) + leW) === ((m + leW) + k)).by(Congruence.from(assoc1, cong, assoc2r))

      val eq1 = have((n + k) === (m + leW) + k).by(Congruence.from(eq0, rhsEq))
      val nEqMc = have(n === (m + leW)).by(
        Tautology.from(NatAlgebra.addRightCancel.of(a := k, b := n, c := (m + leW)), kInℕ, nInℕ, mcInℕ, eq1)
      )

      val w = variable[Ind]
      val leDef = have((m <= n) <=> ∃(w, (w ∈ ℕ) /\ (n === m + w))).by(Restate.from(Nat.le.definition.of(m := m, n := n)))

      val rhs = have((leW ∈ ℕ) /\ (n === m + leW)).by(Tautology.from(leWInℕ, nEqMc))
      val ex = have(∃(w, (w ∈ ℕ) /\ (n === m + w))).by(RightExists(rhs))
      have(thesis).by(Tautology.from(leDef, ex))
    }

    val w = variable[Ind]
    val leDefHyp = have(((m + k) <= (n + k)) <=> ∃(w, (w ∈ ℕ) /\ ((n + k) === (m + k) + w))).by(
      Restate.from(Nat.le.definition.of(m := (m + k), n := (n + k)))
    )
    val exHyp = have(∃(w, (w ∈ ℕ) /\ ((n + k) === (m + k) + w))).by(Tautology.from(leDefHyp, hyp))
    val fromEx = have(∃(leW, (leW ∈ ℕ) /\ ((n + k) === (m + k) + leW)) |- (m <= n)).by(LeftExists(inst))
    have(thesis).by(Cut(exHyp, fromEx))
  }

  /** Theorem: left cancellation of addition for `<=` (Isabelle/HOL: `add_le_cancel_left`). */
  val addLeCancelLeft = Theorem((m ∈ ℕ, n ∈ ℕ, k ∈ ℕ, (k + m) <= (k + n)) |- (m <= n)) {
    val mInℕ = assume(m ∈ ℕ)
    val nInℕ = assume(n ∈ ℕ)
    val kInℕ = assume(k ∈ ℕ)
    val hyp = assume((k + m) <= (k + n))

    val inst = have(((leW ∈ ℕ) /\ ((k + n) === (k + m) + leW)) |- ((m + k) <= (n + k))) subproof {
      val conj = assume((leW ∈ ℕ) /\ ((k + n) === (k + m) + leW))
      val leWInℕ = have(leW ∈ ℕ).by(Tautology.from(conj))
      val eq0 = have((k + n) === (k + m) + leW).by(Tautology.from(conj))

      val kn = have(k + n === n + k).by(Tautology.from(NatAlgebra.addComm.of(m := k, n := n), kInℕ, nInℕ))
      val knSym = have(n + k === k + n).by(Congruence.from(kn))

      val km = have(k + m === m + k).by(Tautology.from(NatAlgebra.addComm.of(m := k, n := m), kInℕ, mInℕ))
      val rhsCong = have((k + m) + leW === (m + k) + leW).by(Congruence.from(km))

      val eq1 = have(n + k === (k + m) + leW).by(Congruence.from(knSym, eq0))
      val eq2 = have(n + k === (m + k) + leW).by(Congruence.from(eq1, rhsCong))

      val w = variable[Ind]
      val leDef = have(((m + k) <= (n + k)) <=> ∃(w, (w ∈ ℕ) /\ ((n + k) === (m + k) + w))).by(
        Restate.from(Nat.le.definition.of(m := (m + k), n := (n + k)))
      )

      val rhs = have((leW ∈ ℕ) /\ ((n + k) === (m + k) + leW)).by(Tautology.from(leWInℕ, eq2))
      val ex = have(∃(w, (w ∈ ℕ) /\ ((n + k) === (m + k) + w))).by(RightExists(rhs))
      have(thesis).by(Tautology.from(leDef, ex))
    }

    val w = variable[Ind]
    val leDefHyp = have(((k + m) <= (k + n)) <=> ∃(w, (w ∈ ℕ) /\ ((k + n) === (k + m) + w))).by(
      Restate.from(Nat.le.definition.of(m := (k + m), n := (k + n)))
    )
    val exHyp = have(∃(w, (w ∈ ℕ) /\ ((k + n) === (k + m) + w))).by(Tautology.from(leDefHyp, hyp))
    val hypComm = have(∃(leW, (leW ∈ ℕ) /\ ((k + n) === (k + m) + leW)) |- ((m + k) <= (n + k))).by(LeftExists(inst))
    val hyp2 = have((m + k) <= (n + k)).by(Cut(exHyp, hypComm))
    have(thesis).by(Tautology.from(addLeCancelRight.of(m := m, n := n, k := k), mInℕ, nInℕ, kInℕ, hyp2))
  }

  /** Theorem: strict right monotonicity of addition for `<` (Isabelle/HOL: `add_less_mono1`). */
  val addLtMonoRight = Theorem((m ∈ ℕ, n ∈ ℕ, k ∈ ℕ, m < n) |- ((m + k) < (n + k))) {
    val mInℕ = assume(m ∈ ℕ)
    val nInℕ = assume(n ∈ ℕ)
    val kInℕ = assume(k ∈ ℕ)
    val hyp = assume(m < n)

    val inst = have(((leW ∈ ℕ) /\ (leW =/= 0) /\ (n === m + leW)) |- ((m + k) < (n + k))) subproof {
      val conj = assume((leW ∈ ℕ) /\ (leW =/= 0) /\ (n === m + leW))
      val leWInℕ = have(leW ∈ ℕ).by(Tautology.from(conj))
      val leWNe0 = have(leW =/= 0).by(Tautology.from(conj))
      val nEq = have(n === m + leW).by(Tautology.from(conj))

      val nPlus = have((n + k) === ((m + leW) + k)).by(Congruence.from(nEq))

      val assoc1 = have(((m + leW) + k) === (m + (leW + k))).by(
        Tautology.from(NatAlgebra.addAssoc.of(a := m, b := leW, c := k), mInℕ, leWInℕ, kInℕ)
      )
      val comm = have((leW + k) === (k + leW)).by(Tautology.from(NatAlgebra.addComm.of(m := leW, n := k), leWInℕ, kInℕ))
      val cong = have((m + (leW + k)) === (m + (k + leW))).by(Congruence.from(comm))
      val assoc2 = have(((m + k) + leW) === (m + (k + leW))).by(
        Tautology.from(NatAlgebra.addAssoc.of(a := m, b := k, c := leW), mInℕ, kInℕ, leWInℕ)
      )
      val assoc2r = have((m + (k + leW)) === ((m + k) + leW)).by(Congruence.from(assoc2))
      val rhsEq = have(((m + leW) + k) === ((m + k) + leW)).by(Congruence.from(assoc1, cong, assoc2r))

      val eq = have((n + k) === ((m + k) + leW)).by(Congruence.from(nPlus, rhsEq))
      val w = variable[Ind]
      val ltDef = have(((m + k) < (n + k)) <=> ∃(w, (w ∈ ℕ) /\ (w =/= 0) /\ ((n + k) === (m + k) + w))).by(
        Restate.from(Nat.lt.definition.of(m := (m + k), n := (n + k)))
      )

      val rhs = have((leW ∈ ℕ) /\ (leW =/= 0) /\ ((n + k) === (m + k) + leW)).by(Tautology.from(leWInℕ, leWNe0, eq))
      val ex = have(∃(w, (w ∈ ℕ) /\ (w =/= 0) /\ ((n + k) === (m + k) + w))).by(RightExists(rhs))
      have(thesis).by(Tautology.from(ltDef, ex))
    }

    val w = variable[Ind]
    val ltDefHyp = have((m < n) <=> ∃(w, (w ∈ ℕ) /\ (w =/= 0) /\ (n === m + w))).by(Restate.from(Nat.lt.definition.of(m := m, n := n)))
    val exHyp = have(∃(w, (w ∈ ℕ) /\ (w =/= 0) /\ (n === m + w))).by(Tautology.from(ltDefHyp, hyp))
    val fromEx = have(∃(leW, (leW ∈ ℕ) /\ (leW =/= 0) /\ (n === m + leW)) |- ((m + k) < (n + k))).by(LeftExists(inst))
    have(thesis).by(Cut(exHyp, fromEx))
  }

  /** Theorem: strict left monotonicity of addition for `<` (Isabelle/HOL: `add_less_mono2`). */
  val addLtMonoLeft = Theorem((m ∈ ℕ, n ∈ ℕ, k ∈ ℕ, m < n) |- ((k + m) < (k + n))) {
    val mInℕ = assume(m ∈ ℕ)
    val nInℕ = assume(n ∈ ℕ)
    val kInℕ = assume(k ∈ ℕ)
    val hyp = assume(m < n)

    val inst = have(((leW ∈ ℕ) /\ (leW =/= 0) /\ (n === m + leW)) |- ((k + m) < (k + n))) subproof {
      val conj = assume((leW ∈ ℕ) /\ (leW =/= 0) /\ (n === m + leW))
      val leWInℕ = have(leW ∈ ℕ).by(Tautology.from(conj))
      val leWNe0 = have(leW =/= 0).by(Tautology.from(conj))
      val nEq = have(n === m + leW).by(Tautology.from(conj))

      val kPlus = have((k + n) === (k + (m + leW))).by(Congruence.from(nEq))
      val assoc = have((k + (m + leW)) === ((k + m) + leW)).by(
        Tautology.from(NatAlgebra.addAssoc.of(a := k, b := m, c := leW), kInℕ, mInℕ, leWInℕ)
      )
      val eq = have((k + n) === ((k + m) + leW)).by(Congruence.from(kPlus, assoc))

      val w = variable[Ind]
      val ltDef = have(((k + m) < (k + n)) <=> ∃(w, (w ∈ ℕ) /\ (w =/= 0) /\ ((k + n) === (k + m) + w))).by(
        Restate.from(Nat.lt.definition.of(m := (k + m), n := (k + n)))
      )

      val rhs = have((leW ∈ ℕ) /\ (leW =/= 0) /\ ((k + n) === (k + m) + leW)).by(Tautology.from(leWInℕ, leWNe0, eq))
      val ex = have(∃(w, (w ∈ ℕ) /\ (w =/= 0) /\ ((k + n) === (k + m) + w))).by(RightExists(rhs))
      have(thesis).by(Tautology.from(ltDef, ex))
    }

    val w = variable[Ind]
    val ltDefHyp = have((m < n) <=> ∃(w, (w ∈ ℕ) /\ (w =/= 0) /\ (n === m + w))).by(Restate.from(Nat.lt.definition.of(m := m, n := n)))
    val exHyp = have(∃(w, (w ∈ ℕ) /\ (w =/= 0) /\ (n === m + w))).by(Tautology.from(ltDefHyp, hyp))
    val fromEx = have(∃(leW, (leW ∈ ℕ) /\ (leW =/= 0) /\ (n === m + leW)) |- ((k + m) < (k + n))).by(LeftExists(inst))
    have(thesis).by(Cut(exHyp, fromEx))
  }

  /** Theorem: right cancellation of addition for `<` (Isabelle/HOL: `add_less_cancel_right`). */
  val addLtCancelRight = Theorem((m ∈ ℕ, n ∈ ℕ, k ∈ ℕ, (m + k) < (n + k)) |- (m < n)) {
    val mInℕ = assume(m ∈ ℕ)
    val nInℕ = assume(n ∈ ℕ)
    val kInℕ = assume(k ∈ ℕ)
    val hyp = assume((m + k) < (n + k))

    val ltDefHyp = have(((m + k) < (n + k)) <=> ∃(leW, (leW ∈ ℕ) /\ (leW =/= 0) /\ ((n + k) === (m + k) + leW))).by(
      Restate.from(Nat.lt.definition.of(m := (m + k), n := (n + k)))
    )
    val exHyp = have(∃(leW, (leW ∈ ℕ) /\ (leW =/= 0) /\ ((n + k) === (m + k) + leW))).by(Tautology.from(ltDefHyp, hyp))

    val inst = have(((leW ∈ ℕ) /\ (leW =/= 0) /\ ((n + k) === (m + k) + leW)) |- (m < n)) subproof {
      val conj = assume((leW ∈ ℕ) /\ (leW =/= 0) /\ ((n + k) === (m + k) + leW))
      val leWInℕ = have(leW ∈ ℕ).by(Tautology.from(conj))
      val leWNe0 = have(leW =/= 0).by(Tautology.from(conj))
      val eq0 = have((n + k) === (m + k) + leW).by(Tautology.from(conj))

      val assoc = have(((m + k) + leW) === (m + (k + leW))).by(
        Tautology.from(NatAlgebra.addAssoc.of(a := m, b := k, c := leW), mInℕ, kInℕ, leWInℕ)
      )
      val eq1 = have((n + k) === m + (k + leW)).by(Congruence.from(eq0, assoc))

      val comm = have((k + leW) === (leW + k)).by(Tautology.from(NatAlgebra.addComm.of(m := k, n := leW), kInℕ, leWInℕ))
      val cong = have(m + (k + leW) === m + (leW + k)).by(Congruence.from(comm))
      val eq2 = have((n + k) === m + (leW + k)).by(Congruence.from(eq1, cong))

      val assoc2 = have((m + leW) + k === m + (leW + k)).by(
        Tautology.from(NatAlgebra.addAssoc.of(a := m, b := leW, c := k), mInℕ, leWInℕ, kInℕ)
      )
      val assoc2sym = have(m + (leW + k) === (m + leW) + k).by(Congruence.from(assoc2))
      val eq3 = have((n + k) === (m + leW) + k).by(Congruence.from(eq2, assoc2sym))

      val mPlusWInℕ = have((m + leW) ∈ ℕ).by(Tautology.from(Nat.addClosed.of(m := m, n := leW), mInℕ, leWInℕ))
      val nEq = have(n === m + leW).by(
        Tautology.from(NatAlgebra.addRightCancel.of(a := k, b := n, c := (m + leW)), kInℕ, nInℕ, mPlusWInℕ, eq3)
      )

      val ltDef = have((m < n) <=> ∃(leW, (leW ∈ ℕ) /\ (leW =/= 0) /\ (n === m + leW))).by(
        Restate.from(Nat.lt.definition.of(m := m, n := n))
      )
      val rhs = have((leW ∈ ℕ) /\ (leW =/= 0) /\ (n === m + leW)).by(Tautology.from(leWInℕ, leWNe0, nEq))
      val ex = have(∃(leW, (leW ∈ ℕ) /\ (leW =/= 0) /\ (n === m + leW))).by(RightExists(rhs))
      have(thesis).by(Tautology.from(ltDef, ex))
    }

    val fromEx = have(∃(leW, (leW ∈ ℕ) /\ (leW =/= 0) /\ ((n + k) === (m + k) + leW)) |- (m < n)).by(LeftExists(inst))
    have(thesis).by(Cut(exHyp, fromEx))
  }

  ///////////////////////////////
  // Multiplicative strict mono //
  ///////////////////////////////

  /** Theorem: strict right monotonicity of multiplication for `<` (requires `k ≠ 0`). */
  lazy val mulLtMonoRight = Theorem((m ∈ ℕ, n ∈ ℕ, k ∈ ℕ, m < n, k =/= 0) |- ((m * k) < (n * k))) {
    val mInℕ = assume(m ∈ ℕ)
    val nInℕ = assume(n ∈ ℕ)
    val kInℕ = assume(k ∈ ℕ)
    val hyp = assume(m < n)
    val kNe0 = assume(k =/= 0)

    val ltDefHyp = have((m < n) <=> ∃(leW, (leW ∈ ℕ) /\ (leW =/= 0) /\ (n === m + leW))).by(
      Restate.from(Nat.lt.definition.of(m := m, n := n))
    )
    val exHyp = have(∃(leW, (leW ∈ ℕ) /\ (leW =/= 0) /\ (n === m + leW))).by(Tautology.from(ltDefHyp, hyp))

    val inst = have(((leW ∈ ℕ) /\ (leW =/= 0) /\ (n === m + leW)) |- ((m * k) < (n * k))) subproof {
      val conj = assume((leW ∈ ℕ) /\ (leW =/= 0) /\ (n === m + leW))
      val leWInℕ = have(leW ∈ ℕ).by(Tautology.from(conj))
      val leWNe0 = have(leW =/= 0).by(Tautology.from(conj))
      val nEq = have(n === m + leW).by(Tautology.from(conj))

      val wkInℕ = have((leW * k) ∈ ℕ).by(Tautology.from(Nat.mulClosed.of(m := leW, n := k), leWInℕ, kInℕ))
      val wkNe0 = have((leW * k) =/= 0).by(Tautology.from(NatAlgebra.mulNeZero.of(m := leW, n := k), leWInℕ, kInℕ, leWNe0, kNe0))

      val nk = have((n * k) === ((m + leW) * k)).by(Congruence.from(nEq))
      val dist = have(((m + leW) * k) === ((m * k) + (leW * k))).by(
        Tautology.from(NatAlgebra.mulDistribRight.of(a := m, b := leW, c := k), mInℕ, leWInℕ, kInℕ)
      )
      val eq = have((n * k) === (m * k) + (leW * k)).by(Congruence.from(nk, dist))

      val ltDef = have(((m * k) < (n * k)) <=> ∃(leW, (leW ∈ ℕ) /\ (leW =/= 0) /\ ((n * k) === (m * k) + leW))).by(
        Restate.from(Nat.lt.definition.of(m := (m * k), n := (n * k)))
      )

      val rhs = have(((leW * k) ∈ ℕ) /\ ((leW * k) =/= 0) /\ ((n * k) === (m * k) + (leW * k))).by(Tautology.from(wkInℕ, wkNe0, eq))
      val ex = have(∃(leW, (leW ∈ ℕ) /\ (leW =/= 0) /\ ((n * k) === (m * k) + leW))).by(RightExists(rhs))
      have(thesis).by(Tautology.from(ltDef, ex))
    }

    val fromEx = have(∃(leW, (leW ∈ ℕ) /\ (leW =/= 0) /\ (n === m + leW)) |- ((m * k) < (n * k))).by(LeftExists(inst))
    have(thesis).by(Cut(exHyp, fromEx))
  }

  /** Theorem: strict left monotonicity of multiplication for `<` (requires `k ≠ 0`). */
  val mulLtMonoLeft = Theorem((m ∈ ℕ, n ∈ ℕ, k ∈ ℕ, m < n, k =/= 0) |- ((k * m) < (k * n))) {
    val mInℕ = assume(m ∈ ℕ)
    val nInℕ = assume(n ∈ ℕ)
    val kInℕ = assume(k ∈ ℕ)
    val mn = assume(m < n)
    val kNe0 = assume(k =/= 0)

    val km = have((k * m) === (m * k)).by(Tautology.from(NatAlgebra.mulComm.of(m := k, n := m), kInℕ, mInℕ))
    val kn = have((k * n) === (n * k)).by(Tautology.from(NatAlgebra.mulComm.of(m := k, n := n), kInℕ, nInℕ))

    val mono = have((m * k) < (n * k)).by(Tautology.from(mulLtMonoRight.of(m := m, n := n, k := k), mInℕ, nInℕ, kInℕ, mn, kNe0))
    val left = have((k * m) < (n * k)).by(Congruence.from(mono, km))
    have(thesis).by(Congruence.from(left, kn))
  }

  /** Theorem: right monotonicity of multiplication for `<=`. */
  val mulMonoRight = Theorem((m ∈ ℕ, n ∈ ℕ, k ∈ ℕ, m <= n) |- ((m * k) <= (n * k))) {
    val mInℕ = assume(m ∈ ℕ)
    val nInℕ = assume(n ∈ ℕ)
    val kInℕ = assume(k ∈ ℕ)
    val mLeN = assume(m <= n)

    val inst = have(((leW ∈ ℕ) /\ (n === m + leW)) |- ((m * k) <= (n * k))) subproof {
      val conj = assume((leW ∈ ℕ) /\ (n === m + leW))
      val leWInℕ = have(leW ∈ ℕ).by(Tautology.from(conj))
      val nEq = have(n === m + leW).by(Tautology.from(conj))

      val leWkInℕ = have((leW * k) ∈ ℕ).by(Tautology.from(Nat.mulClosed.of(m := leW, n := k), leWInℕ, kInℕ))

      val nk = have((n * k) === ((m + leW) * k)).by(Congruence.from(nEq))
      val dist = have(((m + leW) * k) === ((m * k) + (leW * k))).by(
        Tautology.from(NatAlgebra.mulDistribRight.of(a := m, b := leW, c := k), mInℕ, leWInℕ, kInℕ)
      )
      val eq = have((n * k) === ((m * k) + (leW * k))).by(Congruence.from(nk, dist))

      val w = variable[Ind]
      val leDef = have(((m * k) <= (n * k)) <=> ∃(w, (w ∈ ℕ) /\ ((n * k) === (m * k) + w))).by(
        Restate.from(Nat.le.definition.of(m := (m * k), n := (n * k)))
      )

      val rhs = have(((leW * k) ∈ ℕ) /\ ((n * k) === (m * k) + (leW * k))).by(Tautology.from(leWkInℕ, eq))
      val ex = have(∃(w, (w ∈ ℕ) /\ ((n * k) === (m * k) + w))).by(RightExists(rhs))
      have(thesis).by(Tautology.from(leDef, ex))
    }

    val leDefMn = have((m <= n) <=> ∃(leW, (leW ∈ ℕ) /\ (n === m + leW))).by(Restate.from(Nat.le.definition.of(m := m, n := n)))
    val exMn = have(∃(leW, (leW ∈ ℕ) /\ (n === m + leW))).by(Tautology.from(leDefMn, mLeN))
    val fromEx = have(∃(leW, (leW ∈ ℕ) /\ (n === m + leW)) |- ((m * k) <= (n * k))).by(LeftExists(inst))
    have(thesis).by(Cut(exMn, fromEx))
  }

  /** Theorem: left monotonicity of multiplication for `<=`. */
  val mulMonoLeft = Theorem((m ∈ ℕ, n ∈ ℕ, k ∈ ℕ, m <= n) |- ((k * m) <= (k * n))) {
    val mInℕ = assume(m ∈ ℕ)
    val nInℕ = assume(n ∈ ℕ)
    val kInℕ = assume(k ∈ ℕ)
    val mLeN = assume(m <= n)

    val inst = have(((leW ∈ ℕ) /\ (n === m + leW)) |- ((k * m) <= (k * n))) subproof {
      val conj = assume((leW ∈ ℕ) /\ (n === m + leW))
      val leWInℕ = have(leW ∈ ℕ).by(Tautology.from(conj))
      val nEq = have(n === m + leW).by(Tautology.from(conj))

      val kwInℕ = have((k * leW) ∈ ℕ).by(Tautology.from(Nat.mulClosed.of(m := k, n := leW), kInℕ, leWInℕ))

      val kn = have((k * n) === (k * (m + leW))).by(Congruence.from(nEq))
      val dist = have((k * (m + leW)) === ((k * m) + (k * leW))).by(
        Tautology.from(NatAlgebra.mulDistribLeft.of(a := k, b := m, c := leW), kInℕ, mInℕ, leWInℕ)
      )
      val eq = have((k * n) === ((k * m) + (k * leW))).by(Congruence.from(kn, dist))

      val w = variable[Ind]
      val leDef = have(((k * m) <= (k * n)) <=> ∃(w, (w ∈ ℕ) /\ ((k * n) === (k * m) + w))).by(
        Restate.from(Nat.le.definition.of(m := (k * m), n := (k * n)))
      )

      val rhs = have(((k * leW) ∈ ℕ) /\ ((k * n) === (k * m) + (k * leW))).by(Tautology.from(kwInℕ, eq))
      val ex = have(∃(w, (w ∈ ℕ) /\ ((k * n) === (k * m) + w))).by(RightExists(rhs))
      have(thesis).by(Tautology.from(leDef, ex))
    }

    val leDefMn = have((m <= n) <=> ∃(leW, (leW ∈ ℕ) /\ (n === m + leW))).by(Restate.from(Nat.le.definition.of(m := m, n := n)))
    val exMn = have(∃(leW, (leW ∈ ℕ) /\ (n === m + leW))).by(Tautology.from(leDefMn, mLeN))
    val fromEx = have(∃(leW, (leW ∈ ℕ) /\ (n === m + leW)) |- ((k * m) <= (k * n))).by(LeftExists(inst))
    have(thesis).by(Cut(exMn, fromEx))
  }
}
