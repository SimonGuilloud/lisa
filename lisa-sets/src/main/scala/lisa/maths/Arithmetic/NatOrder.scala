package lisa.maths.Arithmetic

import lisa.maths.Arithmetic.Predef.{*, given}
import lisa.maths.Arithmetic.Syntax.{*, given}
import lisa.maths.Quantifiers

/**
 * Basic order on naturals, defined arithmetically.
 *
 * Definitions (in `Nat`):
 * - `m <= n` : `∃c∈ℕ. n = m + c`
 * - `m < n` : `∃c∈ℕ. c ≠ 0 ∧ n = m + c`
 */
object NatOrder extends lisa.Main {

  private val m = variable[Ind]
  private val n = variable[Ind]
  private val k = variable[Ind]
  private val a = variable[Ind]
  private val b = variable[Ind]
  private val w = variable[Ind]

  /** Lemma: unfolding of `<=` (definition). */
  val leUnfold = Lemma((m <= n) <=> ∃(w, (w ∈ ℕ) /\ (n === m + w))) {
    have(thesis).by(Restate.from(Nat.le.definition.of(m := m, n := n)))
  }

  /** Lemma: unfolding of `<` (definition). */
  val ltUnfold = Lemma((m < n) <=> ∃(w, (w ∈ ℕ) /\ (w =/= 0) /\ (n === m + w))) {
    have(thesis).by(Restate.from(Nat.lt.definition.of(m := m, n := n)))
  }

  /** Theorem: introduction rule for `<=` from a witness. */
  val leIntro = Theorem((m ∈ ℕ, n ∈ ℕ, a ∈ ℕ, n === m + a) |- (m <= n)) {
    val mInℕ = assume(m ∈ ℕ)
    val nInℕ = assume(n ∈ ℕ)
    val aInℕ = assume(a ∈ ℕ)
    val nEq = assume(n === m + a)

    val rhs = have((a ∈ ℕ) /\ (n === m + a)).by(Tautology.from(aInℕ, nEq))
    val ex = have(∃(w, (w ∈ ℕ) /\ (n === m + w))).by(RightExists(rhs))
    have(thesis).by(Tautology.from(leUnfold.of(m := m, n := n), ex))
  }

  /** Lemma: elimination rule for `<=` to a witness. */
  val leElim = Lemma((m <= n) |- ∃(w, (w ∈ ℕ) /\ (n === m + w))) {
    val hyp = assume(m <= n)
    have(thesis).by(Tautology.from(leUnfold.of(m := m, n := n), hyp))
  }

  /** Theorem: introduction rule for `<` from a nonzero witness. */
  val ltIntro = Theorem((m ∈ ℕ, n ∈ ℕ, a ∈ ℕ, a =/= 0, n === m + a) |- (m < n)) {
    val mInℕ = assume(m ∈ ℕ)
    val nInℕ = assume(n ∈ ℕ)
    val aInℕ = assume(a ∈ ℕ)
    val aNe0 = assume(a =/= 0)
    val nEq = assume(n === m + a)

    val rhs = have((a ∈ ℕ) /\ (a =/= 0) /\ (n === m + a)).by(Tautology.from(aInℕ, aNe0, nEq))
    val ex = have(∃(w, (w ∈ ℕ) /\ (w =/= 0) /\ (n === m + w))).by(RightExists(rhs))
    have(thesis).by(Tautology.from(ltUnfold.of(m := m, n := n), ex))
  }

  /** Lemma: elimination rule for `<` to a nonzero witness. */
  val ltElim = Lemma((m < n) |- ∃(w, (w ∈ ℕ) /\ (w =/= 0) /\ (n === m + w))) {
    val hyp = assume(m < n)
    have(thesis).by(Tautology.from(ltUnfold.of(m := m, n := n), hyp))
  }

  /** Lemma: reflexivity of `<=` on naturals. */
  val leRefl = Lemma(n ∈ ℕ |- (n <= n)) {
    val nInℕ = assume(n ∈ ℕ)
    val w = variable[Ind]

    val leDef = have((n <= n) <=> ∃(w, (w ∈ ℕ) /\ (n === n + w))).by(Restate.from(Nat.le.definition.of(m := n, n := n)))
    val zInℕ = have(0 ∈ ℕ).by(Restate.from(Nat.zeroInℕ))
    val n0Eq = have(n + 0 === n).by(Tautology.from(NatAlgebra.addZeroRight.of(m := n), nInℕ))
    val eq = have(n === n + 0).by(Congruence.from(n0Eq))
    val rhs = have((0 ∈ ℕ) /\ (n === n + 0)).by(Tautology.from(zInℕ, eq))
    val ex = have(∃(w, (w ∈ ℕ) /\ (n === n + w))).by(RightExists(rhs))
    have(thesis).by(Tautology.from(leDef, ex))
  }

  /** Lemma: `m < n` implies `m <= n` (for naturals). */
  val ltToLe = Lemma((m ∈ ℕ, n ∈ ℕ, m < n) |- (m <= n)) {
    val mInℕ = assume(m ∈ ℕ)
    val nInℕ = assume(n ∈ ℕ)
    val mLtN = assume(m < n)

    val w = variable[Ind]
    val ltDef = have((m < n) <=> ∃(w, (w ∈ ℕ) /\ (w =/= 0) /\ (n === m + w))).by(Restate.from(Nat.lt.definition.of(m := m, n := n)))
    val leDef = have((m <= n) <=> ∃(w, (w ∈ ℕ) /\ (n === m + w))).by(Restate.from(Nat.le.definition.of(m := m, n := n)))

    val Pw = λ(w, (w ∈ ℕ) /\ (w =/= 0) /\ (n === m + w))
    val w0 = ε(w, Pw(w))
    val exLt = have(∃(w, Pw(w))).by(Tautology.from(ltDef, mLtN))
    val w0Prop = have(∃(w, Pw(w)) |- Pw(w0)).by(Tautology.from(Quantifiers.existsEpsilon.of(x := w, P := Pw)))
    val w0Info = have(Pw(w0)).by(Cut(exLt, w0Prop))

    val w0Inℕ = have(w0 ∈ ℕ).by(Tautology.from(w0Info))
    val nEq = have(n === m + w0).by(Tautology.from(w0Info))

    val rhs = have((w0 ∈ ℕ) /\ (n === m + w0)).by(Tautology.from(w0Inℕ, nEq))
    val ex = have(∃(w, (w ∈ ℕ) /\ (n === m + w))).by(RightExists(rhs))
    have(thesis).by(Tautology.from(leDef, ex))
  }

  /** Lemma: transitivity of `<=` on naturals. */
  val leTrans = Lemma((m ∈ ℕ, n ∈ ℕ, k ∈ ℕ, m <= n, n <= k) |- (m <= k)) {
    val mInℕ = assume(m ∈ ℕ)
    val nInℕ = assume(n ∈ ℕ)
    val kInℕ = assume(k ∈ ℕ)
    val mn = assume(m <= n)
    val nk = assume(n <= k)

    val c0 = variable[Ind]

    val Pmn = λ(c0, (c0 ∈ ℕ) /\ (n === m + c0))
    val Pnk = λ(c0, (c0 ∈ ℕ) /\ (k === n + c0))

    val leDefMn = have((m <= n) <=> ∃(c0, Pmn(c0))).by(Restate.from(Nat.le.definition.of(m := m, n := n)))
    val leDefNk = have((n <= k) <=> ∃(c0, Pnk(c0))).by(Restate.from(Nat.le.definition.of(m := n, n := k)))

    val exMn = have(∃(c0, Pmn(c0))).by(Tautology.from(leDefMn, mn))
    val exNk = have(∃(c0, Pnk(c0))).by(Tautology.from(leDefNk, nk))

    val a0 = ε(c0, Pmn(c0))
    val b0 = ε(c0, Pnk(c0))

    val aProp = have(∃(c0, Pmn(c0)) |- Pmn(a0)).by(Tautology.from(Quantifiers.existsEpsilon.of(x := c0, P := Pmn)))
    val bProp = have(∃(c0, Pnk(c0)) |- Pnk(b0)).by(Tautology.from(Quantifiers.existsEpsilon.of(x := c0, P := Pnk)))

    val aInfo = have(Pmn(a0)).by(Cut(exMn, aProp))
    val bInfo = have(Pnk(b0)).by(Cut(exNk, bProp))

    val aInℕ = have(a0 ∈ ℕ).by(Tautology.from(aInfo))
    val nEq = have(n === m + a0).by(Tautology.from(aInfo))

    val bInℕ = have(b0 ∈ ℕ).by(Tautology.from(bInfo))
    val kEq = have(k === n + b0).by(Tautology.from(bInfo))

    val abInℕ = have((a0 + b0) ∈ ℕ).by(Tautology.from(Nat.addClosed.of(m := a0, n := b0), aInℕ, bInℕ))

    val congRhs = have((n === (m + a0)) |- ((n + b0) === ((m + a0) + b0))).by(Congruence)
    val rhsEq = have((n + b0) === ((m + a0) + b0)).by(Cut(nEq, congRhs))

    val trans1 = have((k === (n + b0), (n + b0) === ((m + a0) + b0)) |- k === ((m + a0) + b0)).by(Congruence)
    val kEq2_0 = have((n + b0) === ((m + a0) + b0) |- k === ((m + a0) + b0)).by(Cut(kEq, trans1))
    val kEq2 = have(k === ((m + a0) + b0)).by(Cut(rhsEq, kEq2_0))

    val assoc = have(((m + a0) + b0) === (m + (a0 + b0))).by(Tautology.from(NatAlgebra.addAssoc.of(a := m, b := a0, c := b0), mInℕ, aInℕ, bInℕ))
    val trans2 = have((k === ((m + a0) + b0), ((m + a0) + b0) === (m + (a0 + b0))) |- k === (m + (a0 + b0))).by(Congruence)
    val kEq3_0 = have(((m + a0) + b0) === (m + (a0 + b0)) |- k === (m + (a0 + b0))).by(Cut(kEq2, trans2))
    val kEq3 = have(k === (m + (a0 + b0))).by(Cut(assoc, kEq3_0))

    val w = variable[Ind]
    val leDef = have((m <= k) <=> ∃(w, (w ∈ ℕ) /\ (k === m + w))).by(Restate.from(Nat.le.definition.of(m := m, n := k)))

    val rhs = have(((a0 + b0) ∈ ℕ) /\ (k === m + (a0 + b0))).by(Tautology.from(abInℕ, kEq3))
    val ex = have(∃(w, (w ∈ ℕ) /\ (k === m + w))).by(RightExists(rhs))
    have(thesis).by(Tautology.from(leDef, ex))
  }

  /** Theorem: `0 <= n` for naturals `n`. */
  val zeroLe = Theorem(n ∈ ℕ |- (0 <= n)) {
    val nInℕ = assume(n ∈ ℕ)

    val eq0 = have(0 + n === n).by(Cut(nInℕ, NatAlgebra.addZeroLeft.of(n := n)))
    val eq = have(n === 0 + n).by(Congruence.from(eq0))
    have(thesis).by(Tautology.from(leIntro.of(m := 0, n := n, a := n), Nat.zeroInℕ, nInℕ, nInℕ, eq))
  }

  /** Theorem: `n <= n + k` for naturals `n,k` (right-addition is nondecreasing). */
  val leAddRight = Theorem((n ∈ ℕ, k ∈ ℕ) |- (n <= (n + k))) {
    val nInℕ = assume(n ∈ ℕ)
    val kInℕ = assume(k ∈ ℕ)
    val eq = have((n + k) === (n + k)).by(Restate)
    have(thesis).by(Tautology.from(leIntro.of(m := n, n := (n + k), a := k), nInℕ, Nat.addClosed.of(m := n, n := k), kInℕ, eq))
  }

  /** Theorem: `n <= Succ(n)` for naturals `n`. */
  val leSuccSelf = Theorem(n ∈ ℕ |- (n <= Succ(n))) {
    val nInℕ = assume(n ∈ ℕ)
    val oneInℕ = have(1 ∈ ℕ).by(Restate.from(Nat.oneInℕ))
    val add1 = have(n + 1 === Succ(n)).by(Cut(nInℕ, NatAlgebra.addOneRight.of(n := n)))
    val eq = have(Succ(n) === n + 1).by(Congruence.from(add1))
    have(thesis).by(Tautology.from(leIntro.of(m := n, n := Succ(n), a := 1), nInℕ, Nat.succClosed.of(n := n), oneInℕ, eq))
  }

  /** Theorem: `n < Succ(n)` for naturals `n`. */
  val ltSuccSelf = Theorem(n ∈ ℕ |- (n < Succ(n))) {
    val nInℕ = assume(n ∈ ℕ)
    val oneInℕ = have(1 ∈ ℕ).by(Restate.from(Nat.oneInℕ))
    val oneNe0 = have(1 =/= 0).by(Tautology.from(Nat.succNeZero.of(n := 0), Nat.zeroInℕ))
    val add1 = have(n + 1 === Succ(n)).by(Cut(nInℕ, NatAlgebra.addOneRight.of(n := n)))
    val eq = have(Succ(n) === n + 1).by(Congruence.from(add1))
    have(thesis).by(Tautology.from(ltIntro.of(m := n, n := Succ(n), a := 1), nInℕ, Nat.succClosed.of(n := n), oneInℕ, oneNe0, eq))
  }

  /** Theorem: `¬(n < n)` for naturals `n` (irreflexivity of `<`). */
  val ltIrrefl = Theorem(n ∈ ℕ |- ¬(n < n)) {
    val nInℕ = assume(n ∈ ℕ)

    have(¬(n < n)) subproof {
      val hyp = assume(n < n)

      val ex = have(∃(w, (w ∈ ℕ) /\ (w =/= 0) /\ (n === n + w))).by(Tautology.from(ltUnfold.of(m := n, n := n), hyp))
      val Pw = λ(w, (w ∈ ℕ) /\ (w =/= 0) /\ (n === n + w))
      val w0 = ε(w, Pw(w))
      val w0Prop = have(∃(w, Pw(w)) |- Pw(w0)).by(Tautology.from(Quantifiers.existsEpsilon.of(x := w, P := Pw)))
      val w0Info = have(Pw(w0)).by(Cut(ex, w0Prop))

      val w0Inℕ = have(w0 ∈ ℕ).by(Tautology.from(w0Info))
      val w0Ne0 = have(w0 =/= 0).by(Tautology.from(w0Info))
      val eq0 = have(n === n + w0).by(Tautology.from(w0Info))
      val eq = have(n + w0 === n).by(Congruence.from(eq0))

      val iff = have((n + w0 === n) <=> (w0 === 0)).by(Tautology.from(NatAlgebra.addEqSelfIff.of(m := n, n := w0), nInℕ, w0Inℕ))
      val w0Eq0 = have(w0 === 0).by(Tautology.from(iff, eq))
      val contra = have(¬(w0 === 0)).by(Restate.from(w0Ne0))
      have(⊥).by(Tautology.from(w0Eq0, contra))
    }
  }

  /** Lemma: `m < n` implies `m =/= n` (for naturals). */
  val ltNeq = Lemma((m ∈ ℕ, n ∈ ℕ, m < n) |- (m =/= n)) {
    val mInℕ = assume(m ∈ ℕ)
    val nInℕ = assume(n ∈ ℕ)
    val mLtN = assume(m < n)

    have(m =/= n) subproof {
      val meq = assume(m === n)
      val nLtN = have(n < n).by(Congruence.from(mLtN, meq))
      val irr = have(¬(n < n)).by(Tautology.from(ltIrrefl.of(n := n), nInℕ))
      have(⊥).by(Tautology.from(nLtN, irr))
    }
  }

  /** Theorem: transitivity of `<` on naturals. */
  val ltTrans = Theorem((m ∈ ℕ, n ∈ ℕ, k ∈ ℕ, m < n, n < k) |- (m < k)) {
    val mInℕ = assume(m ∈ ℕ)
    val nInℕ = assume(n ∈ ℕ)
    val kInℕ = assume(k ∈ ℕ)
    val mn = assume(m < n)
    val nk = assume(n < k)

    val exMn = have(∃(w, (w ∈ ℕ) /\ (w =/= 0) /\ (n === m + w))).by(Tautology.from(ltUnfold.of(m := m, n := n), mn))
    val exNk = have(∃(w, (w ∈ ℕ) /\ (w =/= 0) /\ (k === n + w))).by(Tautology.from(ltUnfold.of(m := n, n := k), nk))

    val Pmn = λ(w, (w ∈ ℕ) /\ (w =/= 0) /\ (n === m + w))
    val Pnk = λ(w, (w ∈ ℕ) /\ (w =/= 0) /\ (k === n + w))

    val a0 = ε(w, Pmn(w))
    val b0 = ε(w, Pnk(w))

    val a0Prop = have(∃(w, Pmn(w)) |- Pmn(a0)).by(Tautology.from(Quantifiers.existsEpsilon.of(x := w, P := Pmn)))
    val b0Prop = have(∃(w, Pnk(w)) |- Pnk(b0)).by(Tautology.from(Quantifiers.existsEpsilon.of(x := w, P := Pnk)))

    val a0Info = have(Pmn(a0)).by(Cut(exMn, a0Prop))
    val b0Info = have(Pnk(b0)).by(Cut(exNk, b0Prop))

    val a0Inℕ = have(a0 ∈ ℕ).by(Tautology.from(a0Info))
    val a0Ne0 = have(a0 =/= 0).by(Tautology.from(a0Info))
    val nEq = have(n === m + a0).by(Tautology.from(a0Info))

    val b0Inℕ = have(b0 ∈ ℕ).by(Tautology.from(b0Info))
    val kEq = have(k === n + b0).by(Tautology.from(b0Info))

    val abInℕ = have((a0 + b0) ∈ ℕ).by(Tautology.from(Nat.addClosed.of(m := a0, n := b0), a0Inℕ, b0Inℕ))
    val abNe0 = have((a0 + b0) =/= 0).by(Tautology.from(NatAlgebra.addNeZeroLeft.of(m := a0, n := b0), a0Inℕ, b0Inℕ, a0Ne0))

    val congRhs = have((n === (m + a0)) |- ((n + b0) === ((m + a0) + b0))).by(Congruence)
    val rhsEq = have((n + b0) === ((m + a0) + b0)).by(Cut(nEq, congRhs))

    val trans1 = have((k === (n + b0), (n + b0) === ((m + a0) + b0)) |- k === ((m + a0) + b0)).by(Congruence)
    val kEq2_0 = have((n + b0) === ((m + a0) + b0) |- k === ((m + a0) + b0)).by(Cut(kEq, trans1))
    val kEq2 = have(k === ((m + a0) + b0)).by(Cut(rhsEq, kEq2_0))

    val assoc = have(((m + a0) + b0) === (m + (a0 + b0))).by(Tautology.from(NatAlgebra.addAssoc.of(a := m, b := a0, c := b0), mInℕ, a0Inℕ, b0Inℕ))
    val trans2 = have((k === ((m + a0) + b0), ((m + a0) + b0) === (m + (a0 + b0))) |- k === (m + (a0 + b0))).by(Congruence)
    val kEq3_0 = have(((m + a0) + b0) === (m + (a0 + b0)) |- k === (m + (a0 + b0))).by(Cut(kEq2, trans2))
    val kEq3 = have(k === (m + (a0 + b0))).by(Cut(assoc, kEq3_0))

    have(thesis).by(Tautology.from(ltIntro.of(m := m, n := k, a := (a0 + b0)), mInℕ, kInℕ, abInℕ, abNe0, kEq3))
  }

  /** Theorem: antisymmetry of `<=` on naturals. */
  val leAntiSym = Theorem((m ∈ ℕ, n ∈ ℕ, m <= n, n <= m) |- (m === n)) {
    val mInℕ = assume(m ∈ ℕ)
    val nInℕ = assume(n ∈ ℕ)
    val mn = assume(m <= n)
    val nm = assume(n <= m)

    val exMn = have(∃(w, (w ∈ ℕ) /\ (n === m + w))).by(Tautology.from(leUnfold.of(m := m, n := n), mn))
    val exNm = have(∃(w, (w ∈ ℕ) /\ (m === n + w))).by(Tautology.from(leUnfold.of(m := n, n := m), nm))

    val Pmn = λ(w, (w ∈ ℕ) /\ (n === m + w))
    val Pnm = λ(w, (w ∈ ℕ) /\ (m === n + w))

    val a0 = ε(w, Pmn(w))
    val b0 = ε(w, Pnm(w))

    val a0Prop = have(∃(w, Pmn(w)) |- Pmn(a0)).by(Tautology.from(Quantifiers.existsEpsilon.of(x := w, P := Pmn)))
    val b0Prop = have(∃(w, Pnm(w)) |- Pnm(b0)).by(Tautology.from(Quantifiers.existsEpsilon.of(x := w, P := Pnm)))

    val a0Info = have(Pmn(a0)).by(Cut(exMn, a0Prop))
    val b0Info = have(Pnm(b0)).by(Cut(exNm, b0Prop))

    val a0Inℕ = have(a0 ∈ ℕ).by(Tautology.from(a0Info))
    val nEq = have(n === m + a0).by(Tautology.from(a0Info))

    val b0Inℕ = have(b0 ∈ ℕ).by(Tautology.from(b0Info))
    val mEq = have(m === n + b0).by(Tautology.from(b0Info))

    // Substitute `n = m + a0` into `m = n + b0`.
    val congRhs = have((n === (m + a0)) |- ((n + b0) === ((m + a0) + b0))).by(Congruence)
    val rhsEq = have((n + b0) === ((m + a0) + b0)).by(Cut(nEq, congRhs))

    val trans1 = have((m === (n + b0), (n + b0) === ((m + a0) + b0)) |- m === ((m + a0) + b0)).by(Congruence)
    val mEq2_0 = have((n + b0) === ((m + a0) + b0) |- m === ((m + a0) + b0)).by(Cut(mEq, trans1))
    val mEq2 = have(m === ((m + a0) + b0)).by(Cut(rhsEq, mEq2_0))

    val assoc = have(((m + a0) + b0) === (m + (a0 + b0))).by(Tautology.from(NatAlgebra.addAssoc.of(a := m, b := a0, c := b0), mInℕ, a0Inℕ, b0Inℕ))
    val trans2 = have((m === ((m + a0) + b0), ((m + a0) + b0) === (m + (a0 + b0))) |- m === (m + (a0 + b0))).by(Congruence)
    val mEq3_0 = have(((m + a0) + b0) === (m + (a0 + b0)) |- m === (m + (a0 + b0))).by(Cut(mEq2, trans2))
    val mEq3 = have(m === (m + (a0 + b0))).by(Cut(assoc, mEq3_0))
    val mEq3r = have((m + (a0 + b0)) === m).by(Congruence.from(mEq3))

    val abInℕ = have((a0 + b0) ∈ ℕ).by(Tautology.from(Nat.addClosed.of(m := a0, n := b0), a0Inℕ, b0Inℕ))
    val iff = have(((m + (a0 + b0)) === m) <=> ((a0 + b0) === 0)).by(Tautology.from(NatAlgebra.addEqSelfIff.of(m := m, n := (a0 + b0)), mInℕ, abInℕ))
    val abEq0 = have((a0 + b0) === 0).by(Tautology.from(iff, mEq3r))

    val iff0 = have(((a0 + b0) === 0) <=> ((a0 === 0) /\ (b0 === 0))).by(Tautology.from(NatAlgebra.addEqZeroIff.of(m := a0, n := b0), a0Inℕ, b0Inℕ))
    val both0 = have((a0 === 0) /\ (b0 === 0)).by(Tautology.from(iff0, abEq0))
    val a0Eq0 = have(a0 === 0).by(Tautology.from(both0))

    val nEq2 = have(n === m + 0).by(Congruence.from(nEq, a0Eq0))
    val add0 = have(m + 0 === m).by(Tautology.from(NatAlgebra.addZeroRight.of(m := m), mInℕ))
    val nEqm = have(n === m).by(Congruence.from(nEq2, add0))

    have(thesis).by(Congruence.from(nEqm))
  }

  /** Lemma: closure of `<=` on the right: if `m ∈ ℕ` and `m <= n` then `n ∈ ℕ`. */
  val leClosedRight = Lemma((m ∈ ℕ, m <= n) |- (n ∈ ℕ)) {
    val mInℕ = assume(m ∈ ℕ)
    val mn = assume(m <= n)
    val ex = have(∃(w, (w ∈ ℕ) /\ (n === m + w))).by(Tautology.from(leUnfold.of(m := m, n := n), mn))

    have(∃(w, (w ∈ ℕ) /\ (n === m + w)) |- n ∈ ℕ) subproof {
      assume(∃(w, (w ∈ ℕ) /\ (n === m + w)))

      have((w ∈ ℕ) /\ (n === m + w) |- n ∈ ℕ) subproof {
        val conj = assume((w ∈ ℕ) /\ (n === m + w))
        val wInℕ = have(w ∈ ℕ).by(Tautology.from(conj))
        val eq = have(n === m + w).by(Tautology.from(conj))
        val sumInℕ = have((m + w) ∈ ℕ).by(Tautology.from(Nat.addClosed.of(m := m, n := w), mInℕ, wInℕ))
        have(thesis).by(Congruence.from(eq, sumInℕ))
      }
      thenHave(thesis).by(LeftExists)
    }

    have(thesis).by(Cut(ex, lastStep))
  }

  /** Lemma: closure of `<` on the right: if `m ∈ ℕ` and `m < n` then `n ∈ ℕ`. */
  val ltClosedRight = Lemma((m ∈ ℕ, m < n) |- (n ∈ ℕ)) {
    val mInℕ = assume(m ∈ ℕ)
    val mn = assume(m < n)
    val ex = have(∃(w, (w ∈ ℕ) /\ (w =/= 0) /\ (n === m + w))).by(Tautology.from(ltUnfold.of(m := m, n := n), mn))

    have(∃(w, (w ∈ ℕ) /\ (w =/= 0) /\ (n === m + w)) |- n ∈ ℕ) subproof {
      assume(∃(w, (w ∈ ℕ) /\ (w =/= 0) /\ (n === m + w)))

      have((w ∈ ℕ) /\ (w =/= 0) /\ (n === m + w) |- n ∈ ℕ) subproof {
        val conj = assume((w ∈ ℕ) /\ (w =/= 0) /\ (n === m + w))
        val wInℕ = have(w ∈ ℕ).by(Tautology.from(conj))
        val eq = have(n === m + w).by(Tautology.from(conj))
        val sumInℕ = have((m + w) ∈ ℕ).by(Tautology.from(Nat.addClosed.of(m := m, n := w), mInℕ, wInℕ))
        have(thesis).by(Congruence.from(eq, sumInℕ))
      }
      thenHave(thesis).by(LeftExists)
    }

    have(thesis).by(Cut(ex, lastStep))
  }

  /** Lemma: `n <= 0` iff `n = 0` (for naturals). */
  val leZeroRightIff = Lemma(n ∈ ℕ |- ((n <= 0) <=> (n === 0))) {
    val nInℕ = assume(n ∈ ℕ)

    val `==>` = have(n <= 0 |- n === 0) subproof {
      val nLe0 = assume(n <= 0)
      val ex = have(∃(w, (w ∈ ℕ) /\ (0 === n + w))).by(Tautology.from(leUnfold.of(m := n, n := 0), nLe0))

      val Pw = λ(w, (w ∈ ℕ) /\ (0 === n + w))
      val w0 = ε(w, Pw(w))
      val w0Prop = have(∃(w, Pw(w)) |- Pw(w0)).by(Tautology.from(Quantifiers.existsEpsilon.of(x := w, P := Pw)))
      val w0Info = have(Pw(w0)).by(Cut(ex, w0Prop))
      val w0Inℕ = have(w0 ∈ ℕ).by(Tautology.from(w0Info))
      val eq0 = have(0 === n + w0).by(Tautology.from(w0Info))
      val eq = have(n + w0 === 0).by(Congruence.from(eq0))

      val iff0 = have((n + w0 === 0) <=> ((n === 0) /\ (w0 === 0))).by(Tautology.from(NatAlgebra.addEqZeroIff.of(m := n, n := w0), nInℕ, w0Inℕ))
      val both0 = have((n === 0) /\ (w0 === 0)).by(Tautology.from(iff0, eq))
      have(thesis).by(Tautology.from(both0))
    }

    val `<==` = have(n === 0 |- n <= 0) subproof {
      val nEq0 = assume(n === 0)
      val zInℕ = have(0 ∈ ℕ).by(Restate.from(Nat.zeroInℕ))

      val add0 = have(n + 0 === n).by(Tautology.from(NatAlgebra.addZeroRight.of(m := n), nInℕ))
      val n0Eq0 = have(n + 0 === 0).by(Congruence.from(add0, nEq0))
      val eq = have(0 === n + 0).by(Congruence.from(n0Eq0))

      val rhs = have((0 ∈ ℕ) /\ (0 === n + 0)).by(Tautology.from(zInℕ, eq))
      val ex = have(∃(w, (w ∈ ℕ) /\ (0 === n + w))).by(RightExists(rhs))
      have(thesis).by(Tautology.from(leUnfold.of(m := n, n := 0), ex))
    }

    have(thesis).by(Tautology.from(`==>`, `<==`))
  }

  /** Lemma: `n < 0` is impossible for naturals `n`. */
  val ltZeroFalse = Lemma(n ∈ ℕ |- ¬(n < 0)) {
    val nInℕ = assume(n ∈ ℕ)

    have(¬(n < 0)) subproof {
      val hyp = assume(n < 0)

      val ex = have(∃(w, (w ∈ ℕ) /\ (w =/= 0) /\ (0 === n + w))).by(Tautology.from(ltUnfold.of(m := n, n := 0), hyp))

      val Pw = λ(w, (w ∈ ℕ) /\ (w =/= 0) /\ (0 === n + w))
      val w0 = ε(w, Pw(w))
      val w0Prop = have(∃(w, Pw(w)) |- Pw(w0)).by(Tautology.from(Quantifiers.existsEpsilon.of(x := w, P := Pw)))
      val w0Info = have(Pw(w0)).by(Cut(ex, w0Prop))

      val w0Inℕ = have(w0 ∈ ℕ).by(Tautology.from(w0Info))
      val w0Ne0 = have(w0 =/= 0).by(Tautology.from(w0Info))
      val eq0 = have(0 === n + w0).by(Tautology.from(w0Info))
      val eq = have(n + w0 === 0).by(Congruence.from(eq0))

      val iff0 = have((n + w0 === 0) <=> ((n === 0) /\ (w0 === 0))).by(Tautology.from(NatAlgebra.addEqZeroIff.of(m := n, n := w0), nInℕ, w0Inℕ))
      val both0 = have((n === 0) /\ (w0 === 0)).by(Tautology.from(iff0, eq))
      val w0Eq0 = have(w0 === 0).by(Tautology.from(both0))
      val contra = have(¬(w0 === 0)).by(Restate.from(w0Ne0))
      have(⊥).by(Tautology.from(w0Eq0, contra))
    }
  }

  /** Lemma: if `m <= n` and `m ≠ n` then `m < n` (for naturals). */
  val leAndNeqToLt = Lemma((m ∈ ℕ, n ∈ ℕ, m <= n, m =/= n) |- (m < n)) {
    val mInℕ = assume(m ∈ ℕ)
    val nInℕ = assume(n ∈ ℕ)
    val mn = assume(m <= n)
    val mNeqN = assume(m =/= n)

    val ex = have(∃(w, (w ∈ ℕ) /\ (n === m + w))).by(Tautology.from(leUnfold.of(m := m, n := n), mn))

    have(∃(w, (w ∈ ℕ) /\ (n === m + w)) |- (m < n)) subproof {
      assume(∃(w, (w ∈ ℕ) /\ (n === m + w)))

      have((w ∈ ℕ) /\ (n === m + w) |- (m < n)) subproof {
        val conj = assume((w ∈ ℕ) /\ (n === m + w))
        val wInℕ = have(w ∈ ℕ).by(Tautology.from(conj))
        val nEq = have(n === m + w).by(Tautology.from(conj))

        val notWEq0 = have(¬(w === 0)) subproof {
          val wEq0 = assume(w === 0)
          val nEq2 = have(n === m + 0).by(Congruence.from(nEq, wEq0))
          val add0 = have(m + 0 === m).by(Tautology.from(NatAlgebra.addZeroRight.of(m := m), mInℕ))
          val nEqm = have(n === m).by(Congruence.from(nEq2, add0))
          val mEqn = have(m === n).by(Congruence.from(nEqm))
          val contra = have(¬(m === n)).by(Restate.from(mNeqN))
          have(⊥).by(Tautology.from(mEqn, contra))
        }

        val wNe0 = have(w =/= 0).by(Restate.from(notWEq0))
        have(thesis).by(Tautology.from(ltIntro.of(m := m, n := n, a := w), mInℕ, nInℕ, wInℕ, wNe0, nEq))
      }
      thenHave(thesis).by(LeftExists)
    }

    have(thesis).by(Cut(ex, lastStep))
  }

  /** Lemma: strict order is asymmetric on naturals. */
  val ltAsym = Lemma((m ∈ ℕ, n ∈ ℕ, m < n) |- ¬(n < m)) {
    val mInℕ = assume(m ∈ ℕ)
    val nInℕ = assume(n ∈ ℕ)
    val mn = assume(m < n)

    have(¬(n < m)) subproof {
      val hyp = assume(n < m)
      val mm = have(m < m).by(Tautology.from(ltTrans.of(m := m, n := n, k := m), mInℕ, nInℕ, mInℕ, mn, hyp))
      val irr = have(¬(m < m)).by(Tautology.from(ltIrrefl.of(n := m), mInℕ))
      have(⊥).by(Tautology.from(mm, irr))
    }
  }

  /** Theorem: if `m ∈ ℕ` and `m < n` then `m <= n` and `m =/= n`. */
  val ltImplLeAndNeq = Theorem((m ∈ ℕ, n ∈ ℕ, m < n) |- ((m <= n) /\ (m =/= n))) {
    val mInℕ = assume(m ∈ ℕ)
    val nInℕ = assume(n ∈ ℕ)
    val mn = assume(m < n)
    val le = have(m <= n).by(Tautology.from(ltToLe.of(m := m, n := n), mInℕ, nInℕ, mn))
    val neq = have(m =/= n).by(Tautology.from(ltNeq.of(m := m, n := n), mInℕ, nInℕ, mn))
    have(thesis).by(Tautology.from(le, neq))
  }

  /** Theorem: `m <= n ⟹ (m < n) ∨ (m = n)` (for naturals). */
  val leToLtOrEq = Theorem((m ∈ ℕ, n ∈ ℕ, m <= n) |- ((m < n) \/ (m === n))) {
    val mInℕ = assume(m ∈ ℕ)
    val nInℕ = assume(n ∈ ℕ)
    val mLeN = assume(m <= n)

    val em = have((m === n) \/ (m =/= n)).by(Tautology)
    val caseEq = have(m === n |- (m < n) \/ (m === n)).by(Tautology)

    val caseNe = have(m =/= n |- (m < n) \/ (m === n)) subproof {
      val mNeN = assume(m =/= n)
      val lt = have(m < n).by(Tautology.from(leAndNeqToLt.of(m := m, n := n), mInℕ, nInℕ, mLeN, mNeN))
      have(thesis).by(Tautology.from(lt))
    }

    have(thesis).by(Tautology.from(em, caseEq, caseNe))
  }

  /** Theorem: characterisation of strict order via `<=` and `≠` (for naturals). */
  val ltIffLeAndNe = Theorem((m ∈ ℕ, n ∈ ℕ) |- ((m < n) <=> ((m <= n) /\ (m =/= n)))) {
    val mInℕ = assume(m ∈ ℕ)
    val nInℕ = assume(n ∈ ℕ)

    val dir1 = have((m < n) ==> ((m <= n) /\ (m =/= n))) subproof {
      val mn = assume(m < n)
      have(thesis).by(Tautology.from(ltImplLeAndNeq.of(m := m, n := n), mInℕ, nInℕ, mn))
    }

    val dir2 = have(((m <= n) /\ (m =/= n)) ==> (m < n)) subproof {
      val conj = assume((m <= n) /\ (m =/= n))
      val mLeN = have(m <= n).by(Tautology.from(conj))
      val mNeN = have(m =/= n).by(Tautology.from(conj))
      have(thesis).by(Tautology.from(leAndNeqToLt.of(m := m, n := n), mInℕ, nInℕ, mLeN, mNeN))
    }

    have(thesis).by(Tautology.from(dir1, dir2))
  }
}
