package lisa.maths.Arithmetic

import lisa.maths.Arithmetic.Predef.{*, given}
import lisa.maths.Arithmetic.Syntax.{*, given}
import lisa.maths.Arithmetic.NatOrder.*
import lisa.maths.Quantifiers

/**
 * Extra order lemmas for naturals using the arithmetic-witness definitions of `<=` and `<`.
 *
 * Isabelle/HOL reference (non-exhaustive): `Nat.thy` (ordering + arithmetic interaction).
 */
object NatOrderExtra extends lisa.Main {

  private val m = variable[Ind]
  private val n = variable[Ind]
  private val k = variable[Ind]

  ///////////////////////////
  // Small convenience facts
  ///////////////////////////

  /** Lemma: `n∈ℕ ⟹ 0 < Succ(n)`. */
  val zeroLtSucc = Theorem(n ∈ ℕ |- (0 < Succ(n))) {
    val nInℕ = assume(n ∈ ℕ)

    val SnInℕ = have(Succ(n) ∈ ℕ).by(Cut(nInℕ, Nat.succClosed.of(n := n)))
    val SnNe0 = have(Succ(n) =/= 0).by(Tautology.from(Nat.succNeZero.of(n := n), nInℕ))
    val eq0 = have(Succ(n) === 0 + Succ(n)).by(Congruence.from(NatAlgebra.addZeroLeft.of(n := Succ(n)), SnInℕ))

    val w = variable[Ind]
    val ltDef = have((0 < Succ(n)) <=> ∃(w, (w ∈ ℕ) /\ (w =/= 0) /\ (Succ(n) === 0 + w))).by(Restate.from(Nat.lt.definition.of(m := 0, n := Succ(n))))
    val rhs = have((Succ(n) ∈ ℕ) /\ (Succ(n) =/= 0) /\ (Succ(n) === 0 + Succ(n))).by(Tautology.from(SnInℕ, SnNe0, eq0))
    val ex = have(∃(w, (w ∈ ℕ) /\ (w =/= 0) /\ (Succ(n) === 0 + w))).by(RightExists(rhs))
    have(thesis).by(Tautology.from(ltDef, ex))
  }
}
