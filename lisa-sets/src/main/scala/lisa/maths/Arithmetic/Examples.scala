package lisa.maths.Arithmetic

import lisa.maths.Arithmetic.Predef.{*, given}
import lisa.maths.Arithmetic.Syntax.{*, given}

/**
 * Examples: small arithmetic theorems using only the exported API.
 *
 * Policy: no `sorry` in this file.
 */
object Examples extends lisa.Main {

  private val a = variable[Ind]
  private val b = variable[Ind]
  private val m = variable[Ind]
  private val n = variable[Ind]

  /** Example 1: `0 ∈ ℕ`. */
  val ex1_zeroInℕ = Theorem(0 ∈ ℕ) {
    have(thesis) by Restate.from(Nat.zeroInℕ)
  }

  /** Example 2: `S(0) ∈ ℕ`. */
  val ex2_oneInℕ = Theorem(Succ(0) ∈ ℕ) {
    have(thesis) by Cut(Nat.zeroInℕ, Nat.succClosed.of(n := Nat.zero))
  }

  /** Example 3: `S(S(0)) ∈ ℕ`. */
  val ex3_twoInℕ = Theorem(Succ(Succ(0)) ∈ ℕ) {
    have(thesis) by Restate.from(Nat.twoInℕ)
  }

  /** Example 4: successor closure as a theorem. */
  val ex4_succClosed = Theorem(a ∈ ℕ |- (Succ(a) ∈ ℕ)) {
    have(thesis) by Restate.from(Nat.succClosed.of(n := a))
  }

  /** Example 5: `a + 0 = a`. */
  val ex5_addZero = Theorem(a + 0 === a) {
    have(thesis) by Restate.from(Nat.addZero.of(m := a))
  }

  /** Example 6: `a + S(b) = S(a + b)`. */
  val ex6_addSucc = Theorem(b ∈ ℕ |- (a + Succ(b) === Succ(a + b))) {
    val bInℕ = assume(b ∈ ℕ)
    val res = have(a + Succ(b) === Succ(a + b)).by(Cut(bInℕ, Nat.addSucc.of(m := a, n := b)))
    have(thesis).by(Restate.from(res))
  }

  /** Example 7: `a * 0 = 0`. */
  val ex7_mulZero = Theorem(a * 0 === 0) {
    have(thesis) by Restate.from(Nat.mulZero.of(m := a))
  }

  /** Example 8: `a * S(b) = a*b + a`. */
  val ex8_mulSucc = Theorem(b ∈ ℕ |- (a * Succ(b) === (a * b) + a)) {
    val bInℕ = assume(b ∈ ℕ)
    val res = have(a * Succ(b) === (a * b) + a).by(Cut(bInℕ, Nat.mulSucc.of(m := a, n := b)))
    have(thesis).by(Restate.from(res))
  }

  /** Example 9: closure of addition on `ℕ`. */
  val ex9_addClosed = Theorem((a ∈ ℕ, b ∈ ℕ) |- ((a + b) ∈ ℕ)) {
    have(thesis) by Restate.from(Nat.addClosed.of(m := a, n := b))
  }

  /** Example 10: closure of multiplication on `ℕ`. */
  val ex10_mulClosed = Theorem((a ∈ ℕ, b ∈ ℕ) |- ((a * b) ∈ ℕ)) {
    have(thesis) by Restate.from(Nat.mulClosed.of(m := a, n := b))
  }

}
