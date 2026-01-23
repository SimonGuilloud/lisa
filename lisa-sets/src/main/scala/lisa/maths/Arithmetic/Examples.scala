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

  /** Example 1: `0 ∈ ℕ`. */
  val ex1_zeroInℕ = Theorem(0 ∈ ℕ) {
    have(thesis) by Restate.from(Nat.zeroInℕ)
  }

  /** Example 2: `S(0) ∈ ℕ`. */
  val ex2_oneInℕ = Theorem(S(0) ∈ ℕ) {
    have(∀(a, (a ∈ ℕ) ==> (S(a) ∈ ℕ))).by(Restate.from(Nat.succClosed))
    thenHave((Nat.zero ∈ ℕ) ==> (S(Nat.zero) ∈ ℕ)) by InstantiateForall(Nat.zero)
    thenHave(thesis) by Tautology.fromLastStep(Nat.zeroInℕ)
  }

  /** Example 3: `S(S(0)) ∈ ℕ`. */
  val ex3_twoInℕ = Theorem(S(S(0)) ∈ ℕ) {
    have(∀(a, (a ∈ ℕ) ==> (S(a) ∈ ℕ))).by(Restate.from(Nat.succClosed))
    thenHave((S(Nat.zero) ∈ ℕ) ==> (S(S(Nat.zero)) ∈ ℕ)) by InstantiateForall(S(Nat.zero))
    thenHave(thesis) by Tautology.fromLastStep(ex2_oneInℕ)
  }

  /** Example 4: successor closure as a theorem. */
  val ex4_succClosed = Theorem(∀(a, (a ∈ ℕ) ==> (S(a) ∈ ℕ))) {
    have(thesis) by Restate.from(Nat.succClosed)
  }

  /** Example 5: `a + 0 = a`. */
  val ex5_addZero = Theorem(∀(a, a + 0 === a)) {
    have(thesis) by Restate.from(Nat.addZero)
  }

  /** Example 6: `a + S(b) = S(a + b)`. */
  val ex6_addSucc = Theorem(∀(a, ∀(b, (b ∈ ℕ) ==> (a + S(b) === S(a + b))))) {
    have(thesis) by Restate.from(Nat.addSucc)
  }

  /** Example 7: `a * 0 = 0`. */
  val ex7_mulZero = Theorem(∀(a, a * 0 === 0)) {
    have(thesis) by Restate.from(Nat.mulZero)
  }

  /** Example 8: `a * S(b) = a*b + a`. */
  val ex8_mulSucc = Theorem(∀(a, ∀(b, (b ∈ ℕ) ==> (a * S(b) === (a * b) + a)))) {
    have(thesis) by Restate.from(Nat.mulSucc)
  }

  /** Example 9: closure of addition on `ℕ`. */
  val ex9_addClosed = Theorem(∀(a, ∀(b, (a ∈ ℕ /\ b ∈ ℕ) ==> ((a + b) ∈ ℕ)))) {
    have(thesis) by Restate.from(Nat.addClosed)
  }

  /** Example 10: closure of multiplication on `ℕ`. */
  val ex10_mulClosed = Theorem(∀(a, ∀(b, (a ∈ ℕ /\ b ∈ ℕ) ==> ((a * b) ∈ ℕ)))) {
    have(thesis) by Restate.from(Nat.mulClosed)
  }

}
