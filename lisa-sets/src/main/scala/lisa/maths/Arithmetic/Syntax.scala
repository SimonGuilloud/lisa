package lisa.maths.Arithmetic

import lisa.maths.Arithmetic.Predef.{*, given}

/**
 * Syntactic helpers for arithmetic.
 */
object Syntax {

  /**
   * Embed a Scala `Int` as a natural number term using `Nat.zero` and `Nat.Succ`.
   *
   * This is intended for small numerals used in proofs/examples.
   */
  def numeral(n: Int): Expr[Ind] =
    if n < 0 then throw new IllegalArgumentException(s"negative numeral: $n")
    else if n == 0 then Nat.zero
    else Nat.Succ(numeral(n - 1))

  given Conversion[Int, Expr[Ind]] = n => numeral(n)

  export Nat.{ℕ, Succ, add, mul, le, lt}

  extension (a: Expr[Ind])
    infix def +(b: Expr[Ind]): Expr[Ind] = Nat.add(a)(b)
    infix def *(b: Expr[Ind]): Expr[Ind] = Nat.mul(a)(b)
    infix def <=(b: Expr[Ind]): Expr[Prop] = Nat.le(a)(b)
    infix def <(b: Expr[Ind]): Expr[Prop] = Nat.lt(a)(b)

}
