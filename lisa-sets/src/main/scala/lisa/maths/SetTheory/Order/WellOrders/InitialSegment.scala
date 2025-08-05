package lisa.maths.SetTheory.Order
package WellOrders

import lisa.maths.SetTheory.Base.Predef.{*, given}

import WellOrder.*

/**
 * Given a well-ordering `(A, <)`, the set of `<`-predecessors of `x` in `A`
 * is the set
 *
 *   `predecessors(x, A, <) = {y ∈ A | y < x}`.
  *
  * If `(A, <)` is a well-ordering, `predecessors(x, A, <)` is an [[initialSegment]] of `A`.
 */
object InitialSegment extends lisa.Main {

  private val x, y = variable[Ind]
  private val A = variable[Ind]
  private val < = variable[Ind]

  extension (x: set) {

    /**
     * Local notation.
     */
    private infix def <(y: set): Expr[Prop] = (x, y) ∈ InitialSegment.<
  }

  /**
   * Definition --- The initial segment of `(A, <)` determined by `x` is the
   * set of elements `y ∈ A` that are less than `x`.
   */
  val predecessors = DEF(λ(x, λ(A, λ(<, { y ∈ A | y < x }))))

  /**
   * Theorem --- `y ∈ predecessors(x, A, <)` if and only if `y ∈ A` and `y < x`.
   *
   * Follows from [[Comprehension.membership]].
   */
  val membership = Theorem(
    y ∈ predecessors(x)(A)(<) <=> (y ∈ A) /\ (y < x)
  ) {
    have(y ∈ { y ∈ A | y < x } <=> (y ∈ A) /\ (y < x)) by Comprehension.apply
    thenHave(thesis) by Substitute(predecessors.definition)
  }

  /**
    * Theorem --- If `(A, <)` is a well-ordering, then `(predecessors(x, A, <), <)`
    * is also a well-order.
    */
  val ofWellOrdering = Theorem(
    wellOrdering(A)(<) |- wellOrdering(predecessors(x)(A)(<))(<)
  ) {
    sorry
  }
}
