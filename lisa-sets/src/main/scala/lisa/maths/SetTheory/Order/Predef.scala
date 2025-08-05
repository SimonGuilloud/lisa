package lisa.maths.SetTheory.Order

/**
 * Base exports for the `Order` package.
 */
object Predef {
  export lisa.maths.SetTheory.Order.Definitions.{partialOrder, strictPartialOrder, totalOrder, strictTotalOrder, maximal, minimal, upperBound, lowerBound, greatest, least}
  export lisa.maths.SetTheory.Order.OrderIsomorphism.{isomorphism as orderIsomorphism, isomorphic as orderIsomorphic, ≈}
}
