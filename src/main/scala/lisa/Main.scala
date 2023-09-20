package lisa

import lisa.settheory.SetTheoryLibrary
import lisa.prooflib.BasicMain

/**
 * The parent trait of all theory files containing mathematical development
 */
trait Main extends BasicMain {
  export SetTheoryLibrary.{powerAxiom as _, subsetAxiom as _, given, _}
  export lisa.prooflib.Exports.*

  /**
   * Power Set Axiom --- For a set `x`, there exists a power set of `x`, denoted
   * `PP(x)` or `power(x)` which contains every subset of x.
   *
   * `() |- z ∈ power(x) ⇔ z ⊆ x`
   *
   * This axiom defines [[powerSet]] as the function symbol representing this
   * set.
   */
  final def powerAxiom: SetTheoryLibrary.powerAxiom.type = SetTheoryLibrary.powerAxiom

  /**
   * Subset Axiom --- For sets `x` and `y`, `x` is a subset of `y` iff every
   * element of `x` is in `y`. Denoted `x ⊆ y`.
   *
   * `() |- x ⊆ y ⇔ (z ∈ x ⇒ z ∈ y)`
   *
   * This axiom defines the [[subset]] symbol as this predicate.
   */
  final def subsetAxiom: SetTheoryLibrary.subsetAxiom.type = SetTheoryLibrary.subsetAxiom

  knownDefs.update(emptySet, Some(emptySetAxiom))
  knownDefs.update(unorderedPair, Some(pairAxiom))
  knownDefs.update(union, Some(unionAxiom))
  knownDefs.update(powerSet, Some(powerAxiom))
  knownDefs.update(subset, Some(subsetAxiom))

  //TODO: Refine errors and messages
  extension (symbol: ConstantLabel[?]) {
    def definition: JUSTIFICATION = {
      getDefinition(symbol).get
      /*
      symbol match {
      //case `equality` => throw new NoSuchElementException("Equality has no definition")
      /*case `top` => throw new NoSuchElementException("Top has no definition")
      case `bot` => throw new NoSuchElementException("Bot has no definition")
      case `in` => throw new NoSuchElementException("Membership has no definition")*/
      case _ => ???.asInstanceOf[JUSTIFICATION] //getDefinition(symbol).get*/
    }
  }

}
