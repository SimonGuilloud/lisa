package lisa.settheory

import lisa.utils.K
import lisa.fol.FOL.{*, given}

/**
 * Axioms for the Tarski-Grothendieck theory (TG)
 */
private[settheory] trait SetTheoryTGAxioms extends SetTheoryZFAxioms {
  private val x = variable
  private val y = variable
  private val z = variable

  final val tarskiAxiom: AXIOM = Axiom(
    forall(
      x,
      in(x, universe(x)) /\
        forall(
          y,
          in(y, universe(x)) ==> (in(powerSet(y), universe(x)) /\ subset(powerSet(y), universe(x))) /\
            forall(z, subset(z, universe(x)) ==> (sim(y, universe(x)) /\ in(y, universe(x))))
        )
    )
  , "tarskiAxiom")

  override def axioms: Set[(String, AXIOM)] = super.axioms + (("TarskiAxiom", tarskiAxiom))

}
