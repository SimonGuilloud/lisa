package lisa

import lisa.SetTheoryLibrary
import lisa.utils.prooflib.BasicMain
import lisa.utils.prooflib.OutputManager
import lisa.utils.fol.FOL.{*, given}
import SetTheoryLibrary.{given, _}

/**
 * The parent trait of all theory files containing mathematical development
 */
trait _HOL extends BasicMain {
  export lisa.hol.VarsAndFunctions.{𝔹, Zero, One, typedvar, computeType, eqOne, computeContextOfFormulas, computeContext, fun}
  export lisa.maths.SetTheory.Types.TypingHelpers.{->:, `*`, @@, ::, is}
  export lisa.maths.SetTheory.Types.Tactics.Typecheck.*
  val library = SetTheoryLibrary
  val F: lisa.utils.fol.FOL.type = lisa.utils.fol.FOL



  //def assume(using proof: library.Proof)(t: Expr[Ind]): proof.ProofStep =
  //  library.assume(eqOne(t))


  def withCTX(s:F.Sequent): F.Sequent =
    val ctx = computeContextOfFormulas(s.left ++ s.right).toSet
    s ++<< (ctx |- ())


  def Theorem(using om: OutputManager, name: sourcecode.FullName, line: sourcecode.Line, file: sourcecode.File)(statement: F.Sequent)(computeProof: Proof ?=> Unit): THM = 
    val ctx = computeContext(statement.freeTermVars.toSet)
    SetTheoryLibrary.Theorem(statement ++<< (ctx |- ()))(computeProof)

}


trait HOL extends _HOL {
  //export lisa.hol.HOLSteps.*
  export lisa.utils.prooflib.BasicStepTactic.*
  export lisa.utils.prooflib.SimpleDeducedSteps.*

  export lisa.automation.Tautology
  export lisa.automation.Substitution
  export lisa.automation.Tableau



}
