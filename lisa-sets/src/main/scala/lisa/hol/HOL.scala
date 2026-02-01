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

  
  val F: lisa.utils.fol.FOL.type = lisa.utils.fol.FOL
  export F.{=== as _, ≠ as _, *, given}
  export lisa.maths.SetTheory.Functions.Predef.{*}
  export lisa.maths.SetTheory.Types.TypingHelpers.{main => _, *, given}
  export lisa.hol.VarsAndFunctions.{𝔹, Zero, One, typedvar, computeType, eqOne, computeContextOfFormulas, computeContext, fun,
                                    eqDefin, tforall, TypedForall, HOLProofType, holeq, HOLSequent, =:=, definition, 
                                    given_Conversion_TypedForall_Expr, given_Conversion_Expr_HOLSequent,
                                    given_Conversion_Expr_Expr, termToSetConv, setTermToSetConv}
  export lisa.maths.SetTheory.Types.Tactics.Typecheck.*
  val library = SetTheoryLibrary



  //def assume(using proof: library.Proof)(t: Expr[Ind]): proof.ProofStep =
  //  library.assume(eqOne(t))


  def withCTX(s:F.Sequent): F.Sequent =
    val ctx = computeContextOfFormulas(s.left ++ s.right).toSet
    s ++<< (ctx |- ())


  def HOLTheorem(using om: OutputManager, name: sourcecode.FullName, line: sourcecode.Line, file: sourcecode.File)(statement: F.Sequent)(computeProof: Proof ?=> Unit): THM = 
    val ctx = computeContext(statement.freeTermVars.toSet)
    SetTheoryLibrary.Theorem(statement ++<< (ctx |- ()))(computeProof)

}


trait HOL extends _HOL {
  //export lisa.hol.HOLSteps.*
  export SetTheoryLibrary.{library => _, given, _}
  export lisa.utils.prooflib.BasicStepTactic.*
  export lisa.utils.prooflib.SimpleDeducedSteps.*

  export lisa.automation.Tautology
  export lisa.automation.Substitution
  export lisa.automation.Tableau



}
