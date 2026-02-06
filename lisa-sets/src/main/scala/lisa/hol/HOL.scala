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
  export lisa.hol.VarsAndFunctions.{computeType, eqOne,
                                    eqDefin, tforall, TypedForall, HOLProofType, holeq, HOLSequent, =:=, definition, getContext, typedvar, typevar,
                                    given_Conversion_TypedForall_Expr, given_Conversion_Expr_HOLSequent,
                                    given_Conversion_Expr_Expr, termToSetConv, setTermToSetConv}
  export lisa.hol.HOLHelperTheorems.{𝔹, Zero, One}
  export lisa.maths.SetTheory.Types.Tactics.Typecheck.*
  val library: SetTheoryLibrary.type = SetTheoryLibrary



  //def assume(using proof: library.Proof)(t: Expr[Ind]): proof.ProofStep =
  //  library.assume(eqOne(t))


  def withCTX(s:F.Sequent): F.Sequent =
    s ++<? (getContext(s) |- ())

  // HOLTheorem is now just an alias for regular Theorem since types are managed externally
  def HOLTheorem(using om: OutputManager, name: sourcecode.FullName, line: sourcecode.Line, file: sourcecode.File)(statement: F.Sequent)(computeProof: Proof ?=> Unit): THM = 
    val ctx = getContext(statement)
    SetTheoryLibrary.Theorem(statement ++<< (ctx |- ()))(computeProof)

}


trait HOL extends _HOL {
  //export lisa.hol.HOLSteps.*
  export SetTheoryLibrary.{library => _, have => _, given, _}
  export lisa.utils.prooflib.BasicStepTactic.*
  export lisa.utils.prooflib.SimpleDeducedSteps.*

  export lisa.automation.Tautology
  export lisa.automation.Substitution
  export lisa.automation.Tableau

  def HOLassume(using proof: library.Proof)(t: Expr[Ind]): proof.ProofStep =
    val f = eqOne(t)
    library.assume(f)
    val ctx = getContext(t)
    //ctx.foreach(ta => assume(ta))
    library.have((ctx |- f) +<<  f) by Restate


  def have(using proof: library.Proof)(res: Sequent): HaveSequent = 
    val ctx = getContext(res)
    HaveSequent(res ++<< (ctx |- ()))

  def have(using line: sourcecode.Line, file: sourcecode.File)(using proof: library.Proof)(v: proof.Fact | proof.ProofTacticJudgement) = v match {
    case judg: proof.ProofTacticJudgement => judg.validate(line, file)
    case fact: proof.Fact @unchecked => HaveSequent(proof.sequentOfFact(fact)).by(using proof, line, file)(Weakening(using library, proof)(fact))
  }


}
