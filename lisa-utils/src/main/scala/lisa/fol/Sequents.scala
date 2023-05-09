package lisa.fol

//import lisa.kernel.proof.SequentCalculus.Sequent

import scala.annotation.showAsInfix
import lisa.fol.FOLHelpers.*
import lisa.utils.K
import lisa.prooflib.BasicStepTactic
import lisa.prooflib.Library
import lisa.prooflib.ProofTacticLib.ProofTactic


trait Sequents extends Common with lisa.fol.Lambdas {
  object SequentInstantiationRule extends ProofTactic
  given  ProofTactic = SequentInstantiationRule

  case class Sequent(left:Set[Formula], right:Set[Formula]) extends LisaObject[Sequent] with Absolute{
    def underlying:lisa.kernel.proof.SequentCalculus.Sequent = K.Sequent(left.map(_.underlying), right.map(_.underlying))

    def allSchematicLabels: Set[SchematicLabel[?]] = left.flatMap(_.allSchematicLabels)
    def freeSchematicLabels: Set[SchematicLabel[?]] = left.flatMap(_.freeSchematicLabels)
    def substituteUnsafe(map: Map[SchematicLabel[?], ? <: LisaObject[?]]): Sequent = Sequent(left.map(_.substituteUnsafe(map)), right.map(_.substituteUnsafe(map)))


    
    
    /*Ok for now but what when we have more*/
    def substituteWithProof(using lib: Library, proof: lib.Proof)(map: Map[SchematicLabel[_], _ <: LisaObject[_]])(premise: proof.Fact): (Sequent, proof.ProofTacticJudgement) = {

      val mTerm: Map[SchematicFunctionalLabel[?]|Variable, LambdaExpression[Term, Term, ?]] = 
        map.collect(p => p._1 match {
              case sl: Variable => (sl, LambdaExpression[Term, Term, 0](Seq(), p._2.asInstanceOf[Term], 0))
              case sl: SchematicFunctionalLabel[?] => 
                p._2 match {
                  case l : LambdaExpression[Term, Term, ?] @unchecked if 
                    (l.bounds.isEmpty || l.bounds.head.isInstanceOf[Variable]) & l.body.isInstanceOf[Term] => 
                      (p._1.asInstanceOf, l)
                  case s : FunctionalLabel[?] => 
                    val vars = nFreshId(Seq(s.id), s.arity).map(Variable.apply)
                    (sl, LambdaExpression(vars, s(vars), s.arity))
                }
            })
      val mPred: Map[SchematicPredicateLabel[?]|VariableFormula, LambdaExpression[Term, Formula, ?]] = 
        map.collect(p => p._1 match {
              case sl: VariableFormula =>             (sl, LambdaExpression[Term, Formula, 0](Seq(), p._2.asInstanceOf[Formula], 0))
              case sl: SchematicPredicateLabel[?] => 
                p._2 match {
                  case l : LambdaExpression[Term, Formula, ?] @unchecked  if 
                    (l.bounds.isEmpty || l.bounds.head.isInstanceOf[Variable]) & l.body.isInstanceOf[Formula]=> (sl, l)
                  case s : PredicateLabel[?] => 
                    val vars = nFreshId(Seq(s.id), s.arity).map(Variable.apply)
                    (sl, LambdaExpression(vars, s(vars), s.arity))
                }
            })
      val mConn = map.collect(p => p._1 match {
              case sl: SchematicConnectorLabel[?] =>  
                p._2 match {
                  case l : LambdaExpression[Formula, Formula, ?] @unchecked if 
                    (l.bounds.isEmpty || l.bounds.head.isInstanceOf[VariableFormula]) & l.body.isInstanceOf[Formula] => (sl, l)
                  case s : ConnectorLabel[?] => 
                    val vars = nFreshId(Seq(s.id), s.arity).map(VariableFormula.apply)
                    (sl, LambdaExpression(vars, s(vars), s.arity))
                }
            })
            (substituteUnsafe(map), substituteWithProofLikeKernel(mConn, mPred, mTerm)(premise))

    }

    def substituteWithProofLikeKernel(using
        lib: Library,
        proof: lib.Proof
    )(mCon: Map[SchematicConnectorLabel[?], LambdaExpression[Formula, Formula, ?]],
      mPred: Map[SchematicPredicateLabel[?]|VariableFormula, LambdaExpression[Term, Formula, ?]],
      mTerm: Map[SchematicFunctionalLabel[?]|Variable, LambdaExpression[Term, Term, ?]])(
      premise: proof.Fact
    ): proof.ProofTacticJudgement = {
      val premiseSequent = proof.getSequent(premise).underlying
      val mConK = mCon.map((sl, le) => (sl.underlyingLabel, underlyingLFF(le)))
      val mPredK = mPred.map((sl, le) => sl match {
        case v: VariableFormula => (v.underlyingLabel, underlyingLTF(le))
        case spl: SchematicPredicateLabel[?] => (spl.underlyingLabel, underlyingLTF(le))
      })
      val mTermK = mTerm.map((sl, le) => sl match {
        case v: Variable => (v.underlyingLabel, underlyingLTT(le))
        case sfl: SchematicFunctionalLabel[?] => (sfl.underlyingLabel, underlyingLTT(le))
      })
      val botK = lisa.utils.KernelHelpers.instantiateSchemaInSequent(premiseSequent, mConK, mPredK, mTermK)
      val smap = Map[SchematicLabel[?], LisaObject[?]]()++mCon++mPred++mTerm
      val res = proof.getSequent(premise).substituteUnsafe(smap.asInstanceOf)
      proof.ValidProofTactic(res, Seq(K.InstSchema(botK, -1, mConK, mPredK, mTermK)), Seq(premise))
    }


    infix def +<<(f: Formula): Sequent = this.copy(left = this.left + f)
    infix def -<<(f: Formula): Sequent = this.copy(left = this.left - f)
    infix def +>>(f: Formula): Sequent = this.copy(right = this.right + f)
    infix def ->>(f: Formula): Sequent = this.copy(right = this.right - f)
    infix def ++<<(s1: Sequent): Sequent = this.copy(left = this.left ++ s1.left)
    infix def --<<(s1: Sequent): Sequent = this.copy(left = this.left -- s1.left)
    infix def ++>>(s1: Sequent): Sequent = this.copy(right = this.right ++ s1.right)
    infix def -->>(s1: Sequent): Sequent = this.copy(right = this.right -- s1.right)
    infix def ++(s1: Sequent): Sequent = this.copy(left = this.left ++ s1.left, right = this.right ++ s1.right)
    infix def --(s1: Sequent): Sequent = this.copy(left = this.left -- s1.left, right = this.right -- s1.right)

    infix def removeLeft(f: Formula): Sequent = this.copy(left = this.left.filterNot(isSame(_, f)))
    infix def removeRight(f: Formula): Sequent = this.copy(right = this.right.filterNot(isSame(_, f)))
    infix def removeAllLeft(s1: Sequent): Sequent = this.copy(left = this.left.filterNot(e1 => s1.left.exists(e2 => isSame(e1, e2))))
    infix def removeAllLeft(s1: Set[Formula]): Sequent = this.copy(left = this.left.filterNot(e1 => s1.exists(e2 => isSame(e1, e2))))
    infix def removeAllRight(s1: Sequent): Sequent = this.copy(right = this.right.filterNot(e1 => s1.right.exists(e2 => isSame(e1, e2))))
    infix def removeAllRight(s1: Set[Formula]): Sequent = this.copy(right = this.right.filterNot(e1 => s1.exists(e2 => isSame(e1, e2))))
    infix def removeAll(s1: Sequent): Sequent = this.copy(left = this.left.filterNot(e1 => s1.left.exists(e2 => isSame(e1, e2))), right = this.right.filterNot(e1 => s1.right.exists(e2 => isSame(e1, e2))))
  
    infix def addLeftIfNotExists(f: Formula): Sequent = if (this.left.exists(isSame(_, f))) this else (this +<< f)
    infix def addRightIfNotExists(f: Formula): Sequent = if (this.right.exists(isSame(_, f))) this else (this +>> f)
    infix def addAllLeftIfNotExists(s1: Sequent): Sequent = this ++<< s1.copy(left = s1.left.filterNot(e1 => this.left.exists(isSame(_, e1))))
    infix def addAllRightIfNotExists(s1: Sequent): Sequent = this ++>> s1.copy(right = s1.right.filterNot(e1 => this.right.exists(isSame(_, e1))))
    infix def addAllIfNotExists(s1: Sequent): Sequent = this ++ s1.copy(left = s1.left.filterNot(e1 => this.left.exists(isSame(_, e1))), right = s1.right.filterNot(e1 => this.right.exists(isSame(_, e1))))

    // OL shorthands
    infix def +<?(f: Formula): Sequent = this addLeftIfNotExists f
    infix def -<?(f: Formula): Sequent = this removeLeft f
    infix def +>?(f: Formula): Sequent = this addRightIfNotExists f
    infix def ->?(f: Formula): Sequent = this removeRight f
    infix def ++<?(s1: Sequent): Sequent = this addAllLeftIfNotExists s1
    infix def --<?(s1: Sequent): Sequent = this removeAllLeft s1
    infix def ++>?(s1: Sequent): Sequent = this addAllRightIfNotExists s1
    infix def -->?(s1: Sequent): Sequent = this removeAllRight s1
    infix def --?(s1: Sequent): Sequent = this removeAll s1
    infix def ++?(s1: Sequent): Sequent = this addAllIfNotExists s1
    
  }

  val emptySeq: Sequent = Sequent(Set.empty, Set.empty)

  given Conversion[Formula, Sequent] = f => Sequent(Set.empty, Set(f))

  def isSame(formula1: Formula, formula2: Formula): Boolean = {
      K.isSame(formula1.underlying, formula2.underlying)
  }

  def isSameSequent(sequent1: Sequent, sequent2: Sequent): Boolean = {
    K.isSameSequent(sequent1.underlying, sequent2.underlying)
  }

  /**
   * returns true if the first argument implies the second by the laws of ortholattices.
   */
  def isImplying(formula1: Formula, formula2: Formula): Boolean = {
    K.isImplying(formula1.underlying, formula2.underlying)
  }
  def isImplyingSequent(sequent1: Sequent, sequent2: Sequent): Boolean = {
    K.isImplyingSequent(sequent1.underlying, sequent2.underlying)
  }

  def isSubset(s1: Set[Formula], s2: Set[Formula]): Boolean = {
    K.isSubset(s1.map(_.underlying), s2.map(_.underlying))
  }
  def isSameSet(s1: Set[Formula], s2: Set[Formula]): Boolean =
    K.isSameSet(s1.map(_.underlying), s2.map(_.underlying))

  def contains(s: Set[Formula], f: Formula): Boolean = {
    K.contains(s.map(_.underlying), f.underlying)
  }

}
