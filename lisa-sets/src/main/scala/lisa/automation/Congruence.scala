package lisa.automation
import lisa.fol.FOL.{*, given}
import lisa.prooflib.BasicStepTactic.*
import lisa.prooflib.ProofTacticLib.*
import lisa.prooflib.SimpleDeducedSteps.*
import lisa.prooflib.*
import lisa.utils.parsing.UnreachableException
import leo.datastructures.TPTP.CNF.AtomicFormula

/**
  * This tactic tries to prove a sequent by congruence.
  * Consider the congruence closure of all terms and formulas in the sequent, with respect to all === and <=> left of the sequent.
  * The sequent is provable by congruence if one of the following conditions is met:
  *    - The right side contains an equality s === t or equivalence a <=> b provable in the congruence closure.
  *    - The left side contains an negated equality !(s === t) or equivalence !(a <=> b) provable in the congruence closure.
  *    - There is a formula a on the left and b on the right such that a and b are congruent.
  *    - There are two formulas a and !b on the left such that a and b are congruent.
  *    - There are two formulas a and !b on the right such that a and b are congruent.
  *    - The sequent is Ol-valid without equality reasoning
  * Note that complete congruence closure modulo OL is an open problem.
  * 
  * The tactic uses an egraph datastructure to compute the congruence closure.
  * The egraph itselfs relies on two underlying union-find datastructure, one for terms and one for formulas.
  * The union-finds are equiped with an `explain` method that produces a path between any two elements in the same equivalence class.
  * Each edge of the path can come from an external equality, or be the consequence of congruence.
  * The tactic uses uses this path to produce needed proofs.
  * 
  */
object Congruence  extends ProofTactic with ProofSequentTactic {
    def apply(using lib: Library, proof: lib.Proof)(bot: Sequent): proof.ProofTacticJudgement = TacticSubproof {
      import lib.*

      val egraph = new EGraphTerms()
      egraph.addAll(bot.left)
      egraph.addAll(bot.right)

      bot.left.foreach{
        case (left === right) => egraph.merge(left, right)
        case (left <=> right) => egraph.merge(left, right)
        case _ => ()
      }

      if isSameSequent(bot, ⊤) then
        have(bot) by Restate
      else if bot.left.exists { lf =>
        bot.right.exists { rf =>
          if egraph.idEq(lf, rf) then
            val base = have(bot.left |- (bot.right + lf) ) by Restate
            val eq = have(egraph.proveFormula(lf, rf, bot))
            val a = formulaVariable
            have((bot.left + (lf <=> rf)) |- (bot.right) ) by RightSubstIff.withParametersSimple(List((lf, rf)), lambda(a, a))(base)
            have(bot) by Cut(eq, lastStep)
            true
          else false
        } ||
        bot.left.exists{ 
          case rf2 @ Neg(rf) if egraph.idEq(lf, rf)=>
            val base = have((bot.left + !lf) |- bot.right ) by Restate
            val eq = have(egraph.proveFormula(lf, rf, bot))
            val a = formulaVariable
            have((bot.left + (lf <=> rf)) |- (bot.right) ) by LeftSubstIff.withParametersSimple(List((lf, rf)), lambda(a, !a))(base)
            have(bot) by Cut(eq, lastStep)
            true
          case _  => false
        } || {
        lf match
          case !(a === b) if egraph.idEq(a, b) => 
            have(egraph.proveTerm(a, b, bot))
            true
          case !(a <=> b) if egraph.idEq(a, b) => 
            have(egraph.proveFormula(a, b, bot))
            true
          case _ => false
        }

      } then ()
      else if bot.right.exists { rf =>
        bot.right.exists{ 
          case lf2 @ Neg(lf) if egraph.idEq(lf, rf)=>
            val base = have((bot.left) |- (bot.right + !rf) ) by Restate
            val eq = have(egraph.proveFormula(lf, rf, bot))
            val a = formulaVariable
            have((bot.left + (lf <=> rf)) |- (bot.right) ) by RightSubstIff.withParametersSimple(List((lf, rf)), lambda(a, !a))(base)
            have(bot) by Cut(eq, lastStep)
            true
          case _  => false
        } || {
        rf match
          case (a === b) if egraph.idEq(a, b) => 
            have(egraph.proveTerm(a, b, bot))
            true
          case (a <=> b) if egraph.idEq(a, b) =>
            have(egraph.proveFormula(a, b, bot))
            true
          case _ => false
        }
      } then ()
      else
        return proof.InvalidProofTactic(s"No congruence found to show sequent\n $bot")
    }

  
}


class UnionFind[T]  {
  // parent of each element, leading to its root. Uses path compression
  val parent = scala.collection.mutable.Map[T, T]()
  // original parent of each element, leading to its root. Does not use path compression. Used for explain.
  val realParent = scala.collection.mutable.Map[T, (T, ((T, T), Boolean, Int))]()
  //keep track of the rank (i.e. number of elements bellow it) of each element. Necessary to optimize union.
  val rank = scala.collection.mutable.Map[T, Int]()
  //tracks order of ancientness of unions.
  var unionCounter = 0

  /**
    * add a new element to the union-find.
    */
  def add(x: T): Unit = {
    parent(x) = x
    realParent(x) = (x, ((x, x), true, 0))
    rank(x) = 0
  }

  /**
    *
    * @param x the element whose parent we want to find
    * @return the root of x
    */
  def find(x: T): T = {
    if parent(x) == x then
      x
    else
      var root = x
      while parent(root) != root do
        root = parent(root)
      var y = x
      while parent(y) != root do
        parent(y) = root
        y = parent(y)
      root
  }

  /**
    * Merges the classes of x and y
    */
  def union(x: T, y: T): Unit = {
    unionCounter += 1
    val xRoot = find(x)
    val yRoot = find(y)
    if (xRoot == yRoot) return
    if (rank(xRoot) < rank(yRoot)) {
      parent(xRoot) = yRoot
      realParent(xRoot) = (yRoot, ((x, y), true, unionCounter))
    } else if (rank(xRoot) > rank(yRoot)) {
      parent(yRoot) = xRoot
      realParent(yRoot) = (xRoot, ((x, y), false, unionCounter))
    } else {
      parent(yRoot) = xRoot
      realParent(yRoot) = (xRoot, ((x, y), false, unionCounter))
      rank(xRoot) = rank(xRoot) + 1
    }
  }

  private def getPathToRoot(x: T): List[T] = {
    if x == find(x) then
      List(x)
    else
      val next = realParent(x)
      x :: getPathToRoot(next._1)

  }

  private def getExplanationFromTo(x:T, c: T): List[(T, ((T, T), Boolean, Int))] = {
    if x == c then
      List()
    else
      val next = realParent(x)
      next :: getExplanationFromTo(next._1, c)}

  private def lowestCommonAncestor(x: T, y: T): Option[T] = {
    val pathX = getPathToRoot(x)
    val pathY = getPathToRoot(y)
    pathX.find(pathY.contains)
  }

  /**
    * Returns a path from x to y made of pairs of elements (u, v)
    * such that union(u, v) was called.
    */
  def explain(x:T, y:T): Option[List[(T, T)]]= {

    if (x == y) then return Some(List())
    val lca = lowestCommonAncestor(x, y)
    lca match
      case None => None
      case Some(lca) =>
        var max :((T, T), Boolean, Int) = ((x, x), true, 0)
        var itX = x
        while itX != lca do
          val (next, ((u1, u2), b, c)) = realParent(itX)
          if c > max._3 then
            max = ((u1, u2), b, c)
          itX = next

        var itY = y
        while itY != lca do
          val (next, ((u1, u2), b, c)) = realParent(itY)
          if c > max._3 then
            max = ((u1, u2), !b, c)
          itY = next

        val u1 = max._1._1
        val u2 = max._1._2
        if max._2 then
          Some(explain(x, u1).get ++ List((u1, u2)) ++ explain(u2, y).get)
        else
          Some(explain(x, u2).get ++ List((u1, u2)) ++ explain(u1, y).get)
  }


  /**
    * Returns the set of all roots of all classes
    */
  def getClasses: Set[T] = parent.keys.map(find).toSet

  /**
    * Add all elements in the collection to the union-find
    */
  def addAll(xs: Iterable[T]): Unit = xs.foreach(add)

}


///////////////////////////////
///////// E-graph /////////////
///////////////////////////////

import scala.collection.mutable

class EGraphTerms() {

  type ENode = Term | Formula



  val termMap = mutable.Map[Term, Set[Term]]()
  val termParents = mutable.Map[Term, mutable.Set[AppliedFunctional | AppliedPredicate]]()
  var termWorklist = List[Term]()
  val termUF = new UnionFind[Term]()




  val formulaMap = mutable.Map[Formula, Set[Formula]]()
  val formulaParents = mutable.Map[Formula, mutable.Set[AppliedConnector]]()
  var formulaWorklist = List[Formula]()
  val formulaUF = new UnionFind[Formula]()




  trait TermStep
  case class TermExternal(between: (Term, Term)) extends TermStep
  case class TermCongruence(between: (Term, Term)) extends TermStep

  trait FormulaStep
  case class FormulaExternal(between: (Formula, Formula)) extends FormulaStep
  case class FormulaCongruence(between: (Formula, Formula)) extends FormulaStep

  val termProofMap = mutable.Map[(Term, Term), TermStep]()
  val formulaProofMap = mutable.Map[(Formula, Formula), FormulaStep]()

  def explain(id1: Term, id2: Term): Option[List[TermStep]] = {
    val steps = termUF.explain(id1, id2)
    steps.map(_.foldLeft((id1, List[TermStep]())) {
      case ((prev, acc), step) =>
      termProofMap(step) match
        case s @ TermExternal((l, r)) => 
          if l == prev then
            (r, s :: acc)
          else if r == prev then
            (l, TermExternal(r, l) :: acc)
          else throw new Exception("Invalid proof recovered: It is not a chain")
        case s @ TermCongruence((l, r)) => 
          if l == prev then
            (r, s :: acc)
          else if r == prev then
            (l, TermCongruence(r, l) :: acc)
          else throw new Exception("Invalid proof recovered: It is not a chain")

    }._2.reverse)
  }

  def explain(id1: Formula, id2: Formula): Option[List[FormulaStep]] = {
    val steps = formulaUF.explain(id1, id2)
    steps.map(_.foldLeft((id1, List[FormulaStep]())) {
      case ((prev, acc), step) =>
      formulaProofMap(step) match
        case s @ FormulaExternal((l, r)) => 
          if l == prev then
            (r, s :: acc)
          else if r == prev then
            (l, FormulaExternal(r, l) :: acc)
          else throw new Exception("Invalid proof recovered: It is not a chain")
        case s @ FormulaCongruence((l, r)) => 
          if l == prev then
            (r, s :: acc)
          else if r == prev then
            (l, FormulaCongruence(r, l) :: acc)
          else throw new Exception("Invalid proof recovered: It is not a chain")

    }._2.reverse)
  }


  def makeSingletonEClass(node:Term): Term = {
    termUF.add(node)
    termMap(node) = Set(node)
    termParents(node) = mutable.Set()
    node
  }
  def makeSingletonEClass(node:Formula): Formula = {
    formulaUF.add(node)
    formulaMap(node) = Set(node)
    formulaParents(node) = mutable.Set()
    node
  }

  def classOf(id: Term): Set[Term] = termMap(id)
  def classOf(id: Formula): Set[Formula] = formulaMap(id)

  def idEq(id1: Term, id2: Term): Boolean = termUF.find(id1) == termUF.find(id2)
  def idEq(id1: Formula, id2: Formula): Boolean = formulaUF.find(id1) == formulaUF.find(id2)

  def canonicalize(node: Term): Term = node match
    case AppliedFunctional(label, args) => 
      AppliedFunctional(label, args.map(termUF.find.asInstanceOf))
    case _ => node
  
    
  def canonicalize(node: Formula): Formula = {
    node match
      case AppliedPredicate(label, args) => AppliedPredicate(label, args.map(termUF.find))
      case AppliedConnector(label, args) => AppliedConnector(label, args.map(formulaUF.find))
      case node => node
  }

  def add(node: Term): Term =
    if termMap.contains(node) then return node
    makeSingletonEClass(node)
    node match
      case node @ AppliedFunctional(_, args) => 
        args.foreach(child => 
          add(child)
          termParents(child).add(node)
        )
        node
      case _ => node
  
  def add(node: Formula): Formula =
    if formulaMap.contains(node) then return node
    makeSingletonEClass(node)
    node match
      case node @ AppliedPredicate(_, args) => 
        args.foreach(child => 
          add(child)
          termParents(child).add(node)
        )
        node
      case node @ AppliedConnector(_, args) =>
        args.foreach(child => 
          add(child)
          formulaParents(child).add(node)
        )
        node
      case _ => node

  def addAll(nodes: Iterable[Term|Formula]): Unit = 
    nodes.foreach{
      case node: Term => add(node)
      case node: Formula => add(node)
    }
    
    


  def merge(id1: Term, id2: Term): Unit = {
    mergeWithStep(id1, id2, TermExternal((id1, id2)))
  }
  def merge(id1: Formula, id2: Formula): Unit = {
    mergeWithStep(id1, id2, FormulaExternal((id1, id2)))
  }

  protected def mergeWithStep(id1: Term, id2: Term, step: TermStep): Unit = {
    if termUF.find(id1) == termUF.find(id2) then ()
    else
      termProofMap((id1, id2)) = step
      val newSet = termMap(termUF.find(id1)) ++ termMap(termUF.find(id2))
      val newparents = termParents(termUF.find(id1)) ++ termParents(termUF.find(id2))
      termUF.union(id1, id2)
      val newId1 = termUF.find(id1)
      val newId2 = termUF.find(id2)
      termMap(newId1) = newSet
      termMap(newId2) = newSet
      termParents(newId1) = newparents
      termParents(newId2) = newparents
    
      val id = termUF.find(id2)
      termWorklist = id :: termWorklist
      val cause = (id1, id2)
      val termSeen = mutable.Map[Term, AppliedFunctional]()
      val formulaSeen = mutable.Map[Formula, AppliedPredicate]()
      newparents.foreach { 
        case pTerm: AppliedFunctional =>
          val canonicalPTerm = canonicalize(pTerm) 
          if termSeen.contains(canonicalPTerm) then 
            val qTerm = termSeen(canonicalPTerm)
            Some((pTerm, qTerm, cause))
            mergeWithStep(pTerm, qTerm, TermCongruence((pTerm, qTerm)))
          else
            termSeen(canonicalPTerm) = pTerm
        case pFormula: AppliedPredicate =>
          val canonicalPFormula = canonicalize(pFormula) 
          if formulaSeen.contains(canonicalPFormula) then 
            val qFormula = formulaSeen(canonicalPFormula)

            Some((pFormula, qFormula, cause))
            mergeWithStep(pFormula, qFormula, FormulaCongruence((pFormula, qFormula)))
          else
            formulaSeen(canonicalPFormula) = pFormula
      }
      termParents(id) = (termSeen.values.to(mutable.Set): mutable.Set[AppliedFunctional | AppliedPredicate])  ++ formulaSeen.values.to(mutable.Set)
  }

  protected def mergeWithStep(id1: Formula, id2: Formula, step: FormulaStep): Unit = 
    if formulaUF.find(id1) == formulaUF.find(id2) then ()
    else
      formulaProofMap((id1, id2)) = step
      val newSet = formulaMap(formulaUF.find(id1)) ++ formulaMap(formulaUF.find(id2))
      val newparents = formulaParents(formulaUF.find(id1)) ++ formulaParents(formulaUF.find(id2))
      formulaUF.union(id1, id2)
      val newId1 = formulaUF.find(id1)
      val newId2 = formulaUF.find(id2)
      formulaMap(newId1) = newSet
      formulaMap(newId2) = newSet
      formulaParents(newId1) = newparents
      formulaParents(newId2) = newparents
      val id = formulaUF.find(id2)
      formulaWorklist = id :: formulaWorklist
      val cause = (id1, id2)
      val formulaSeen = mutable.Map[Formula, AppliedConnector]()
      newparents.foreach { 
        case pFormula: AppliedConnector =>
          val canonicalPFormula = canonicalize(pFormula) 
          if formulaSeen.contains(canonicalPFormula) then 
            val qFormula = formulaSeen(canonicalPFormula)
            Some((pFormula, qFormula, cause))
            mergeWithStep(pFormula, qFormula, FormulaCongruence((pFormula, qFormula)))
          else
            formulaSeen(canonicalPFormula) = pFormula
      }
      formulaParents(id) = formulaSeen.values.to(mutable.Set)


  def proveTerm(using lib: Library, proof: lib.Proof)(id1: Term, id2:Term, base: Sequent): proof.ProofTacticJudgement = 
    TacticSubproof { proveInnerTerm(id1, id2, base) }

  def proveInnerTerm(using lib: Library, proof: lib.Proof)(id1: Term, id2:Term, base: Sequent): Unit = {
    import lib.*
    val steps = explain(id1, id2)
    steps match {
      case None => throw new Exception("No proof found in the egraph")
      case Some(steps) => 
        if steps.isEmpty then have(base.left |- (base.right + (id1 === id2))) by Restate
        steps.foreach {
          case TermExternal((l, r)) => 
            val goalSequent = base.left |- (base.right + (id1 === r))
            if l == id1 then 
              have(goalSequent) by Restate
            else
              val x = freshVariable(id1)
              have(goalSequent) by RightSubstEq.withParametersSimple(List((l, r)), lambda(x, id1 === x))(lastStep)
          case TermCongruence((l, r)) => 
            val prev = if id1 != l then lastStep else null
            val leqr = have(base.left |- (base.right + (l === r))) subproof { sp ?=>
              (l, r) match
                case (AppliedFunctional(labell, argsl), AppliedFunctional(labelr, argsr)) if labell == labelr && argsl.size == argsr.size => 
                  var freshn = freshId((l.freeVariables ++ r.freeVariables).map(_.id), "n").no
                  val ziped = (argsl zip argsr)
                  var zip = List[(Term, Term)]()
                  var children = List[Term]()
                  var vars = List[Variable]()
                  var steps = List[(Formula, sp.ProofStep)]()
                  ziped.reverse.foreach { (al, ar) =>
                    if al == ar then children = al :: children
                    else {
                      val x = Variable(Identifier("n", freshn))
                      freshn = freshn + 1
                      children = x :: children
                      vars = x :: vars
                      steps = (al === ar, have(proveTerm(al, ar, base))) :: steps
                      zip = (al, ar) :: zip
                    }
                  }
                  have(base.left |- (base.right + (l === l))) by Restate
                  val eqs = zip.map((l, r) => l === r)
                  val goal = have((base.left ++ eqs) |- (base.right + (l === r))).by.bot
                  have((base.left ++ eqs) |- (base.right + (l === r))) by RightSubstEq.withParametersSimple(zip, lambda(vars, l === labelr.applyUnsafe(children)))(lastStep)
                  steps.foreach { s =>
                    have(
                      if s._2.bot.left.contains(s._1) then lastStep.bot else lastStep.bot -<< s._1
                    ) by Cut(s._2, lastStep)
                  }
                case _ => 
                  println(s"l: $l")
                  println(s"r: $r")
                  throw UnreachableException
        
            }
            if id1 != l then
              val goalSequent = base.left |- (base.right + (id1 === r))
              val x = freshVariable(id1)
              have(goalSequent +<< (l === r)) by RightSubstEq.withParametersSimple(List((l, r)), lambda(x, id1 === x))(prev)
              have(goalSequent) by Cut(leqr, lastStep)
        }
    }
  }

  def proveFormula(using lib: Library, proof: lib.Proof)(id1: Formula, id2:Formula, base: Sequent): proof.ProofTacticJudgement = 
    TacticSubproof { proveInnerFormula(id1, id2, base) }

  def proveInnerFormula(using lib: Library, proof: lib.Proof)(id1: Formula, id2:Formula, base: Sequent): Unit = {
    import lib.*
    val steps = explain(id1, id2)
    steps match {
      case None => throw new Exception("No proof found in the egraph")
      case Some(steps) => 
        if steps.isEmpty then have(base.left |- (base.right + (id1 <=> id2))) by Restate
        steps.foreach {
          case FormulaExternal((l, r)) => 
            val goalSequent = base.left |- (base.right + (id1 <=> r))
            if l == id1 then 
              have(goalSequent) by Restate
            else
              val x = freshVariableFormula(id1)
              have(goalSequent) by RightSubstIff.withParametersSimple(List((l, r)), lambda(x, id1 <=> x))(lastStep)
          case FormulaCongruence((l, r)) => 
            val prev = if id1 != l then lastStep else null
            val leqr = have(base.left |- (base.right + (l <=> r))) subproof { sp ?=>
              (l, r) match
                case (AppliedConnector(labell, argsl), AppliedConnector(labelr, argsr)) if labell == labelr && argsl.size == argsr.size => 
                  var freshn = freshId((l.freeVariableFormulas ++ r.freeVariableFormulas).map(_.id), "n").no
                  val ziped = (argsl zip argsr)
                  var zip = List[(Formula, Formula)]()
                  var children = List[Formula]()
                  var vars = List[VariableFormula]()
                  var steps = List[(Formula, sp.ProofStep)]()
                  ziped.reverse.foreach { (al, ar) =>
                    if al == ar then children = al :: children
                    else {
                      val x = VariableFormula(Identifier("n", freshn))
                      freshn = freshn + 1
                      children = x :: children
                      vars = x :: vars
                      steps = (al <=> ar, have(proveFormula(al, ar, base))) :: steps
                      zip = (al, ar) :: zip
                    }
                  }
                  have(base.left |- (base.right + (l <=> l))) by Restate
                  val eqs = zip.map((l, r) => l <=> r)
                  val goal = have((base.left ++ eqs) |- (base.right + (l <=> r))).by.bot
                  have((base.left ++ eqs) |- (base.right + (l <=> r))) by RightSubstIff.withParametersSimple(zip, lambda(vars, l <=> labelr.applyUnsafe(children)))(lastStep)
                  steps.foreach { s =>
                    have(
                      if s._2.bot.left.contains(s._1) then lastStep.bot else lastStep.bot -<< s._1
                    ) by Cut(s._2, lastStep)
                  }

                case (AppliedPredicate(labell, argsl), AppliedPredicate(labelr, argsr)) if labell == labelr && argsl.size == argsr.size => 
                  var freshn = freshId((l.freeVariableFormulas ++ r.freeVariableFormulas).map(_.id), "n").no
                  val ziped = (argsl zip argsr)
                  var zip = List[(Term, Term)]()
                  var children = List[Term]()
                  var vars = List[Variable]()
                  var steps = List[(Formula, sp.ProofStep)]()
                  ziped.reverse.foreach { (al, ar) =>
                    if al == ar then children = al :: children
                    else {
                      val x = Variable(Identifier("n", freshn))
                      freshn = freshn + 1
                      children = x :: children
                      vars = x :: vars
                      steps = (al === ar, have(proveTerm(al, ar, base))) :: steps
                      zip = (al, ar) :: zip
                    }
                  }
                  have(base.left |- (base.right + (l <=> l))) by Restate
                  val eqs = zip.map((l, r) => l === r)
                  val goal = have((base.left ++ eqs) |- (base.right + (l <=> r))).by.bot
                  have((base.left ++ eqs) |- (base.right + (l <=> r))) by RightSubstEq.withParametersSimple(zip, lambda(vars, l <=> labelr.applyUnsafe(children)))(lastStep)
                  steps.foreach { s =>
                    have(
                      if s._2.bot.left.contains(s._1) then lastStep.bot else lastStep.bot -<< s._1
                    ) by Cut(s._2, lastStep)
                  }
                case _ => 
                  println(s"l: $l")
                  println(s"r: $r")
                  throw UnreachableException
        
            }
            if id1 != l then
              val goalSequent = base.left |- (base.right + (id1 <=> r))
              val x = freshVariableFormula(id1)
              have(goalSequent +<< (l <=> r)) by RightSubstIff.withParametersSimple(List((l, r)), lambda(x, id1 <=> x))(prev)
              have(goalSequent) by Cut(leqr, lastStep)
        
        }
    }
  }


}