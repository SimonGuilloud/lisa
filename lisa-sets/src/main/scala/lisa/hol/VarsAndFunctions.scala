
package lisa.hol

import lisa.maths.SetTheory.Types
import lisa.maths.SetTheory.Types.Tactics.*

import lisa.utils.fol.FOL as F
import lisa.utils.fol.FOL.*
import lisa.utils.prooflib.ProofTacticLib.ProofTactic
import lisa.SetTheoryLibrary
import lisa.maths.SetTheory.Types.Tactics.Typecheck
import lisa.maths.SetTheory.Types.TypingHelpers.{=== => _, *}
//import lisa.hol.VarsAndFunctions.HOLSequent.toHOLSequent
import lisa.maths.SetTheory.Base.Predef.{pair, ∅, singleton, unorderedPair, ∈ }
import lisa.maths.SetTheory.Base.CartesianProduct.cartesianProduct
import lisa.maths.SetTheory.Base.Pair.{snd}
import lisa.maths.SetTheory.Functions.Function.app
import lisa.maths.SetTheory.Types.Tactics.Typecheck

import scala.annotation.targetName
//import lisa.utils.unification.UnificationUtils.matchTerm

object VarsAndFunctions extends lisa.Main :

  // import TypeSystem.*

  val f = variable[Ind]
  val x, y, z = variable[Ind]
  val a = variable[Ind]
  val A, B = variable[Ind]
  val any = DEF(λ(x, ⊤))


  // A ->: B is the set of functions from A to B
  private val Bool: Constant[Ind] = {
    val 𝔹 = DEF(unorderedPair(∅, singleton(∅)))
    𝔹
  }

  val `0 : 𝔹` = Theorem(∅ :: Bool) {
    have(∅ :: unorderedPair(∅, singleton(∅))) by Tautology.from(pairAxiom of (z := ∅, x := ∅, y := singleton(∅)))
    thenHave(thesis) by Substitute(Bool.definition)
  }

  val `1 : 𝔹` = Theorem(singleton(∅) :: Bool) {
    have(singleton(∅) :: unorderedPair(∅, singleton(∅))) by Tautology.from(pairAxiom of (z := singleton(∅), x := ∅, y := singleton(∅)))
    thenHave(thesis) by Substitute(Bool.definition)
  }

  val Zero: TypedConstant = {
    val Zero = DEF(∅)
    val Zero_in_B = Theorem(Zero :: Bool) {
      have(thesis) by Substitute(Zero.definition)(`0 : 𝔹`)
    }
    Zero.typedWith(Bool)(Zero_in_B)
  }

  val One: TypedConstant = {
    val One = DEF(singleton(∅))
    val One_in_B = Theorem(One :: Bool) {
      have(thesis) by Substitute(One.definition)(`1 : 𝔹`)
    }
    One.typedWith(Bool)(One_in_B)
  }

  val zero_in_B = Theorem(Zero :: Bool) {
    have(Zero :: Bool) by Typecheck.prove
  }




  ///////////////////////////////////////////////
  /////////// Typed HOL Terms ///////////////////
  ///////////////////////////////////////////////

      
  var counter: Int = 0
  def nextId: Identifier = {
    counter += 1
    Identifier("$λ", counter)
  }

  sealed trait TypedHOLTerm {
    this : Expr[Ind] & HOLTerm =>
    val typ: Typ
    def asTerm: Expr[Ind] & TypedHOLTerm = this
    var typThm: Option[JUSTIFICATION] = None // conditional proof of this :: typ
  }

  class HOLConstant(id: Identifier, override val typ: Expr[Ind], val thm: JUSTIFICATION) extends TypedConstant(id, typ, thm) with TypedHOLTerm {
    typThm = Some(thm)
  }

  type HOLTerm = HOLApplication | TypedVar |  TypedConstant  | HOLAbstraction // | PolymorphicConstant[?]

  var i = 0
  extension (ht: HOLTerm)
    def typ = ht match
      case ht: TypedHOLTerm => ht.typ
      case tc: TypedConstant => tc.typ.asInstanceOf[Expr[Ind]]

    def getTypThmOrElseUpdate(computeProof: Proof ?=> Unit): JUSTIFICATION = {
      ht match
        case ht: TypedHOLTerm => 
          ht.typThm match
            case Some(thm) => thm
            case None => 
              val name = "¢typ_hol_" + i
              i += 1
              val ctx = computeContext(Set(ht.asTerm))
              val newthm = THM( ctx.asInstanceOf[Set[Expr[Prop]]] |- (ht.asTerm::ht.typ), name, summon[sourcecode.Line].value, summon[sourcecode.File].value, InternalStatement)(pr ?=> computeProof(using pr))
              ht.typThm = Some(newthm)
              newthm
        case tc: TypedConstant => tc.justif


    }

  class HOLApplication(func: Expr[Ind], arg: Expr[Ind]) extends App[Ind, Ind](App(app, func), arg) with TypedHOLTerm {
    val typ = computeType(func) match {
      case SArrow(inType, outType) => 
        if computeType(arg) == inType then outType
        else 
          throw new IllegalArgumentException("Argument " + arg + " of function " + func + " has type " + computeType(arg) + " instead of expected " + inType + ".")
      case funcType => throw new IllegalArgumentException("Function " + func + " expected to have function type A ->: B, but has type " + funcType + ". ")
    }

  }

  class TypedVar( id: Identifier, val typ: Typ ) extends Variable[Ind](id) with TypedHOLTerm {
    override def substituteUnsafe(map: Map[Variable[?], Expr[?]]): Expr[Ind] = 

      if map.contains(this) then map(this).asInstanceOf[Expr[Ind]]
      else 
        val typ2 = typ.substituteUnsafe(map)
        if typ2 == typ then this
        else new TypedVar(id, typ2)

    def toStringFull = s"(${id.name}: $typ)"

    def instType(map: Map[Variable[?], Expr[?]]): TypedVar = new TypedVar(id, typ.substituteUnsafe(map))

  }



  class HOLAbstraction(x: TypedVar, body: Expr[Ind]) extends App[Ind >>: Ind, Ind](abs(x.typ), (λ(x, body))) with TypedHOLTerm {
    val typ = x.typ ->: computeType(body)
  }

  def fun(v: TypedVar, b: Expr[Ind]): Expr[Ind] = HOLAbstraction(v, b)


  def computeType(t:Expr[Ind]): Typ = 
    val r = t match 
      case tv: TypedVar => tv.typ
      case tc: TypedConstant => tc.typ
      case #@[Ind >>: Ind, Ind](#@[Ind, (Ind >>: Ind) >>: Ind](`abs`, base), Abs(v: TypedVar, b)) => 
        v.typ ->: computeType(b)
      case App(App(`app`, func), arg) => 
        computeType(func) match 
          case dom ->: codom => 
            if computeType(arg) == dom then codom
            else throw new IllegalArgumentException("In application " + t + ", argument " + arg + " has type " + computeType(arg) + " instead of expected " + dom + ".")
          case funcType => throw new IllegalArgumentException("In application " + t + ", function " + func + " expected to have function type A ->: B, but has type " + funcType + ". ")
      case Multiapp(func, args: List[Expr[Ind]] @unchecked) => 
        func match
          case tcf: TypedConstantFunctional[?] =>
            if tcf.arity != args.size then 
              throw new IllegalArgumentException("computeType can only handle fully applied functions. Function " + tcf + " has arity " + tcf.arity + " but was applied to " + args.size + " arguments.")
            if args.zip(tcf.typ.inTyp).forall((arg, inType) => inType match
              case Some(value) => 
                val argType = computeType(arg)
                lisa.utils.fol.FOL.isSame(optype(inType, arg), (arg is argType))
              case None => true
            ) then
              val subst = (tcf.typ.args zip args).map((v, a) => (v := a))
              tcf.typ.outTyp.substitute(subst*)
            else
              val argsTypes = args.map(arg =>
                try computeType(arg)
                catch
                  case e: IllegalArgumentException => "?"
              )
              throw new IllegalArgumentException("Function " + tcf + " has type " + tcf.typ + " but was applied to arguments " + args + " of types " + argsTypes + ".")
          case _ => throw new IllegalArgumentException("computeType can only handle typed constant functionals. " + func + " is not a typed constant functional.")
      case _ => throw new IllegalArgumentException("computeTypes only support fully typed terms. " + t + " is not fully typed.")
    r


  def computeContext(terms: Set[Expr[Ind]]): Set[VarTypeAssign] = computeContextKnown(terms, Set.empty)

  def computeContextKnown(terms: Set[Expr[Ind]], known: Set[Variable[Ind]]): Set[VarTypeAssign] = 
    val frees = terms.flatMap(_.freeVars) -- known
    val r1 = frees.foldLeft(List.empty[VarTypeAssign]) {
      case (acc1, v: TypedVar) => 
        (v is v.typ) :: acc1
      case (acc1, v) => 
        acc1
    }
    r1.toSet

  def computeContextOfFormulas(formulas: Set[Expr[Prop]], known: Set[Variable[Ind]] = Set()): (Set[VarTypeAssign]) = 
    val vars = formulas.flatMap(_.freeVars) -- known
    computeContextKnown(vars.filter(_.sort == K.Ind).toSet.asInstanceOf[Set[Expr[Ind]]], Set.empty)

  class HOLSequent(
    val premises: Set[Expr[Ind]],
    val conclusion: Expr[Ind],
    val varTypes: Set[VarTypeAssign]
    ) extends F.Sequent(premises.map(_ === One) ++ varTypes, Set(conclusion === One)) {
      
      infix def +<<(t: Expr[Ind]): HOLSequent = HOLSequent(this.premises + t, conclusion)
      infix def -<<(t: Expr[Ind]): HOLSequent = HOLSequent(this.premises - t, conclusion)

      override infix def +<<(f: Expr[Prop]): F.Sequent = 
        f match 
          case ===(t, One) => +<<(t)
          case ===(One, t) => +<<(t)
          case _ => super.+<<(f)
      override infix def -<<(f: Expr[Prop]): F.Sequent = 
        f match 
          case ===(t, One) => -<<(t)
          case ===(One, t) => -<<(t)
          case _ => super.-<<(f)

      infix def ++<<(s1: HOLSequent): HOLSequent = HOLSequent(this.premises ++ s1.premises, conclusion)
      infix def --<<(s1: HOLSequent): HOLSequent = HOLSequent(this.premises -- s1.premises, conclusion)

      override infix def ++<<(s1: F.Sequent): F.Sequent = 
        s1 match 
          case s1: HOLSequent => ++<<(s1)
          case s1: F.Sequent => super.++<<(s1)
      override infix def --<<(s1: F.Sequent): F.Sequent = 
        s1 match 
          case s1: HOLSequent => --<<(s1)
          case s1: F.Sequent => super.--<<(s1)
  }

  object HOLSequent {
    def apply(premises: Set[Expr[Ind]], conclusion: Expr[Ind]): HOLSequent = {
      val (valTypes) = computeContext(premises + conclusion)
      new HOLSequent(premises, conclusion, valTypes)
    }

    def fromFOLSequent(s: F.Sequent): HOLSequent = 
      if s.isInstanceOf[HOLSequent] then 
        return s.asInstanceOf[HOLSequent]
      if s.right.size != 1 then 
        throw new IllegalArgumentException("Sequent in HOL must have exactly one conclusion.")
      val r = s.right.head
      r match 
        case eqOne(t) => 
          var vartypes = List.empty[VarTypeAssign]
          var prems = Set.empty[Expr[Ind]]
          s.left.foreach {a => a match 
            case VarTypeAssign(_, _)  => vartypes = a.asInstanceOf[VarTypeAssign] :: vartypes
            case eqOne(t) => prems = prems + t
            case _ => throw new IllegalArgumentException("Premises must be of the form t === One, be a type assignment or an abstraction definition.")
          }
          new HOLSequent(prems.toSet, t, vartypes.toSet)
        case _ => 
          throw new IllegalArgumentException("Conclusion must be of the form t === One.")
  }


  def typedvar(using name: sourcecode.Name)(typ: Typ): TypedVar = new TypedVar(Identifier(name.value), typ)

  opaque type TypedForall <: Expr[Prop] & {val v: Variable[Ind]; val prop: Expr[Prop]} = TypedForallConcrete

  private class TypedForallConcrete( val v: Variable[Ind], val prop: Expr[Prop] ) extends App(forall, λ(v, v match {
    case v: TypedVar => (v is v.typ) ==> prop
    case _ => forall(v, prop)
  })) {
    override def toString = 
      val typeStr = v match
        case v: TypedVar => s" : ${v.typ}"
        case _ => "" 
      s"∀$v$typeStr. $prop"
  }

  object TypedForall {
    def apply(v: TypedVar, prop: Expr[Prop]): TypedForall = new TypedForallConcrete(v, prop)
  }

  def tforall(v: TypedVar, prop: Expr[Prop]): TypedForall = TypedForall(v, prop)
  inline given Conversion[TypedForall, Expr[Prop]] with
    def apply(tf: TypedForall): Expr[Prop] = tf



  val functionalExtentionality = Axiom({
    val f = typedvar(A ->: B)
    val g = typedvar(A ->: B)
    val x = typedvar(A)
    ((f :: (A ->: B)) /\ (g :: (A ->: B)) /\ tforall(x, f*x === g*x)) ==> (f === g)
  })


  val boolNonEmpty = Theorem(exists(x, (x ∈ Bool))) {
    have(thesis) by RightExists(One.justif)
  }
  val 𝔹 = ConstantTypeTerm("𝔹", boolNonEmpty)


  val =:= : TypedConstantFunctional[Ind >>: Ind] ={
    val =:= =  Constant[Ind >>: Ind]("=:=").printInfix()
    addSymbol(=:=)
    val typing_of_eq = Axiom(forall(A, =:=(A) :: (A ->: (A ->: 𝔹))))
    TypedConstantFunctional[Ind >>: Ind]("=:=", FunctionalClass(List(None), List(A), (A ->: (A ->: 𝔹))), typing_of_eq)
  }
  lazy val eqDefin = {
    val x = typedvar(A)
    val y = typedvar(A)
    val eqDefin = Axiom(((x::A) /\ (y::A)) ==> ((x =:= y)===One) <=> (x===y))
    eqDefin
  }

  val holeq : TypedConstantFunctional[Ind >>: Ind] = VarsAndFunctions.=:=

  object eqOne {
    def unapply(f: Expr[Prop]): Option[Expr[Ind]] = f match {
      case ===(t, One) => Some(t)
      case ===(One, t) => Some(t)
      case _ => None
    }
    
      def apply(t: Expr[Ind]): Expr[Prop] = t === One
  }

  given Conversion[Expr[Ind], F.Expr[Prop]] = t => eqOne(t)

  extension (t1:Expr[Ind]) {
    def =:=(t2:Expr[Ind]): Expr[Ind] = 
      val A = computeType(t1)
      if (A == computeType(t2)) 
        holeq(A)*(t1)*(t2) 
      else 
        throw new Exception("in expression " + t1 + " =:= " + t2 + " the types " + A + "of left-hand side and " + computeType(t2) + " of right-hand side do not match.")
    def equalityOfType(A:Expr[Ind]) (t2:Expr[Ind]): Expr[Ind] = holeq(A)*(t1)*(t2) //compute A with computeType, possibly.
  }





  object TypeNonEmptyProof extends ProofTactic {
    val A = variable[Ind]
    val B = variable[Ind]
    val nonEmptyFuncSpace = Axiom(exists(x, x ∈ B) ==> exists(x, x ∈ (A ->: B)))
    
    def apply(using proof: Proof)(typ: Expr[Ind]): proof.ProofTacticJudgement = TacticSubproof{ ip ?=>
      typ match {
        case ctt: ConstantTypeTerm => have(ctt.nonEmptyThm)
        case v: Variable[Ind] => 
          val x = Variable.fresh[Ind](Set(v), "x")
          have(exists(x, x ∈ v) |- exists(x, x ∈ v))
        case a ->: b => 
          val x = Variable.fresh[Ind](Set(a, b), "x")
          val s1 = have(TypeNonEmptyProof(b))
          have(exists(x, x ∈ (a ->: b))) by Tautology.from(s1, nonEmptyFuncSpace of (A := a, B := b))
        case _ => throw new IllegalArgumentException("TypeNonEmptyProof can only handle type constants, type variables, and function types.")
      }
    }
  }

  class ConstantTypeTerm(id: Identifier, val nonEmptyThm: JUSTIFICATION) extends Constant[Ind](id)



  val T = variable[Ind]
  val nonEmptyTypeExists = Theorem(exists(T, exists(x, (x ∈ T)))) {
    have(thesis) by RightExists(boolNonEmpty)
  }

  def TypingTheorem(using om: lisa.utils.prooflib.OutputManager, name: sourcecode.FullName)(assignment: Expr[Prop]): THM = 
    Theorem(using om, name)(computeContextOfFormulas(Set(assignment)) |- assignment) {
      have(thesis) by Typecheck.prove
    }


  object HOLProofType extends ProofTactic {
    def apply2(using proof: SetTheoryLibrary.Proof)(t:Expr[Ind]): proof.ProofTacticJudgement =
      val context: Set[ Expr[Prop]] = computeContext(Set(t)).toSet
      Typecheck.inferProof(context, t)

    def apply(using proof: SetTheoryLibrary.Proof)(t:Expr[Ind]): proof.ProofTacticJudgement = TacticSubproof {
      given SetTheoryLibrary.type = SetTheoryLibrary
      val r = if false then apply2(t) else t match 
        case t: HOLTerm => 
          t.getTypThmOrElseUpdate {
            have(apply2(t))
          }
        case _ => 
          apply2(t)
      val r1 = have(r)
      val r2 = have(r1.statement) by lisa.utils.prooflib.BasicStepTactic.Weakening(r1)
    }
  }


  given termToSetConv[T <: Expr[Ind]]: FormulaSetConverter[T] = t => Set(eqOne(t))
  given setTermToSetConv[T <: Iterable[Expr[Ind]]]: FormulaSetConverter[T] = _.map(eqOne(_)).toSet


  given Conversion[Expr[Ind], HOLSequent] = HOLSequent(Set(), _)


end VarsAndFunctions


/*
object VarsAndFunctions {

  val =:= : TypedConstantFunctional[1] ={
    val =:= =  F.ConstantFunctionLabel.infix("=:=", 1)
    addSymbol(=:=)
    val typ =  (A ->: (A ->: 𝔹))
    val typing_of_eq = Axiom(F.forall(A, =:=(A) :: typ))
    TypedConstantFunctional[1]("=:=", 1, FunctionalClass(Seq(any), Seq(A), (A ->: (A ->: 𝔹)), 1), typing_of_eq)
  }
  lazy val eqDefin = {
    val x = typedvar(A)
    val y = typedvar(A)
    val eqDefin = Axiom(((x::A) /\ (y::A)) ==> ((x =:= y)===One) <=> (x===y))
    eqDefin
  }

  val holeq : TypedConstantFunctional[1] = VarsAndFunctions.=:=

  object eqOne {
    def unapply(f: Expr[Prop]): Option[Expr[Ind]] = f match {
      case ===(t, One) => Some(t)
      case ===(One, t) => Some(t)
      case _ => None
    }
    
      def apply(t: Expr[Ind]): Expr[Prop] = t === One
  }

  given Conversion[Expr[Ind], F.Expr[Prop]] = t => eqOne(t)

  extension (t1:Expr[Ind]) {
    def =:=(t2:Expr[Ind]): Expr[Ind] = 
      val A = computeType(t1)
      if (A == computeType(t2)) 
        holeq.applySeq(Seq(A))*(t1)*(t2) 
      else 
        throw new TypingException("in expression " + t1 + " =:= " + t2 + " the types " + A + "of left-hand side and " + computeType(t2) + " of right-hand side do not match.")
    def equalityOfType(A:Expr[Ind]) (t2:Expr[Ind]): Expr[Ind] = holeq.applySeq(Seq(A))*(t1)*(t2) //compute A with computeType, possibly.
  }

  object HOLSequent {
    def apply(premises: Set[Expr[Ind]], conclusion: Expr[Ind]): HOLSequent = {
      val (valTypes, abstr) = HOLSeqToFOLSeq(premises, conclusion)
      new HOLSequent(premises, conclusion, valTypes, abstr)
    }

    def toHOLSequent(s: F.Sequent): HOLSequent = 
      if s.isInstanceOf[HOLSequent] then 
        return s.asInstanceOf[HOLSequent]
      if s.right.size != 1 then 
        throw new IllegalArgumentException("Sequent must have exactly one conclusion.")
      val r = s.right.head
      r match 
        case eqOne(t) => 
          var vartypes = List.empty[VarTypeAssign]
          var abstr = List.empty[AbstractionDefinition]
          var prems = Set.empty[Expr[Ind]]
          s.left.foreach {
            case v: VarTypeAssign => vartypes = v :: vartypes
            case a: AbstractionDefinition => abstr = a :: abstr
            case eqOne(t) => prems = prems + t
            case _ => throw new IllegalArgumentException("Premises must be of the form t === One, be a type assignment or an abstraction definition.")
          }
          new HOLSequent(prems.toSet, t, vartypes.toSet, abstr.toSet)
        case _ => 
          throw new IllegalArgumentException("Conclusion must be of the form t === One.")
      


    def unapply(s: F.Sequent): Option[(Set[Expr[Ind]], Expr[Ind])] = 
      if s.isInstanceOf[HOLSequent] then 
        val s1 = s.asInstanceOf[HOLSequent]
        Some((s1.premises, s1.conclusion))
      else 
        try {
          val s1 = toHOLSequent(s)
          Some((s1.premises, s1.conclusion))
        }
        catch
          case e: IllegalArgumentException => 
            println(e.getMessage())
            return None


  }


  def TypingTheorem(using om: lisa.utils.prooflib.OutputManager, name: sourcecode.FullName)(assignment: TypeAssignment[Typ]): THM = 
    val (l1, l2) = HOLSeqToFOLSeq(Set.empty, assignment.t)
    Theorem(using om, name)(F.Sequent(l1 ++ l2, Set(assignment.t is assignment.typ))) {
      have(thesis) by TypeChecker.prove
    }


    
  extension (t:Expr[Ind]) {
    def * (t2:Expr[Ind]): Expr[Ind] = HOLApplication(t, t2)
  }

  object * {def unapply(t: Expr[Ind]): Option[(Expr[Ind], Expr[Ind])] = t match {
    case AppliedFunction(f, a) => Some((f, a))
    case app(f, a) => Some((f, a))
    case _ => None
  }}

  ///////////////////////////////////////
  /////////// Typed Variables ///////////
  ///////////////////////////////////////

  class TypedForall( val v: Variable[Ind], val prop: Expr[Prop] ) extends BinderFormula(forall, v, v match {
    case v: TypedVar => (v is v.typ) ==> prop
    case _ => prop
  }
  ) {
    override def toString = 
      val typeStr = v match
        case v: TypedVar => s" : ${v.typ}"
        case _ => "" 
      s"∀$v$typeStr. $prop"
  }


  def tforall(v: TypedVar, prop: Expr[Prop]): TypedForall = TypedForall(v, prop)

  var counter: Int = 0

  type VarTypeAssign = Expr[Prop] & TypeAssignment[Typ] {val t:Variable[Ind]}
  

  def nextId: Identifier = {
    counter += 1
    Identifier("$λ", counter)
  }

  sealed trait TypedHOLTerm {
    this : Expr[Ind] =>
    val typ: Typ
    def asTerm: Expr[Ind] & TypedHOLTerm = this
    var typThm: Option[JUSTIFICATION] = None // conditional proof of this :: typ
  }

  class PolymorphicConstant[N <: Arity](label: TypedConstantFunctional[N], args: Expr[Ind]**N) extends AppliedFunctional(label, args.toSeq) with TypedHOLTerm {
    val typ = {
      val subst = (label.typ.args zip args.toSeq).map((v, a) => (v := a))
      label.typ.out.asInstanceOf[Expr[Ind]].substitute(subst: _*)
    }

  }
  class HOLConstant(id: Identifier, override val typ: Expr[Ind], val thm: JUSTIFICATION) extends TypedConstant[Expr[Ind]](id, typ, thm) with TypedHOLTerm {
    typThm = Some(thm)
  }

  type HOLTerm = HOLApplication | TypedVar | Abstraction | TypedConstant[Expr[Ind]] | PolymorphicConstant[?]

  var i = 0
  extension (ht: HOLTerm)
    def typ = ht match
      case ht: TypedHOLTerm => ht.typ
      case tc: TypedConstant[?] => tc.typ.asInstanceOf[Expr[Ind]]
    
    def getTypThmOrElseUpdate(computeProof: Proof ?=> Unit): JUSTIFICATION = {
      ht match
        case ht: TypedHOLTerm => 
          ht.typThm match
            case Some(thm) => thm
            case None => 
              val name = "¢typ_hol_" + i
              i += 1
              val ctx = computeContext(Set(ht.asTerm))
              val newthm = THM( (ctx._1 ++ ctx._2) |- (ht.asTerm::ht.typ), name, summon[sourcecode.Line].value, summon[sourcecode.File].value, InternalStatement)(pr ?=> computeProof(using pr))
              ht.typThm = Some(newthm)
              newthm
        case tc: TypedConstant[?] => tc.justif
      
      
    }

  class HOLApplication(func: Expr[Ind], arg: Expr[Ind]) extends AppliedFunction(func, arg) with TypedHOLTerm {
    val typ = computeType(func) match {
      case inType ->: outType => 
        if computeType(arg) == inType then outType
        else 
          throw new IllegalArgumentException("Argument " + arg + " of function " + func + " has type " + computeType(arg) + " instead of expected " + inType + ".")
      case funcType => throw new IllegalArgumentException("Function " + func + " expected to have function type A ->: B, but has type " + funcType + ". ")
    }

  }

  class TypedVar( id: Identifier, val typ: Typ ) extends Variable[Ind](id) with TypedHOLTerm {
    override def substituteUnsafe(map: Map[SchematicLabel[?], LisaObject[?]]): Expr[Ind] = 

      if map.contains(this) then map(this).asInstanceOf[Expr[Ind]]
      else 
        val typ2 = typ.substituteUnsafe(map)
        if typ2 == typ then this
        else new TypedVar(id, typ2)

    def toStringFull = s"(${id.name}: $typ)"

    def instType(map: Map[SchematicLabel[?], LisaObject[?]]): TypedVar = new TypedVar(id, typ.substituteUnsafe(map))
    
  }


  ///////////////////////////////////////
  ///////// Lambda Abstractions /////////
  ///////////////////////////////////////


  class AbstrVar( id: Identifier, val defin:AbstractionDefinition ) extends TypedVar(id, defin.typ){
    override def substituteUnsafe(map: Map[SchematicLabel[?], LisaObject[?]]): Expr[Ind] = 

      if map.contains(this) then map(this).asInstanceOf[Expr[Ind]]
      else 
        val typ2 = defin.typ.substituteUnsafe(map)
        if typ2 == defin.typ then this
        else 
          val t = new AbstrVar(id, defin.substituteUnsafe(map - this).asInstanceOf) // TODO: appropriate?
          t
  }



  trait Abstraction  extends TypedHOLTerm{
    this : Expr[Ind] =>
    override def asTerm: Abstraction & Expr[Ind] = this

    val bound: TypedVar
    val body: Expr[Ind]
    val repr: AbstrVar
    val freeVars: Seq[TypedVar]
    val defin: AbstractionDefinition


    val origin: Expr[Ind]

    val typ: Typ


    override def toString = s"${repr.id}($bound. $body)"


    private lazy val t = this * bound
    lazy val betaName = "¢beta_" + repr.id
    // import HOLSteps.{=:= => _, *, given}
    

    lazy val BETA = THM( t =:= body, betaName, summon[sourcecode.Line].value, summon[sourcecode.File].value, InternalStatement) {
      val context = VarsAndFunctions.computeContext(Set(t, body))
      assume((context._1 ++ context._2).toSeq: _*)
      val outType = defin.outType
      val pro = have(defin.bodyProp |- defin.bodyProp) by Restate
      freeVars.reverse.foreach(v => 
        have(lastStep.statement.right.head.asInstanceOf[TypedForall].prop) by Weakening(lastStep of v)
      )
      val aftFreeVars = lastStep
      val h = have((bound::bound.typ) |- (t === body)) by Weakening(aftFreeVars of bound)
      val h2 = have((bound::bound.typ, t::outType, body::outType) |- ((t =:= body) === One) ) by Substitute(HOLSteps.eqCorrect of (x := t, y := body, A := outType))(h)
      val h3 = have(ProofType(body))
      val h4 = have(((bound::bound.typ, t::outType) |- ((t =:= body) === One)) ++<? h3.statement) by Cut.withParameters(body::outType)(h3, h2)
      val h5 = have(ProofType(t))
      val h6 = have(((bound::bound.typ) |- ((t =:= body) === One)) ++<? h3.statement ++<? h5.statement) by Cut.withParameters(t::outType)(h5, h4)
      val c = thenHave(t =:= body) by Restate
    }

     
  }

  class AbstractionClosureWithoutFreeVars private[VarsAndFunctions] (
    val reprId: Identifier,
    val bound: TypedVar,
    val body: Expr[Ind],
    defin: AbstractionDefinition
  ) extends AbstrVar(reprId, defin) with Abstraction{

    override def substituteUnsafe(map: Map[F.SchematicLabel[?], F.LisaObject[?]]): Expr[Ind] = 
      if map.contains(repr) then map(repr).asInstanceOf[Expr[Ind]]
      else if (defin.freeVars.exists(v => map.contains(v))) then 
        TypeInstAbstractionWithout(this, map.asInstanceOf)
      else 
        val newMap = map - bound
        AbstractionClosureWithoutFreeVars(reprId, bound.instType(newMap), body.substituteUnsafe(newMap), defin.substituteUnsafe(newMap).asInstanceOf)

    val repr: AbstrVar = this
    val freeVars: Seq[TypedVar] = Seq.empty
    val origin = this
    //override def toString = s"(λ$bound. $body)"
  }

  class AbstractionClosureWithFreeVars private[VarsAndFunctions] (
    val repr: AbstrVar,
    val bound: TypedVar,
    val body: Expr[Ind],
    val freeVars: Seq[TypedVar],
    val defin: AbstractionDefinition
  ) extends AppliedFunction(freeVars.init.foldLeft(repr: Expr[Ind])((acc, v) => acc*v), freeVars.last) with Abstraction {

    //override def toString = s"(λ$bound. $body)"
    val origin = AppliedFunction(freeVars.init.foldLeft(repr: Expr[Ind])((acc, v) => acc*v), freeVars.last)
    val typ = bound.typ ->: defin.outType
    override def substituteUnsafe(map: Map[F.SchematicLabel[?], F.LisaObject[?]]): AppliedFunction = 
      if map.contains(repr) then super.substituteUnsafe(map)
      else if (defin.freeVars.exists(v => map.contains(v))) then 
        TypeInstAbstractionWith(this, map.asInstanceOf)
      else 
        val r = InstAbstraction(this, freeVars.map(v => map.getOrElse(v, v)).asInstanceOf)
        val exp = super.substituteUnsafe(map)
        
        r
  }

  class InstAbstraction(
    val base: Abstraction,
    val insts: List[Expr[Ind]]
  ) extends AppliedFunction(insts.init.foldLeft(base.repr: Expr[Ind])((acc, v) => acc @@ v), insts.last) with TypedHOLTerm {
    val typ = base.typ

    override def toString() = "I"+super.toString()

  }

  class TypeInstAbstractionWithout(
    val base:AbstractionClosureWithoutFreeVars,
    val typeinst: Map[lisa.utils.fol.FOL.SchematicLabel[?], lisa.utils.fol.FOL.LisaObject[?]]
  ) extends AbstractionClosureWithoutFreeVars(base.reprId, base.bound.substituteUnsafe(typeinst).asInstanceOf, base.body.substituteUnsafe(typeinst), base.defin.substituteUnsafe(typeinst).asInstanceOf)

  class TypeInstAbstractionWith(
    val base:AbstractionClosureWithFreeVars,
    val typeinst: Map[lisa.utils.fol.FOL.SchematicLabel[?], lisa.utils.fol.FOL.LisaObject[?]]
  ) extends AbstractionClosureWithFreeVars(base.repr.substituteUnsafe(typeinst).asInstanceOf, base.bound.substituteUnsafe(typeinst).asInstanceOf, base.body.substituteUnsafe(typeinst), base.freeVars.map(_.substituteUnsafe(typeinst)).asInstanceOf, base.defin.substituteUnsafe(typeinst).asInstanceOf)
  


  object Abstraction {

    val cache = collection.mutable.HashMap.empty[(F.Identifier, Expr[Ind], Expr[Ind]), Abstraction & Expr[Ind]]
    def apply(bound: TypedVar, body: Expr[Ind]): Abstraction & Expr[Ind] = {
      cache.getOrElseUpdate((bound.id, bound.typ, body), {
        val freeVars: Seq[TypedVar] = (body.freeVars - bound).toSeq.sortBy(_.id.name).collect {
          case v: TypedVar if !v.isInstanceOf[AbstrVar] => v
        }
        val repr = Variable[Ind](nextId)
        val inner = tforall(bound, 
            (freeVars.foldLeft[Expr[Ind]](repr) { (acc, v) => 
              acc @@ v
            } @@ bound) === body
          )
        val bodyProp = freeVars.foldLeft[Expr[Prop]](inner) { (acc, v) => 
          tforall(v, acc)
        }
        val outType = computeType(body)
        

        val defin = new AbstractionDefinition(repr, bound, body, freeVars, outType, bodyProp)
        if freeVars.isEmpty then new AbstractionClosureWithoutFreeVars(repr.id, bound, body, defin)
        else new AbstractionClosureWithFreeVars(AbstrVar(repr.id, defin), bound, body, freeVars, defin)
      }.asTerm)
    }
  }
  def λ(bound: TypedVar, body: Expr[Ind]) = Abstraction(bound, body)
  
  class AbstractionDefinition(
    val reprVar: Variable[Ind],
    val bound: TypedVar,
    val body: Expr[Ind],
    val freeVars: Seq[TypedVar],
    val outType: Typ,
    val bodyProp: Expr[Prop]
  ) extends AppliedConnector(And, Seq(reprVar is freeVars.foldRight(bound.typ ->: outType)((v, acc) => v.typ ->: acc), bodyProp)) {
    val typ = freeVars.foldRight(bound.typ ->: outType)((v, acc) => v.typ ->: acc)

    override def substituteUnsafe(map: Map[F.SchematicLabel[?], F.LisaObject[?]]): Expr[Prop] = 
      if map.contains(reprVar) then super.substituteUnsafe(map)
      else 
        val newMap = map - bound -- freeVars
        AbstractionDefinition(
          reprVar, 
          bound.instType(map - bound), 
          body.substituteUnsafe(newMap), 
          freeVars.map(_.instType(newMap)), 
          outType.substituteUnsafe(newMap), 
          bodyProp.substituteUnsafe(newMap)
        )

    
    import HOLSteps.{=:= => _, *, given}
    lazy val elimName = "¢elim_" + reprVar.id
    lazy val elim = Axiom(exists(reprVar, this))



  }

  var j: Int = 0




  object ProofType extends ProofTactic {
    def apply2(using proof: SetTheoryLibrary.Proof)(t:Expr[Ind]): proof.ProofTacticJudgement =
      val context = computeContext(Set(t))
      TypeChecker.typecheck(context._1.toSeq ++ context._2.toSet, t, None)

    def apply(using proof: SetTheoryLibrary.Proof)(t:Expr[Ind]): proof.ProofTacticJudgement = TacticSubproof {
      given SetTheoryLibrary.type = SetTheoryLibrary
      val r = if true then apply2(t) else t match 
        case t: TypedHOLTerm => 
          val r = t.asInstanceOf[HOLTerm].getTypThmOrElseUpdate {
            have(apply2(t.asTerm))
          }
          lisa.utils.prooflib.SimpleDeducedSteps.Restate.from(r)(r.statement)
        case tc: TypedConstant[?] => 
          lisa.utils.prooflib.SimpleDeducedSteps.Restate.from(tc.justif)(tc.justif.statement)
        case _ => 
          apply2(t)

        val r1 = have(r)
        val r2 = have(r1.statement) by lisa.utils.prooflib.BasicStepTactic.Weakening(r1)
    }
  }

  var debug = false
  def computeType(t:Expr[Ind]): Typ = 
    val r = {
    t match
      case t: TypedVar => 
        t.typ
      case t: TypedConstant[?] => 
        t.typ match
          case t: Expr[Ind] => t
          case _ => throw new IllegalArgumentException("computeTypes only support subterms typed by terms, not untyped or typed by classes.")
      case t: AppliedFunction => 
        val funcType = computeType(t.func)
        funcType match
          case inType ->: outType => 
            if computeType(t.arg) == inType then outType
            else 
              throw new IllegalArgumentException("Argument " + t.arg + " of function " + t.func + " has type " + computeType(t.arg) + " instead of expected " + inType + ".")
          case funcType => throw new IllegalArgumentException("Function " + t.func + " expected to have function type A ->: B, but has type " + funcType + ". ")
      case AppliedFunctional(label, args) => 
        label match
          case label: TypedConstantFunctional[?] => 
            val labelType = label.typ
            if args.zip(labelType.in).forall((arg, inType) => 
              (inType == any) || {
                val argType = computeType(arg)
                K.isSame((arg is inType).asFormula.underlying, (arg is argType).asFormula.underlying)
              }
            ) then
              val subst = (labelType.args zip args).map((v, a) => (v := a))
              labelType.out match {
                case t: Expr[Ind] => t.substitute(subst: _*)
                case f: (Expr[Ind]**1 |-> Expr[Prop]) @unchecked => throw new IllegalArgumentException("computeTypes only support subterms typed by terms, not untyped or typed by classes.")
              }
            else 
              val argsTypes = args.map(arg =>
                try computeType(arg)
                catch
                  case e: IllegalArgumentException => "?"
                computeType
              )
              throw new IllegalArgumentException("Function " + label + " has type " + labelType + " but was applied to arguments " + args + " of types " + argsTypes + ".")
          case _ => 
            throw new IllegalArgumentException("computeTypes only support subterms typed by terms, not untyped or typed by classes.")
      case _ => 
        throw new IllegalArgumentException("computeTypes only support fully typed terms. " + t + " is not fully typed.")
      }
      r



  object TypeNonEmptyProof extends ProofTactic {
    val A = variable
    val B = variable
    val nonEmptyFuncSpace = Axiom(exists(x, in(x, B)) ==> exists(x, in(x, (A ->: B))))
    
    def apply(using proof: Proof)(typ: Expr[Ind]): proof.ProofTacticJudgement = TacticSubproof{ ip ?=>
      typ match {
        case ctt: ConstantTypeTerm => have(ctt.nonEmptyThm)
        case v: Variable[Ind] => 
          val x = freshVariable(Set(v), "x")
          have(exists(x, in(x, v)) |- exists(x, in(x, v)))
        case a ->: b => 
          val x = freshVariable(Set(a, b), "x")
          val s1 = have(TypeNonEmptyProof(b))
          have(exists(x, in(x, a ->: b))) by Tautology.from(s1, nonEmptyFuncSpace of (A := a, B := b))
      }
    }
  }




  class NonEmptyType(val x: Variable[Ind], val typ: Expr[Ind]) extends BinderFormula(exists, x, in(x, typ)) {
    override def toString = s"∃${variable}. ${typ}"
  }
  object NonEmptyType {
    def apply(typ: Expr[Ind]): NonEmptyType = 
      val x = freshVariable(Set(typ), "x")
      new NonEmptyType(x, typ)
    def unapply(t: NonEmptyType): Some[(Variable[Ind], Expr[Ind])] = Some(t.x, t.typ)
  }

  // Sequent Syntax

  trait TermSetConverter[T] {
    def apply(t: T): Set[Expr[Ind]]
  }

  given TermSetConverter[Unit] with {
    override def apply(u: Unit): Set[Expr[Ind]] = Set.empty
  }

  given TermSetConverter[EmptyTuple] with {
    override def apply(t: EmptyTuple): Set[Expr[Ind]] = Set.empty
  }

  given [H <: Expr[Ind], T <: Tuple](using c: TermSetConverter[T]): TermSetConverter[H *: T] with {
    override def apply(t: H *: T): Set[Expr[Ind]] = c.apply(t.tail) + t.head
  }

  given term_to_set[T <: Expr[Ind]]: TermSetConverter[T] with {
    override def apply(f: T): Set[Expr[Ind]] = Set(f)
  }

  given term_iterable_to_set[T <: Expr[Ind], I <: Iterable[T]]: TermSetConverter[I] with {
    override def apply(s: I): Set[Expr[Ind]] = s.toSet
  }

  private def any2set[A, T <: A](any: T)(using c: TermSetConverter[T]): Set[Expr[Ind]] = c.apply(any)

  extension [A, T1 <: A](left: T1)(using TermSetConverter[T1]) {
    infix def |-(right: Expr[Ind]): HOLSequent = HOLSequent(any2set(left), right)
    infix def ⊢(right: Expr[Ind]): HOLSequent = HOLSequent(any2set(left), right)
  }

  given Conversion[Expr[Ind], HOLSequent] = HOLSequent(Set(), _)

}
*/