
package lisa.hol

import lisa.maths.SetTheory.Types
import lisa.maths.SetTheory.Types.Tactics.*

import lisa.utils.fol.FOL as F
import lisa.utils.fol.FOL.*
import lisa.utils.prooflib.ProofTacticLib.ProofTactic
import lisa.SetTheoryLibrary
import lisa.maths.SetTheory.Types.Tactics.Typecheck
import lisa.maths.SetTheory.Types.TypingHelpers.{*}
//import lisa.hol.VarsAndFunctions.HOLSequent.toHOLSequent
import lisa.maths.SetTheory.Base.Predef.{pair, ∅, singleton, unorderedPair, ∈ }
import lisa.maths.SetTheory.Base.CartesianProduct.cartesianProduct
import lisa.maths.SetTheory.Base.Pair.{snd}
import lisa.maths.SetTheory.Functions.Predef.{*, given}
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
  val G, H = variable[Ind >>: Ind]


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

  class HOLConstant(id: Identifier, override val typ: Expr[Ind], val thm: JUSTIFICATION) extends TypedConstant(id, typ, thm)

  type HOLTerm = TypedConstant

  def fun(v: TypeAssign[Variable[Ind]], b: Expr[Ind]): Expr[Ind] = abs(v.typ)(λ(v.vari, b))

  type TypingContext = Map[Variable[Ind], Typ]
  type TypevarContext = Set[Variable[Ind]]

  def relevantTypeContext(t: LisaObject, context: TypingContext): Set[TypeAssign[Variable[Ind]]] = 
    val varsInT = t.freeVars
    context.filter((v, _) => varsInT.contains(v)).map((v, typ) => TypeAssign(v, typ)).toSet

  def relevantTypevarContext(lo: LisaObject, typevars: TypevarContext): Set[Variable[Ind]] =
    val varsInT = lo.freeVars
    typevars.filter(tv => varsInT.contains(tv))

  def relevantContext(t: LisaObject, context: TypingContext, typevars: TypevarContext): Set[Expr[Prop]] = 
    relevantTypeContext(t, context) ++ relevantTypevarContext(t, typevars).map(tv => 
      val v = Variable[Ind](K.Identifier("x", tv.id.no+1))
      exists(v, v ∈ tv)
    )
  
  def relevantAssumptions(lo: LisaObject)(using context: TypingContext, typevars: TypevarContext): Set[Expr[Prop]] = 
    relevantContext(lo, context, typevars) ++ relevantTypeContext(lo, context).map(ta => ta.vari :: ta.typ)

  def typeVarsFromType(typ: Typ): Set[Variable[Ind]] = 
    typ match 
      case v: Variable[Ind] => Set(v)
      case A ->: B => typeVarsFromType(A) ++ typeVarsFromType(B)
      case _ => Set.empty

  def nonEmpty(typ: Variable[Ind]): Expr[Prop] = 
    val v = if typ.id.name == "x" then Variable[Ind](K.Identifier("x", typ.id.no+1)) else Variable[Ind]("x")
    exists(v, v ∈ typ)
/*
  def getTypes(t: Expr[Ind]): Set[Expr[Ind]] = t match 
    case v: Variable[Ind] => Set()
    case tc: TypedConstant => Set(tc.typ)
    case #@[Ind >>: Ind, Ind](#@[Ind, (Ind >>: Ind) >>: Ind](`abs`, base), Abs(v, b)) => 
      getTypes(b) + base
    case App(App(`app`, func), arg) => 
      getTypes(func) ++ getTypes(arg)
    case Multiapp(func, args: List[Expr[Ind]] @unchecked) => 
      args.toSet
    case _ => throw new IllegalArgumentException("computeTypes only support fully typed terms. " + t + " is not fully typed.")
*/   

  def computeType(t: Expr[Ind], context: TypingContext): Typ = 
    val r = t match 
      case v: Variable[Ind] => 
        context.getOrElse(v, throw new IllegalArgumentException(s"Variable $v not found in typing context"))
      case tc: TypedConstant => tc.typ
      case #@[Ind >>: Ind, Ind](#@[Ind, (Ind >>: Ind) >>: Ind](`abs`, base), Abs(v, b)) => 
        base ->: computeType(b, context.updated(v, base))
      case App(App(`app`, func), arg) => 
        computeType(func, context) match 
          case dom ->: codom => 
            val argType = computeType(arg, context)
            if isSame(argType, dom) then codom
            else 
              throw new IllegalArgumentException("In application " + t + ", argument " + arg + " has type " + argType + " instead of expected " + dom + ".")
          case funcType => throw new IllegalArgumentException("In application " + t + ", function " + func + " expected to have function type A ->: B, but has type " + funcType + ". ")
      case Multiapp(func, args: List[Expr[Ind]] @unchecked) => 
        func match
          case tcf: TypedConstantFunctional[?] =>
            if tcf.arity != args.size then 
              throw new IllegalArgumentException("computeType can only handle fully applied functions. Function " + tcf + " has arity " + tcf.arity + " but was applied to " + args.size + " arguments.")
            if args.zip(tcf.typ.inTyp).forall((arg, inType) => inType match
              case Some(value) => 
                val argType = computeType(arg, context)
                lisa.utils.fol.FOL.isSame(optype(inType, arg), (arg is argType))
              case None => true
            ) then
              val subst = (tcf.typ.args zip args).map((v, a) => (v := a))
              tcf.typ.outTyp.substitute(subst*)
            else
              val argsTypes = args.map(arg =>
                computeType(arg, context)
              )
              throw new IllegalArgumentException("Function " + tcf + " has type " + tcf.typ + " but was applied to arguments " + args + " of types " + argsTypes + ".")
          case _ => throw new IllegalArgumentException("computeType can only handle typed constant functionals. " + func + " is not a typed constant functional.")
      case _ => throw new IllegalArgumentException("computeTypes only support fully typed terms. " + t + " is not fully typed.")
    r


  def computeContextOfFormulas(formulas: Set[Expr[Prop]], known: Set[Variable[Ind]] = Set()): (Set[TypeAssign[Variable[Ind]]] ) = 
    formulas.collect {
      case TypeAssign(v: Variable[Ind], typ) if !known.contains(v) => TypeAssign(v, typ)
    }

  def contextToMap(typeAssigns: Set[TypeAssign[Variable[Ind]]]): Map[Variable[Ind], Typ] =
    typeAssigns.map(ta => ta.vari -> ta.typ).toMap


  class HOLSequent(
    val premises: Set[Expr[Ind]],
    val conclusion: Expr[Ind],
    val typeAssigns: Set[TypeAssign[Variable[Ind]]],
    val typeVarsNonEmpty: Set[Expr[Prop]]
    ) extends F.Sequent(premises.map(_ === One) ++ typeAssigns, Set(conclusion === One)) {
      
      infix def +<<(t: Expr[Ind]): HOLSequent = HOLSequent(this.premises + t, conclusion, typeAssigns)
      infix def -<<(t: Expr[Ind]): HOLSequent = HOLSequent(this.premises - t, conclusion, typeAssigns)

      override infix def +<<(f: Expr[Prop]): F.Sequent = 
        f match 
          case ===(t, One) => +<<(t)
          case ===(One, t) => +<<(t)
          case TypeAssign(v: Variable[Ind], typ) => new HOLSequent(premises, conclusion, typeAssigns + TypeAssign(v, typ), typeVarsNonEmpty)
          case _ => super.+<<(f)
      override infix def -<<(f: Expr[Prop]): F.Sequent = 
        f match 
          case ===(t, One) => -<<(t)
          case ===(One, t) => -<<(t)
          case TypeAssign(v: Variable[Ind], typ) => new HOLSequent(premises, conclusion, typeAssigns - TypeAssign(v, typ), typeVarsNonEmpty)
          case _ => super.-<<(f)

      infix def ++<<(s1: HOLSequent): HOLSequent = HOLSequent(this.premises ++ s1.premises, conclusion, typeAssigns ++ s1.typeAssigns)
      infix def --<<(s1: HOLSequent): HOLSequent = HOLSequent(this.premises -- s1.premises, conclusion, typeAssigns -- s1.typeAssigns)

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

    def apply(premises: Set[Expr[Ind]], conclusion: Expr[Ind], typeAssigns: Set[TypeAssign[Variable[Ind]]] = Set.empty, typeVarsNonEmpty: Set[Expr[Prop]] = Set.empty): HOLSequent = {
      new HOLSequent(premises, conclusion, typeAssigns, typeVarsNonEmpty)
    }

    def fromFOLSequent(s: F.Sequent): HOLSequent = 
      if s.isInstanceOf[HOLSequent] then 
        return s.asInstanceOf[HOLSequent]
      if s.right.size != 1 then 
        throw new IllegalArgumentException("Sequent in HOL must have exactly one conclusion.")
      val r = s.right.head
      r match 
        case eqOne(t) => 
          var vartypes = Set.empty[TypeAssign[Variable[Ind]]]
          var typeVarsNonEmpty = Set.empty[Expr[Prop]]
          var prems = Set.empty[Expr[Ind]]
          s.left.foreach {a => a match 
            case TypeAssign(v: Variable[Ind], typ)  => vartypes += TypeAssign(v, typ)
            case exists(v1: Variable[Ind], v2 ∈ (typ: Variable[Ind])) if v1 == v2 => typeVarsNonEmpty += a
            case eqOne(t) => prems += t
            case _ => throw new IllegalArgumentException("Premises must be of the form t === One or be a type assignment. violating: " + a)
          }
          new HOLSequent(prems, t, vartypes, typeVarsNonEmpty)
        case _ => 
          throw new IllegalArgumentException("Conclusion must be of the form t === One.")

    def unapply(s: F.Sequent): Option[(Set[Expr[Ind]], Expr[Ind])] = 
      if s.isInstanceOf[HOLSequent] then 
        val s1 = s.asInstanceOf[HOLSequent]
        Some((s1.premises, s1.conclusion))
      else 
        try {
          val s1 = fromFOLSequent(s)
          Some((s1.premises, s1.conclusion))
        }
        catch
          case e: IllegalArgumentException => 
            println(e.getMessage())
            return None
  }




  opaque type TypedForall <: Expr[Prop] & {val v: Variable[Ind]; val prop: Expr[Prop]} = TypedForallConcrete

  private class TypedForallConcrete( val v: Variable[Ind], val vType: Typ, val prop: Expr[Prop] ) extends App(forall, λ(v, (v is vType) ==> prop)) {
    override def toString = s"∀$v : $vType. $prop"
  }

  object TypedForall {
    def apply(v: Variable[Ind], vType: Typ, prop: Expr[Prop]): TypedForall = new TypedForallConcrete(v, vType, prop)
  }

  def tforall(v: Variable[Ind], vType: Typ, prop: Expr[Prop]): TypedForall = TypedForall(v, vType, prop)
  def tforall(v: TypeAssign[Variable[Ind]], prop: Expr[Prop]): TypedForall = TypedForall(v.vari, v.typ, prop)
  inline given Conversion[TypedForall, Expr[Prop]] with
    def apply(tf: TypedForall): Expr[Prop] = tf








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
    val x = variable[Ind]
    val y = variable[Ind]
    val eqDefin = Axiom(((x::A) /\ (y::A)) ==> ((x =:= y)(using Map(x -> A, y -> A))===One) <=> (x===y))
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
    def =:=(t2:Expr[Ind])(using context: TypingContext): Expr[Ind] = 
      val A = computeType(t1, context)
      val B = computeType(t2, context)
      if isSame(A, B) then
        holeq(A)*(t1)*(t2) 
      else 
        throw new Exception("in expression " + t1 + " =:= " + t2 + " the types " + A + " of left-hand side and " + B + " of right-hand side do not match.")
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
          val ax = assume(exists(x, x ∈ v))
          have(ax.statement) by Restate
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

  def TypingTheorem(using om: lisa.utils.prooflib.OutputManager, name: sourcecode.FullName)(assignment: Expr[Prop])(using context: TypingContext): THM = 
    val contextAssigns = context.map((v, typ) => v :: typ).toSet
    Theorem(using om, name)(contextAssigns |- assignment) {
      have(thesis) by Typecheck.prove
    }


  object HOLProofType extends ProofTactic {
    def apply2(using proof: SetTheoryLibrary.Proof)(t:Expr[Ind], context: TypingContext): proof.ProofTacticJudgement =
      val contextAssigns: Set[Expr[Prop]] = context.map((v, typ) => v is typ).toSet
      Typecheck.inferProof(contextAssigns, t)

    def apply(using proof: SetTheoryLibrary.Proof)(t:Expr[Ind], context: TypingContext): proof.ProofTacticJudgement = TacticSubproof {
      given SetTheoryLibrary.type = SetTheoryLibrary
      t match 
        case tc: TypedConstant => 
          have(tc.justif.statement) by Weakening(tc.justif)
        case _ => 
          have(apply2(t, context))
    }
  }


  given termToSetConv[T <: Expr[Ind]]: FormulaSetConverter[T] = t => Set(eqOne(t))
  given setTermToSetConv[T <: Iterable[Expr[Ind]]]: FormulaSetConverter[T] = _.map(eqOne(_)).toSet


  given Conversion[Expr[Ind], HOLSequent] = HOLSequent(Set(), _)


end VarsAndFunctions