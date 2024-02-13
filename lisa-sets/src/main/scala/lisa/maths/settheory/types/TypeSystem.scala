package lisa.maths.settheory.types
import scala.compiletime.ops.int.-
import lisa.prooflib.ProofTacticLib.ProofTactic
import lisa.fol.FOL
import lisa.automation.Tautology
import lisa.utils.unification.UnificationUtils.matchTerm
object Test extends lisa.Main {
	import TypeSystem.*

	def typedVariable[Type : IsClass](using name: sourcecode.Name): TypedVariable[Type] = TypedVariable[Type](name.value)

	val top_is_true = Theorem( top) {
		have(thesis) by Restate
	}

	val ℕ = TypedConstant[top.type]("ℕ", top_is_true)
	addSymbol(ℕ)
	type ℕ = ℕ.asType

	val n: ℕ = typedVariable
	val f: ℕ |=> (ℕ |=> ℕ) = typedVariable
	val g: (ℕ |=> ℕ) |=> (ℕ |=> ℕ) = typedVariable

	val testThm = Theorem((typing(n), typing(f), typing(g)) |- g(g(f(n))) ∈ (ℕ |=> ℕ)) {
		have(TypingJudgement.typecheck( g(g(f(n))) ))
	}


}



object TypeSystem {
	import lisa.fol.FOL.{*, given}
	import lisa.prooflib.BasicStepTactic.* 
	import lisa.prooflib.SimpleDeducedSteps.*
	import lisa.SetTheoryLibrary.{given, *}

	val x = variable
	val y = variable
	val z = variable






	given[A] : Conversion[TypedTerm[A], Term] = _.asTerm


	trait IsClass[A] {
		def predicate: Term**1 |-> Formula
	}
	def predicateOf[A](using c: IsClass[A]): Term**1 |-> Formula = c.predicate

	trait IsSmallClass[A] extends IsClass[A]{
		def set: Term
		def predicate: Term**1 |-> Formula = lambda(x, in(x, set))
	}
	object IsSmallClass:
		def apply[T](using c: IsClass[T]) = c

	given given_setSmallClass[C <: Term & Singleton: ValueOf]: IsSmallClass[C] with {
		def set = valueOf[C]
	}

	def setOfClass[A](using c: IsSmallClass[A]): Term = c.set


	given [C <: ConstantPredicateLabel[1] & Singleton: ValueOf]: IsClass[C] with {
		val predicate = valueOf[C]
	}



	given IsClass[top.type] with {
		val predicate = lambda(x, top)
	}

	
	given IsClass[bot.type] with {
		val predicate = lambda(x, bot)
	}
	type bot = TypedTerm[bot.type]


	type top = TypedTerm[top.type]

	/*
	given given_setSmallClass[C <: Term & Singleton: ValueOf]: IsSmallClass[C] with {
			val set = valueOf[C]
	}*/

	trait ClassFunction[A: IsClass, B: IsClass] {
		def application(a: TypedTerm[A]): TypedTerm[B]
	}

	val functionSpace: ConstantFunctionLabel[2] = ConstantFunctionLabel("functionSpace", 2)
	extension (t:Term) {
		def |=>(o:Term): Term = functionSpace(t, o)
	}
	val app: ConstantFunctionLabel[2] = ConstantFunctionLabel("app", 2)
	addSymbol(functionSpace)
	addSymbol(app)


	given given_funcSpaceIsSmallClass[A: IsSmallClass, B: IsSmallClass]: IsSmallClass[ClassFunction[A, B]] with {
		val set = functionSpace(setOfClass[A], setOfClass[B])
	}

	infix type |=>[A<: TypedTerm[?], B<: TypedTerm[?]] = A match {
		case TypedTerm[i] => B match {
			case TypedTerm[j] => TypedTerm[ClassFunction[i, j]]
			case _ => Nothing
		}
		case _ => Nothing
}


	type DeconstructTT[T <: TypedTerm[?]] = T match {
		case TypedTerm[t] => t
		case _ => Nothing
	}

	def setOf[TT <: TypedTerm[_]](using c: IsSmallClass[DeconstructTT[TT]]): Term = c.set








	sealed trait TypedTerm[T](using val ev: IsClass[T]) extends LisaObject[TypedTerm[T]] {
		this: Term  =>

		val typeEvidence: IsClass[Type] = ev

		type Type = T

		type asType = TypedTerm[this.type]
		
		def asTerm: Term = this

		val proofCache = collection.mutable.Map[Proof, Proof#Fact]()

		//protected def noCacheGetUntypedJudgement(proof: Proof): proof.Fact

		//def getTypeJudgement(proof:Proof): proof.Fact = proofCache.getOrElseUpdate(proof, noCacheGetUntypedJudgement(proof)).asInstanceOf[proof.Fact] //can be redundant because does not look in superproofs
	}


	extension [A: IsSmallClass, B: IsSmallClass] (t: TypedTerm[ClassFunction[A, B]])
		def apply(a: TypedTerm[A]): TypedTerm[B] = TypedAppliedFunction(t, a)

	
	class TypedVariable[Type : IsClass](id: Identifier) extends Variable(id) with TypedTerm[Type] with LisaObject[TypedVariable[Type]] {
		val formula = predicateOf[Type](this)
		/*protected def noCacheGetUntypedJudgement(proof: lisa.SetTheoryLibrary.Proof): proof.Fact = 
			given proof.type = proof
			have(TacticSubproof {
				have(predicateOf[Type](this) |- predicateOf[Type](this)) by Restate
			})*/


		override def substituteUnsafe(map: Map[lisa.fol.FOL.SchematicLabel[?], lisa.fol.FOL.LisaObject[?]]): TypedVariable[Type] = this
	}
	object TypedVariable {
		def unapply[Type: IsClass](t: TypedVariable[Type]): Some[Identifier] = Some(t.id)
		
	}

	class TypedConstant[Type : IsClass]
		(id: Identifier, val justif: JUSTIFICATION) extends Constant(id) with TypedTerm[Type] with LisaObject[TypedConstant[Type]]  {
		val formula = predicateOf[Type](this)
		assert(justif.statement.left.isEmpty && (justif.statement.right.head == formula))
		//protected def noCacheGetUntypedJudgement(proof: lisa.SetTheoryLibrary.Proof): proof.Fact = justif
		//override def getUntypedJudgement(proof: lisa.SetTheoryLibrary.Proof): proof.Fact = justif

		override def substituteUnsafe(map: Map[lisa.fol.FOL.SchematicLabel[?], lisa.fol.FOL.LisaObject[?]]): TypedConstant[Type] = this

	}

	// Function Labels


	sealed trait TypedFunctional extends LisaObject[TypedFunctional] {
		this: FunctionLabel[?] =>
		
		def applyUnsafe2(args: Seq[Term]): TypedTerm[?] = ???
		def asLabel: FunctionLabel[?] = this
	}

	trait TypedFunctional1[-In: IsClass, +Out<:LisaObject[Out]:IsClass] extends TypedFunctional/* with (In |-> Out)*/  {
		this: FunctionLabel[1] =>
		val formula = forall(x, predicateOf[In](x) ==> predicateOf[Out](this(x))) //TODO fresh x but predicateOf is supposed to be free variables free.
		//def getUntypedJudgement(proof: lisa.SetTheoryLibrary.Proof): proof.Fact // justification of |- formula

		//def applyUnsafe(arg: In): Out = ???

	}

	trait TypedFunctional2[-In1: IsClass, -In2: IsClass, +Out<:LisaObject[Out]:IsClass] extends TypedFunctional/* with ((In1, In2) |-> Out)*/  {
		this: FunctionLabel[2] =>
		val formula = forall(x, forall(y, (predicateOf[In1](x) /\ predicateOf[In2](y)) ==> predicateOf[Out](this(x, y))))
		//def getUntypedJudgement(proof: lisa.SetTheoryLibrary.Proof): proof.Fact

		def applyUnsafe(arg1: In1, arg2: In2): Out = ???

	}

	

	trait TypedFunctional3[-In1: IsClass, -In2: IsClass, -In3: IsClass, +Out<:LisaObject[Out]:IsClass] extends TypedFunctional /* with ((In1, In2, In3) |-> Out)*/ {
		this: FunctionLabel[3] =>
		val formula = forall(x, forall(y, forall(z, (predicateOf[In1](x) /\ predicateOf[In2](y) /\ predicateOf[In3](z)) ==> predicateOf[Out](this(x, y, z)))))
		//def getUntypedJudgement(proof: lisa.SetTheoryLibrary.Proof): proof.Fact

		def applyUnsafe(arg1: In1, arg2: In2, arg3: In3): Out = ???

	}

	class TypedConstantFunctional1[-In: IsClass, +Out<:LisaObject[Out]:IsClass]
		(id: Identifier, val justif: JUSTIFICATION) extends ConstantFunctionLabel[1](id, 1) with TypedFunctional1[In, Out] with LisaObject[TypedConstantFunctional1[In, Out]] {
		assert(justif.statement.left.isEmpty && justif.statement.right == formula)
		//def getUntypedJudgement(proof: lisa.SetTheoryLibrary.Proof): proof.Fact = justif
		
		override def substituteUnsafe(map: Map[lisa.fol.FOL.SchematicLabel[?], lisa.fol.FOL.LisaObject[?]]): TypedConstantFunctional1[In, Out] = this

		//def applyUnsafe(arg: In): Out & Term = ???
	}

	
	class TypedConstantFunctional2[-In1: IsClass, -In2: IsClass, +Out<:LisaObject[Out]:IsClass]
		(id: Identifier, val justif: JUSTIFICATION) extends ConstantFunctionLabel[2](id, 2) with TypedFunctional2[In1, In2, Out] with LisaObject[TypedConstantFunctional2[In1, In2, Out]] {
		assert(justif.statement.left.isEmpty && justif.statement.right == formula)
		//def getUntypedJudgement(proof: lisa.SetTheoryLibrary.Proof): proof.Fact = justif
		
		override def substituteUnsafe(map: Map[lisa.fol.FOL.SchematicLabel[?], lisa.fol.FOL.LisaObject[?]]): TypedConstantFunctional2[In1, In2, Out] = this
	}

	class TypedConstantFunctional3[-In1: IsClass, -In2: IsClass, -In3: IsClass, +Out<:LisaObject[Out]:IsClass]
		(id: Identifier, val justif: JUSTIFICATION) extends ConstantFunctionLabel[3](id, 3) with TypedFunctional3[In1, In2, In3, Out] with LisaObject[TypedConstantFunctional3[In1, In2, In3, Out]] {
		assert(justif.statement.left.isEmpty && justif.statement.right == formula)
		//def getUntypedJudgement(proof: lisa.SetTheoryLibrary.Proof): proof.Fact = justif
		
		override def substituteUnsafe(map: Map[lisa.fol.FOL.SchematicLabel[?], lisa.fol.FOL.LisaObject[?]]): TypedConstantFunctional3[In1, In2, In3, Out] = this
	}

	/*
	class TypedSchematicFunctional1[-In: IsClass, +Out<:LisaObject[Out]:IsClass]
			(id: Identifier, val justif: JUSTIFICATION) extends SchematicFunctionLabel[1](id, 1) with TypedFunctional1[In, Out] {
			def getTypeJudgement(proof: lisa.SetTheoryLibrary.Proof): proof.Fact = ???
			
			override def substituteUnsafe(map: Map[lisa.fol.FOL.SchematicLabel[?], lisa.fol.FOL.LisaObject[?]]): Term**1 |-> Term  = 
					map.get(this) match {
							case Some(subst) =>
									subst match {
											case s: (Term**1 |-> Term) => s
											case _ => throw SubstitutionException()
									}
							case None => this
					}
	}

	class TypedSchematicFunctional2[-In1: IsClass, -In2: IsClass, +Out<:LisaObject[Out]:IsClass]
			(id: Identifier, val justif: JUSTIFICATION) extends SchematicFunctionLabel[2](id, 2) with TypedFunctional2[In1, In2, Out] {
			def getTypeJudgement(proof: lisa.SetTheoryLibrary.Proof): proof.Fact = ???
			
			override def substituteUnsafe(map: Map[lisa.fol.FOL.SchematicLabel[?], lisa.fol.FOL.LisaObject[?]]): Term**2 |-> Term  = 
					map.get(this) match {
							case Some(subst) =>
									subst match {
											case s: (Term**2 |-> Term) => s
											case _ => throw SubstitutionException()
									}
							case None => this
					}
	}

	class TypedSchematicFunctional3[-In1: IsClass, -In2: IsClass, -In3: IsClass, +Out<:LisaObject[Out]:IsClass]
			(id: Identifier, val justif: JUSTIFICATION) extends SchematicFunctionLabel[3](id, 3) with TypedFunctional3[In1, In2, In3, Out] {
			def getTypeJudgement(proof: lisa.SetTheoryLibrary.Proof): proof.Fact = ???
			
			override def substituteUnsafe(map: Map[lisa.fol.FOL.SchematicLabel[?], lisa.fol.FOL.LisaObject[?]]): Term**3 |-> Term  = 
					map.get(this) match {
							case Some(subst) =>
									subst match {
											case s: (Term**3 |-> Term) => s
											case _ => throw SubstitutionException()
									}
							case None => this
					}
	}
*/
	
	def cast[T: IsClass](t: Term, justif:JUSTIFICATION): TypedTerm[T] = ??? //Todo

	private class CastAppliedFunctional[Type: IsClass](label: FunctionLabel[?],args: Seq[Term], val justif: JUSTIFICATION) extends AppliedFunction(label, args) with TypedTerm[Type] with LisaObject[TypedTerm[Type]] {
		val formula = predicateOf[Type](this)
		assert(justif.statement.right == formula)
		protected def noCacheGetUntypedJudgement(proof: lisa.SetTheoryLibrary.Proof): proof.Fact = justif

		//label.substituteUnsafe(map).applyUnsafe(args.map[Term]((x: Term) => x.substituteUnsafe(map)))
		override def substituteUnsafe(map: Map[lisa.fol.FOL.SchematicLabel[?], lisa.fol.FOL.LisaObject[?]]): TypedTerm[Type] & Term = cast[Type](label.substituteUnsafe(map).applyUnsafe(args.map[Term]((x: Term) => x.substituteUnsafe(map))), justif).asInstanceOf //TODO justif
	}

	class TypedAppliedFunctional[Type:IsClass](label: TypedFunctional, args: Seq[TypedTerm[?]]) extends AppliedFunction(label.asLabel, args.asInstanceOf[Seq[Term]]) with TypedTerm[Type] with LisaObject[TypedTerm[Type]]  {
		val formula = predicateOf[Type](this)
		protected def noCacheGetUntypedJudgement(proof: lisa.SetTheoryLibrary.Proof): proof.Fact = ???

		override def substituteUnsafe(map: Map[lisa.fol.FOL.SchematicLabel[?], lisa.fol.FOL.LisaObject[?]]): TypedTerm[Type] & Term = 
			val newlab: TypedFunctional = label.substituteUnsafe(map)
			val newargs = args.map[TypedTerm[?]]((x: TypedTerm[?]) => x.substituteUnsafe(map))
			newlab.applyUnsafe2(newargs.asInstanceOf[Seq[Term]]).asInstanceOf[TypedTerm[Type] & Term] //first asInstanceOf is alwys safe, second is safe because it's a cast from TypedTerm[?] to TypedTerm[Type] & Type, and by assumption label has type of Type(args) => Type
	}

	class TypedAppliedFunction[A:IsSmallClass, B:IsSmallClass](val func: TypedTerm[ClassFunction[A, B]], val arg: TypedTerm[A]) extends AppliedFunction(app, Seq(func.asTerm, arg.asTerm)) with TypedTerm[B] with LisaObject[TypedAppliedFunction[A, B]] {
		type In = A
		type Out = B
		override val typeEvidence: IsSmallClass[Type] = summon[IsSmallClass[B]]
		val typeInEvidence: IsSmallClass[A] = summon[IsSmallClass[A]]
		override def substituteUnsafe(map: Map[FOL.SchematicLabel[?], FOL.LisaObject[?]]): TypedAppliedFunction[In, Out] = 
			TypedAppliedFunction(func.substituteUnsafe(map).asInstanceOf[TypedTerm[ClassFunction[In, Out]]], arg.substituteUnsafe(map).asInstanceOf[TypedTerm[In]])

	}
	object TypedAppliedFunction {
		def unapply[A, B](t: TypedAppliedFunction[A, B]): Option[(TypedTerm[ClassFunction[A, B]], TypedTerm[A])] = 
			Some((t.func, t.arg))
		
		def test[A:IsSmallClass, B:IsSmallClass](t: TypedAppliedFunction[A, B]): Some[(TypedTerm[ClassFunction[A, B]], TypedTerm[A])] = Some((t.func, t.arg))
	}

	

	/**
		* A type assumption is a pair of a variable and a type.
		* It is also a formula, equal to the type applied to the variable.
		*/
	trait TypeAssumption[A : IsClass]{
		this: Formula =>
		val t: Term
		type Type = A
		val predicate = predicateOf[Type]
		val asFormula: Formula = this

	}

	object TypeAssumption {
		/**
			* A type assumption is a pair of a variable and a type.
			* It is also a formula, equal to the type applied to the variable.
			*/
		def apply[Type : IsClass](t: Term): TypeAssumption[Type] = 
			val form = predicateOf[Type](t)
			form match
				case f: VariableFormula => 
					throw new IllegalArgumentException("Class formula cannot be a variable formula, as we require a type to have no free variable.")
				case f: ConstantFormula => new TypeAssumptionConstant(t, f)
				case f: AppliedPredicate => new TypeAssumptionPredicate(t, f)
				case f: AppliedConnector => new TypeAssumptionConnector(t, f)
				case f: BinderFormula => new TypeAssumptionBinder(t, f)
	}

	def typing[Type : IsClass](t: TypedTerm[Type]): TypeAssumption[Type] & Formula = TypeAssumption.apply(t.asTerm).asInstanceOf

	private class TypeAssumptionConstant[Type : IsClass](val t: Term,  formula: ConstantFormula) extends ConstantFormula(formula.id) with TypeAssumption[Type]
	private class TypeAssumptionPredicate[Type : IsClass](val t: Term, formula: AppliedPredicate) extends AppliedPredicate(formula.label, formula.args) with TypeAssumption[Type]
	private class TypeAssumptionConnector[Type : IsClass](val t: Term,  formula: AppliedConnector) extends AppliedConnector(formula.label, formula.args) with TypeAssumption[Type]
	private class TypeAssumptionBinder[Type : IsClass](val t: Term,  formula: BinderFormula) extends BinderFormula(formula.f, formula.bound, formula.body) with TypeAssumption[Type]
	


	val f = variable
	val A = variable
	val B = variable
	val funcspaceAxiom = Axiom(f ∈ functionSpace(A, B) ==> (x ∈ A ==> app(f, x) ∈ B))

	object TypingJudgement extends ProofTactic {

		def typecheck[Type: IsClass](using proof: setLibrary.Proof)(t: TypedTerm[Type]) : proof.ProofTacticJudgement = TacticSubproof {t match
			case tv: TypedVariable[Type] =>
				have(TypeAssumption[Type](tv).asFormula |- predicateOf[Type](tv)) by Restate
			case tc: TypedConstant[Type] =>
				have(tc.justif)

			case caf: CastAppliedFunctional[Type] =>
				have(caf.justif)

			case taf: TypedAppliedFunctional[Type] =>
				???
			
			case t @ TypedAppliedFunction(fun, arg) =>
				val funType = have(typecheck[fun.Type](fun)(using fun.typeEvidence)) // ... |- f ∈ setOf[f.Type]  ==== |- f ∈ setOf[ClassFunction[A, B]] which is f ∈ functionSpace(setOf[A], setOf[Type])
				val argType = have(typecheck[arg.Type](arg)(using arg.typeEvidence)) // ... |- arg ∈ setOf[A]
				val funcProp = funcspaceAxiom of (f := fun.asTerm, A := (setOfClass[t.In](using t.typeInEvidence)), B := setOfClass[t.Type](using t.typeEvidence), x := arg.asTerm)


				have((funType.bot.left ++ argType.bot.left) |- predicateOf[Type](app(fun.asTerm, arg.asTerm))) by Tautology.from(
					funcspaceAxiom of (f := fun.asTerm, A := (setOfClass[t.In](using t.typeInEvidence)), B := setOfClass[t.Type](using t.typeEvidence), x := arg.asTerm),
					funType,
					argType
				)
		}
		
	}



	//def variable[Type : IsClass](using name: sourcecode.Name): TypedVariable[Type] = TypedVariable[Type](name.value)
	//def typedVariable[Type : IsClass](using name: sourcecode.Name): TypedVariable[Type] = TypedVariable[Type](name.value)



}