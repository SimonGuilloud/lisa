package lisa.maths.settheory.types
import scala.compiletime.ops.int.-

object TypeSystem {
    import lisa.fol.FOL.{*, given}
    import lisa.SetTheoryLibrary.*

    val x = variable
    val y = variable
    val z = variable

    def main(args: Array[String]): Unit = {
        val ℕ: TypedConstant[top] = TypedConstant("ℕ", extensionalityAxiom)
        type ℕ = ℕ.asType
        assert(setOf[ℕ ==> ℕ] == functionSpace(ℕ, ℕ))

        println(setOf[ℕ ==> ℕ])


        val n: ℕ = TypedConstant("n", ???)
        val f: ℕ ==> ℕ = TypedConstant("f", ???)
        val g: (ℕ ==> ℕ) ==> (ℕ ==> ℕ) = TypedConstant("g", ???)

        f(n)
        val f2 = g(f)
        f2(n)
        //n(g)
    }



    trait IsClass[A] {
        def predicate: Term**1 |-> Formula
    }
    def predicateOf[A](using c: IsClass[A]): Term**1 |-> Formula = c.predicate

    trait IsSmallClass[A] extends IsClass[A]{
        def set: Term
        def predicate: Term**1 |-> Formula = lambda(x, in(x, set))
    }
    def setOfClass[A](using c: IsSmallClass[A]): Term = c.set

    object IsSmallClass:
        def apply[T](using c: IsClass[T]) = c

    given given_setSmallClass[C <: Term & Singleton: ValueOf]: IsSmallClass[C] with {
        def set = valueOf[C]
    }



    given [C <: ConstantPredicateLabel[1] & Singleton: ValueOf]: IsClass[C] with {
        val predicate = valueOf[C]
    }



    given IsClass[top.type] with {
            val predicate = lambda(x, top)
        }
    type top = top.type

    /*
    given given_setSmallClass[C <: Term & Singleton: ValueOf]: IsSmallClass[C] with {
        val set = valueOf[C]
    }*/

    trait ClassFunction[A: IsClass, B: IsClass] {
        def application(a: TypedTerm[A]): TypedTerm[B]
    }

    val functionSpace: ConstantFunctionLabel[2] = ConstantFunctionLabel("functionSpace", 2)


    given given_funcSpaceIsSmallClass[A: IsSmallClass, B: IsSmallClass]: IsSmallClass[ClassFunction[A, B]] with {
        val set = functionSpace(setOfClass[A], setOfClass[B])
    }

    infix type ==>[A<: TypedTerm[?], B<: TypedTerm[?]] = A match {
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








    trait TypedTerm[T : IsClass] extends LisaObject[TypedTerm[T]] {
        this: Term  =>

        type Type = T

        type asType = TypedTerm[this.type]
        
        def asTerm: Term = this

        def getTypeJudgement(proof:Proof): proof.Fact //proof of predicateOf[Type](this)
    }


    extension [A: IsClass, B: IsClass] (t: TypedTerm[ClassFunction[A, B]])
        def apply(a: TypedTerm[A]): TypedTerm[B] = ??? // TypedAppliedFunction(t, a)

    

    class TypedConstant[Type : IsClass]
        (id: Identifier, val justif: JUSTIFICATION) extends Constant(id) with TypedTerm[Type] with LisaObject[TypedConstant[Type]]  {
        val formula = predicateOf[Type](this)
        def getTypeJudgement(proof: lisa.SetTheoryLibrary.Proof): proof.Fact = ???

        override def substituteUnsafe(map: Map[lisa.fol.FOL.SchematicLabel[?], lisa.fol.FOL.LisaObject[?]]): TypedConstant[Type] = this

    }

    // Function Labels


    trait TypedFunctional extends LisaObject[TypedFunctional] {
        this: FunctionLabel[?] =>
        def applyUnsafe2(args: Seq[Term]): TypedTerm[?] = ???
        def asLabel: FunctionLabel[?] = this
    }

    trait TypedFunctional1[-In: IsClass, +Out<:LisaObject[Out]:IsClass] extends TypedFunctional/* with (In |-> Out)*/  {
        this: FunctionLabel[1] =>
        val formula = forall(x, predicateOf[In](x) ==> predicateOf[Out](this(x))) //TODO fresh x but predicateOf is supposed to be free variables free.
        def getTypeJudgement(proof: lisa.SetTheoryLibrary.Proof): proof.Fact

        //def applyUnsafe(arg: In): Out = ???

    }

    trait TypedFunctional2[-In1: IsClass, -In2: IsClass, +Out<:LisaObject[Out]:IsClass] extends TypedFunctional/* with ((In1, In2) |-> Out)*/  {
        this: FunctionLabel[2] =>
        val formula = forall(x, forall(y, (predicateOf[In1](x) /\ predicateOf[In2](y)) ==> predicateOf[Out](this(x, y))))
        def getTypeJudgement(proof: lisa.SetTheoryLibrary.Proof): proof.Fact

        def applyUnsafe(arg1: In1, arg2: In2): Out = ???

    }

    

    trait TypedFunctional3[-In1: IsClass, -In2: IsClass, -In3: IsClass, +Out<:LisaObject[Out]:IsClass] extends TypedFunctional /* with ((In1, In2, In3) |-> Out)*/ {
        this: FunctionLabel[3] =>
        val formula = forall(x, forall(y, forall(z, (predicateOf[In1](x) /\ predicateOf[In2](y) /\ predicateOf[In3](z)) ==> predicateOf[Out](this(x, y, z)))))
        def getTypeJudgement(proof: lisa.SetTheoryLibrary.Proof): proof.Fact

        def applyUnsafe(arg1: In1, arg2: In2, arg3: In3): Out = ???

    }

    class TypedConstantFunctional1[-In: IsClass, +Out<:LisaObject[Out]:IsClass]
        (id: Identifier, val justif: JUSTIFICATION) extends ConstantFunctionLabel[1](id, 1) with TypedFunctional1[In, Out] with LisaObject[TypedConstantFunctional1[In, Out]] {
        def getTypeJudgement(proof: lisa.SetTheoryLibrary.Proof): proof.Fact = ???
        
        override def substituteUnsafe(map: Map[lisa.fol.FOL.SchematicLabel[?], lisa.fol.FOL.LisaObject[?]]): TypedConstantFunctional1[In, Out] = this

        //def applyUnsafe(arg: In): Out & Term = ???
    }

    
    class TypedConstantFunctional2[-In1: IsClass, -In2: IsClass, +Out<:LisaObject[Out]:IsClass]
        (id: Identifier, val justif: JUSTIFICATION) extends ConstantFunctionLabel[2](id, 2) with TypedFunctional2[In1, In2, Out] with LisaObject[TypedConstantFunctional2[In1, In2, Out]] {
        def getTypeJudgement(proof: lisa.SetTheoryLibrary.Proof): proof.Fact = ???
        
        override def substituteUnsafe(map: Map[lisa.fol.FOL.SchematicLabel[?], lisa.fol.FOL.LisaObject[?]]): TypedConstantFunctional2[In1, In2, Out] = this
    }

    class TypedConstantFunctional3[-In1: IsClass, -In2: IsClass, -In3: IsClass, +Out<:LisaObject[Out]:IsClass]
        (id: Identifier, val justif: JUSTIFICATION) extends ConstantFunctionLabel[3](id, 3) with TypedFunctional3[In1, In2, In3, Out] with LisaObject[TypedConstantFunctional3[In1, In2, In3, Out]] {
        def getTypeJudgement(proof: lisa.SetTheoryLibrary.Proof): proof.Fact = ???
        
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
        def getTypeJudgement(proof: lisa.SetTheoryLibrary.Proof): proof.Fact = justif

        //label.substituteUnsafe(map).applyUnsafe(args.map[Term]((x: Term) => x.substituteUnsafe(map)))
        override def substituteUnsafe(map: Map[lisa.fol.FOL.SchematicLabel[?], lisa.fol.FOL.LisaObject[?]]): TypedTerm[Type] & Term = cast[Type](label.substituteUnsafe(map).applyUnsafe(args.map[Term]((x: Term) => x.substituteUnsafe(map))), justif).asInstanceOf //TODO justif
    }

    class TypedAppliedFunction[Type:IsClass](label: TypedFunctional, args: Seq[TypedTerm[?]]) extends AppliedFunction(label.asLabel, args.asInstanceOf[Seq[Term]]) with TypedTerm[Type] with LisaObject[TypedTerm[Type]]  {
        val formula = predicateOf[Type](this)
        def getTypeJudgement(proof: lisa.SetTheoryLibrary.Proof): proof.Fact = ???

        override def substituteUnsafe(map: Map[lisa.fol.FOL.SchematicLabel[?], lisa.fol.FOL.LisaObject[?]]): TypedTerm[Type] & Term = 
            val newlab: TypedFunctional = label.substituteUnsafe(map)
            val newargs = args.map[TypedTerm[?]]((x: TypedTerm[?]) => x.substituteUnsafe(map))
            newlab.applyUnsafe2(newargs.asInstanceOf[Seq[Term]]).asInstanceOf[TypedTerm[Type] & Term] //first asInstanceOf is alwys safe, second is safe because it's a cast from TypedTerm[?] to TypedTerm[Type] & Type, and by assumption label has type of Type(args) => Type
    }


    //private class TypedAppliedFunction[In1: IsClass, In2: IsClass, Out: IsClass](val label:

    


    
    //n(f) //does not compile


        // Define Class Assumptions as containers over a variable and a type, which is also a formula.

    /**
      * A type assumption is a pair of a variable and a type.
      * It is also a formula, equal to the type applied to the variable.
      */
    trait TypeAssumption[A <: Singleton : IsClass]{
        this: Formula =>
        val x: Variable
        type Type = A
        val predicate = predicateOf[A]
        val formula: Formula
/*
        def unapply(f: Formula): Option[(Variable, Class)] = 
            f match
                case f: TypeAssumption => Some((f.x, f.typ))
                case _ => None
                */
    }

    object TypeAssumption {
        /**
          * A type assumption is a pair of a variable and a type.
          * It is also a formula, equal to the type applied to the variable.
          */
        def apply[A <: Singleton : IsClass](x: Variable): TypeAssumption[A] = 
            val formula = predicateOf[A](x)
            formula match
                case f: VariableFormula => 
                    throw new IllegalArgumentException("Class formula cannot be a variable formula, as we require a type to have no free variable.")
                case f: ConstantFormula => new TypeAssumptionConstant(x, f)
                case f: AppliedPredicate => new TypeAssumptionPredicate(x, f)
                case f: AppliedConnector => new TypeAssumptionConnector(x, f)
                case f: BinderFormula => new TypeAssumptionBinder(x, f)
    }
    private class TypeAssumptionConstant[A <: Singleton : IsClass](val x: Variable, val formula: ConstantFormula) extends ConstantFormula(formula.id) with TypeAssumption[A]
    private class TypeAssumptionPredicate[A <: Singleton : IsClass](val x: Variable, val formula: AppliedPredicate) extends AppliedPredicate(formula.label, formula.args) with TypeAssumption[A]
    private class TypeAssumptionConnector[A <: Singleton : IsClass](val x: Variable, val formula: AppliedConnector) extends AppliedConnector(formula.label, formula.args) with TypeAssumption[A]
    private class TypeAssumptionBinder[A <: Singleton : IsClass](val x: Variable, val formula: BinderFormula) extends BinderFormula(formula.f, formula.bound, formula.body) with TypeAssumption[A]
    


/*
    trait TypedFunctional[In <: SetType & Singleton, +Out <: SetType & Singleton] extends LisaObject[TypedFunctional[In, Out]] {
        this: FunctionLabel[1] =>
        val typIn: In
        val typOut: Out

        def apply(arg: TypedTerm[In]): TypedAppliedFunction[In, Out] = ???
    }



    }

    class TypedConstantFunction[In <: SetType & Singleton, +Out <: SetType & Singleton]
        (id: Identifier, val typIn: In, val typOut: Out, val justif: JUSTIFICATION) extends ConstantFunctionLabel[1](id, 1) with  TypedFunctional[In, Out] with LisaObject[TypedConstantFunction[In, Out]] {
        
        def getTypeJudgement(proof: lisa.SetTheoryLibrary.Proof): proof.Fact = ???
        
        override def substituteUnsafe(map: Map[lisa.fol.FOL.SchematicLabel[?], lisa.fol.FOL.LisaObject[?]]): TypedConstantFunction[In, Out] = this
    }

    class TypedAppliedFunction[In <: SetType & Singleton, +Type <: SetType & Singleton]
        (label: TypedConstantFunction[In, Type], arg: TypedTerm[In], val out: Type, val typ: Type, val justif: JUSTIFICATION) extends AppliedFunction(label, Seq(arg.asTerm)) with TypedTerm[Type] with LisaObject[TypedAppliedFunction[In, Type]] {
        val formula = typ(this)
        def getTypeJudgement(proof: lisa.SetTheoryLibrary.Proof): proof.Fact = ???

        override def substituteUnsafe(map: Map[lisa.fol.FOL.SchematicLabel[?], lisa.fol.FOL.LisaObject[?]]): TypedAppliedFunction[In, Type] = label.substituteUnsafe(map).apply(arg.substituteUnsafe(map))
    }
*/



}