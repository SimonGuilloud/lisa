package lisa.maths.settheory.types


object TypeSystem {
    import lisa.fol.FOL.{*, given}
    import lisa.SetTheoryLibrary.*

    val x = variable
    val y = variable

    def main(args: Array[String]): Unit = {
        val ℕ: TypedConstant[top] = TypedConstant("ℕ", extensionalityAxiom)
        type ℕ = ℕ.asType
        assert(setOf[ℕ ==> ℕ] == functionSpace(ℕ, ℕ))

        println(setOf[ℕ ==> ℕ])
    }



  /*


    class Class(val predicate: Term**1 |-> Formula) extends (Term**1 |-> Formula) {
        require(predicate.freeSchematicLabels == Set.empty)
        type T = TypedTerm[this.type]
        def allSchematicLabels: Set[lisa.fol.FOL.SchematicLabel[?]] = predicate.allSchematicLabels
        def freeSchematicLabels: Set[lisa.fol.FOL.SchematicLabel[?]] = predicate.freeSchematicLabels
        def substituteUnsafe(map: Map[lisa.fol.FOL.SchematicLabel[?], lisa.fol.FOL.LisaObject[?]]): lisa.fol.FOL.Term**1 |-> lisa.fol.FOL.Formula =
            predicate.substituteUnsafe(map)
        def applyUnsafe(arg: lisa.fol.FOL.Term**1): lisa.fol.FOL.Formula = predicate.applyUnsafe(arg)
    }

    class SetType(val set: Term) extends Class(lambda(x, x ∈ set)) {
    }

    case class FunctionType[A<:SetType & Singleton, B<:SetType & Singleton](domain: A, range: B) extends SetType(AppliedFunction(to, Seq(domain.set, range.set))) {
        override type T = TypedTerm[this.type]
    }

    val to: ConstantFunctionLabel[2] = ConstantFunctionLabel("to", 2)
    extension (domain: SetType)
        def to(range: SetType) = FunctionType(domain, range)




    // (N to N).T <: N.T |-> N.T


*/






    trait IsClass[A]{
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




    /*
    val n: ℕ = TypedConstant("n", ???)
    val f: ℕ ==> ℕ = TypedConstant("f", ???)
    val g: (ℕ ==> ℕ) ==> (ℕ ==> ℕ) = TypedConstant("g", ???)

    f(n)
    val f2 = g(f)
    f2(n)
    n(g)
    */
    
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