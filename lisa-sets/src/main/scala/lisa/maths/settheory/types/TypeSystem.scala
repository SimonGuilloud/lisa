package lisa.maths.settheory.types


object TypeSystem {
    import lisa.fol.FOL.{*, given}
    import lisa.SetTheoryLibrary.*

    private val x = Variable("x")



  


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




    val TopType = new Class(lambda(x, top))
    object BottomType extends Class(lambda(x, bot))

    



    // Define Class Assumptions as containers over a variable and a type, which is also a formula.

    /**
      * A type assumption is a pair of a variable and a type.
      * It is also a formula, equal to the type applied to the variable.
      */
    trait TypeAssumption {
        this: Formula =>
        val x: Variable
        val typ: Class
        val formula: Formula

        def unapply(f: Formula): Option[(Variable, Class)] = 
            f match
                case f: TypeAssumption => Some((f.x, f.typ))
                case _ => None
    }

    object TypeAssumption {
        /**
          * A type assumption is a pair of a variable and a type.
          * It is also a formula, equal to the type applied to the variable.
          */
        def apply(x: Variable, typ: Class): TypeAssumption = 
            val formula = typ(x)
            formula match
                case f: VariableFormula => throw new IllegalArgumentException("Class formula cannot be a variable formula, as we require a type to have no free variable.")
                case f: ConstantFormula => new TypeAssumptionConstant(x, typ, f)
                case f: AppliedPredicate => new TypeAssumptionPredicate(x, typ, f)
                case f: AppliedConnector => new TypeAssumptionConnector(x, typ, f)
                case f: BinderFormula => new TypeAssumptionBinder(x, typ, f)
    }
    private class TypeAssumptionConstant(val x: Variable, val typ: Class, val formula: ConstantFormula) extends ConstantFormula(formula.id) with TypeAssumption
    private class TypeAssumptionPredicate(val x: Variable, val typ: Class, val formula: AppliedPredicate) extends AppliedPredicate(formula.label, formula.args) with TypeAssumption
    private class TypeAssumptionConnector(val x: Variable, val typ: Class, val formula: AppliedConnector) extends AppliedConnector(formula.label, formula.args) with TypeAssumption
    private class TypeAssumptionBinder(val x: Variable, val typ: Class, val formula: BinderFormula) extends BinderFormula(formula.f, formula.bound, formula.body) with TypeAssumption

    

    class SetTypeAssumption(val x: Variable, val typ: SetType) extends AppliedPredicate(in, Seq(x, typ.set)) with TypeAssumption{
        val formula = x ∈ typ.set
    }





    trait TypedTerm[+Type <: Class] extends LisaObject[TypedTerm[Type]] {
        this: Term  =>
        val typ: Class

        def getTypeJudgement(proof:Proof): proof.Fact

        def apply[A <: SetType & Singleton, B <: SetType & Singleton](using ev: Type <:< FunctionType[A, B])(a: TypedTerm[A]): TypedTerm[B] = ???
    }


    trait Func[T, A] {
        type T1
        type T2
        extension (t:T){
            def apply(a: T1): T2
        }
    }

    //  TypedTerm[FunctionType[A, B]] = SetType((A to B)).T

    given thing[A <: SetType & Singleton, B <: SetType & Singleton] : Func[TypedTerm[FunctionType[A, B]], Int] = new Func[TypedTerm[FunctionType[A, B]], Int]{
        type T1 = TypedTerm[A] 
        type T2 = TypedTerm[B]
        def apply(a: TypedTerm[A]): TypedTerm[B] = ???
    }


    def foo[V: Func[V, Int]](v:V)(a: v.T1): v.T2 = v.apply(a)





    class TypedConstant[+Type <: Class & Singleton](id: Identifier, val typ:Type, val justif: JUSTIFICATION) extends Constant(id) with TypedTerm[Type] with LisaObject[TypedConstant[Type]]  {
        val formula = typ(this)
        def getTypeJudgement(proof: lisa.SetTheoryLibrary.Proof): proof.Fact = ???

        override def substituteUnsafe(map: Map[lisa.fol.FOL.SchematicLabel[?], lisa.fol.FOL.LisaObject[?]]): TypedConstant[Type] = this

    }

    class TypedConstantFunction[N <: Arity](id: Identifier, arity: N, val typs: Class**N, val justif: JUSTIFICATION) extends ConstantFunctionLabel[N](id, arity) 



}