package lisa.fol
import lisa.kernel.fol.FOL.Identifier
import FOLHelpers.freshId
import lisa.utils.K
import scala.reflect.ClassTag
trait Lambdas extends Common{
  /**
    * Denotes a lambda expression, i.e. an expression with "holes". 
    * N is the number of arguments.
    * T is the type of input of the lambda.
    * R is the return type.
    * For example, LambdaExpression[Term, Formula, 2] denotes an expression of type (Term**2 |-> Formula),
    * i.e. an expression that can be substituted in place of a 2-variable predicate
    *
    * @param bounds The bound variable encoding the parameter of the lambda
    * @param body The body of the lambda
    * @param arity The number of parameters.
    */
  case class LambdaExpression[T <: LisaObject[T], R <: LisaObject[R], N <: Arity](bounds:Seq[SchematicLabel[T]], body:R, arity:N) extends |->[T**N, R]{
    assert(arity == bounds.length)
    private val seqBounds = bounds.toSeq

    def app(args: T**N): R = body.substituteUnsafe((bounds zip args.toSeq).toMap)
    def appUnsafe(args: Seq[T]): R = body.substituteUnsafe((bounds zip args.toSeq).toMap)

    /**
      * Substitute schematic symbols by values of corresponding type in the body of expressions. The variables of the expression are bound: This implies that 
      * 1. They are not substituted in the body even if they are in the substitution map, and
      * 2. The bounds of the expression are renamed before substitution if they appear in the substitution.
      *
      * @param map
      * @return
      */
    def substituteUnsafe(map: Map[SchematicLabel[_], LisaObject[_]]): LambdaExpression[T, R, N] = {
      val newSubst = map -- seqBounds
      val conflict = map.values.flatMap(_.freeSchematicLabels).toSet.intersect(bounds.asInstanceOf)
      if (conflict.nonEmpty) {
        val taken = (map.values.flatMap(_.allSchematicLabels).map(_.id) ++ map.keys.map(_.id)).toList
        val newBounds = seqBounds.scanLeft[List[Identifier]](taken)((list, v: SchematicLabel[T]) =>
          freshId(list, v.id) :: list
        ).map(_.head).zip(seqBounds).map(v => v._2.rename(v._1))
        val newBody = body.substituteUnsafe(seqBounds.zip(newBounds.map(_.lift)).toMap)
        LambdaExpression(newBounds, newBody.substituteUnsafe(newSubst), arity)
      } else{
        LambdaExpression(bounds, body.substituteUnsafe(newSubst), arity)
      }
    }

    def freeSchematicLabels:Set[SchematicLabel[?]] = body.freeSchematicLabels--seqBounds
    def allSchematicLabels:Set[SchematicLabel[?]] = body.freeSchematicLabels

  }

  /**
    * Construct a Lambda expression with a single variable
    */
  def lambda[T <: LisaObject[T],R <: LisaObject[R]](bound:SchematicLabel[T], body:R) = LambdaExpression[T, R, 1](Seq(bound), body, 1)
  /**
    * Construct a Lambda expression with multiple variables
    */
  def lambda[T <: LisaObject[T], R <: LisaObject[R], N <: Arity](bounds:SchematicLabel[T]**N, body:R)(using n: ValueOf[N]) = {
    val boundsSeq = bounds.toSeq
    LambdaExpression[T, R, N](boundsSeq, body, n.value)
  }
  def lambda[T <: LisaObject[T], R <: LisaObject[R]](bounds:Seq[SchematicLabel[T]], body:R, n: Int) = {
      val boundsSeq = bounds.toSeq
      LambdaExpression(boundsSeq, body, n)
    }

    /**
      * Recovers the underlying [[K.LambdaTermTerm]]
      */
  extension [N <: Arity] (ltt:LambdaExpression[Term, Term, N]) {
    def underlyingLTT: K.LambdaTermTerm  = 
      K.LambdaTermTerm(ltt.bounds.map(b => b.asInstanceOf[Variable].underlyingLabel), ltt.body.underlying)
  }
  /**
    * Recovers the underlying [[K.LambdaTermFormula]]
    */
  extension [N <: Arity] (ltf:LambdaExpression[Term, Formula, N]) {
    def underlyingLTF: K.LambdaTermFormula  = 
      K.LambdaTermFormula(ltf.bounds.map(b => b.asInstanceOf[Variable].underlyingLabel), ltf.body.underlying)
  }



  /**
    * Recovers the underlying [[K.LambdaFormulaFormula]]
    */
  extension [N <: Arity] (lff:LambdaExpression[Formula, Formula, N]) {
    def underlyingLFF: K.LambdaFormulaFormula =  
      K.LambdaFormulaFormula(lff.bounds.map((b: SchematicLabel[Formula]) => b.asInstanceOf[VariableFormula].underlyingLabel), lff.body.underlying)
  }


}
