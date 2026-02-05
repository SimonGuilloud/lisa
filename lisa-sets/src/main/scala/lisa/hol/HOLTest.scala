package lisa.hol
import VarsAndFunctions._
import lisa.utils.fol.FOL.{variable, Variable}

object HOLTest extends lisa.HOL{

    val x = variable[Ind]
    val y = variable[Ind]
    val f = variable[Ind]
    val g = variable[Ind]
    val h = variable[Ind]
    
    given ctx: Map[Variable[Ind], Typ] = Map(
      x -> 𝔹,
      y -> 𝔹,
      f -> (𝔹 ->: 𝔹),
      g -> (𝔹 ->: (𝔹 ->: 𝔹)),
      h -> ((𝔹 ->: 𝔹) ->: 𝔹)
    )

    output("------Expression 1------")
    val expr1 = g*(x)*(f*(y))
    output("expr1: " + expr1)
    output("expr1 type: " + computeType(expr1, ctx))

    val typecheckTest = TypingTheorem(expr1 :: 𝔹)


    output("------Expression 2------")
    val expr2 = g*(x)*(fun(x :: 𝔹, f*(x))*(y))
    output("expr2: " + expr2)
    output("expr2 type: " + computeType(expr2, ctx))

    val typecheckTest2 = TypingTheorem(expr2 :: 𝔹)


    output("------Expression 3------")
    val expr3 = x =:= y
    output("expr3: " + expr3)
    output("expr3 type: " + computeType(expr3, ctx))

    val typecheckTest3 = TypingTheorem(expr3 :: 𝔹 )

    output("------Expression 4------")
    val expr4 = (g*(x)) =:= fun(x :: 𝔹, f*(x))
    output("expr4: " + expr4)
    output("expr4 type: " + computeType(expr4, ctx))

    val typecheckTest4 = TypingTheorem(expr4 :: 𝔹 )

    output("------Expression 5------")
    val expr5 = fun(h :: ((𝔹 ->: 𝔹) ->: 𝔹),  fun(f :: (𝔹 ->: 𝔹), f*(x)) =:= h)
    output("expr5: " + expr5)
    output("expr5 type: " + computeType(expr5, ctx))

    val typecheckTest5 = TypingTheorem(expr5 :: (((𝔹 ->: 𝔹) ->: 𝔹) ->: 𝔹) )

}