import scala.collection.mutable.ArrayBuffer

/////////////////////////////////
// Syntax tree
/////////////////////////////////

sealed abstract class Expression
case class ELambda(x : String, e : Expression) extends Expression
case class EApply(e1 : Expression, e2 : Expression) extends Expression
case class EVariable(x : String) extends Expression

sealed abstract class Type
case class TConstructor(name : String, generics : List[Type] = List()) extends Type
case class TVariable(index : Int) extends Type

sealed abstract class Constraint
case class CEquality(t1 : Type, t2 : Type) extends Constraint


/////////////////////////////////
// Type inference
/////////////////////////////////

case class TypeError(message : String) extends RuntimeException

class Inference() {

    val typeConstraints = ArrayBuffer[Constraint]()
    val substitution = ArrayBuffer[Type]()

    def freshTypeVariable() : TVariable = {
        val result = TVariable(substitution.length)
        substitution += result
        result
    }

    def inferType(
        expression : Expression,
        environment : Map[String, Type]
    ) : Type = expression match {
        case ELambda(x, e) =>
            val t1 = freshTypeVariable()
            val environment2 = environment.updated(x, t1)
            val t2 = inferType(e, environment2)
            TConstructor("Function1", List(t1, t2))
        case EApply(e1, e2) =>
            val t1 = inferType(e1, environment)
            val t2 = inferType(e2, environment)
            val t3 = freshTypeVariable()
            typeConstraints += CEquality(t1, TConstructor("Function1", List(t2, t3)))
            t3
        case EVariable(x) =>
            environment.getOrElse(x,
                throw TypeError("Variable not in scope: " + x)
            )
    }

    def solveConstraints() : Unit = {
        for(CEquality(t1, t2) <- typeConstraints) unify(t1, t2)
        typeConstraints.clear()
    }

    def unify(t1 : Type, t2 : Type) : Unit = (t1, t2) match {
        case (TVariable(i), _) if substitution(i) != TVariable(i) =>
            unify(substitution(i), t2)
        case (_, TVariable(i)) if substitution(i) != TVariable(i) =>
            unify(t1, substitution(i))
        case (TVariable(i), _) =>
            if(occursIn(i, t2)) throw TypeError("Infinite type: $" + i + " = " + t2)
            substitution(i) = t2
        case (_, TVariable(i)) =>
            if(occursIn(i, t1)) throw TypeError("Infinite type: $" + i + " = " + t1)
            substitution(i) = t1
        case (TConstructor(name1, generics1), TConstructor(name2, generics2)) if name1 == name2 =>
            if(generics1.size != generics2.size) {
                throw TypeError("Generics mismatch: " + generics1 + " vs. " + generics2)
            }
            for((t1, t2) <- generics1.zip(generics2)) unify(t1, t2)
        case _ =>
            throw TypeError("Type mismatch: " + t1 + " vs. " + t2)
    }

    def occursIn(index : Int, t : Type) : Boolean = t match {
        case TVariable(i) if substitution(i) != TVariable(i) => occursIn(index, substitution(i))
        case TVariable(i) => i == index
        case TConstructor(_, generics) => generics.exists(t => occursIn(index, t))
    }

    def substitute(t : Type) : Type = t match {
        case TVariable(i) if substitution(i) != TVariable(i) => substitute(substitution(i))
        case TConstructor(name, generics) => TConstructor(name, generics.map(t => substitute(t)))
        case _ => t
    }

}


/////////////////////////////////
// Tests
/////////////////////////////////

val initialEnvironment = 
    List("+", "-", "*", "/").map(
        _ -> TConstructor("Function1", List(TConstructor("Int"), TConstructor("Function1", List(TConstructor("Int"), TConstructor("Int")))))
    ).toMap ++
    (0 to 99).map(_.toString).map(_ -> TConstructor("Int")).toMap

def infer(expression : Expression) : Type = {
    val inference = new Inference()
    val t = inference.inferType(expression, initialEnvironment)
    inference.solveConstraints()
    inference.substitute(t)
}

def printInfer(expression : Expression) : String = {
    try {
        infer(expression).toString
    } catch {
        case e : TypeError => e.message
    }
}

printInfer(
    ELambda("x", EApply(EApply(EVariable("+"), EVariable("x")), EVariable("x")))
)
