import scala.collection.mutable.ArrayBuffer

/////////////////////////////////
// Syntax tree
/////////////////////////////////

sealed abstract class Expression

case class ELambda(
    parameters : List[Parameter],
    returnType : Option[Type],
    body : Expression
) extends Expression

case class EApply(
    function : Expression,
    arguments : List[Expression]
) extends Expression

case class EVariable(
    name : String
) extends Expression

case class ELet(
    name : String,
    typeAnnotation : Option[Type],
    value : Expression,
    body : Expression
) extends Expression

case class EInt(
    value : Int
) extends Expression

case class EString(
    value : String
) extends Expression

case class EArray(
    itemType : Option[Type],
    items : List[Expression],
) extends Expression


case class Parameter(
    name : String,
    typeAnnotation : Option[Type]
)


sealed abstract class Type
case class TConstructor(name : String, generics : List[Type] = List()) extends Type { 
  override def toString = if(generics.isEmpty) name else s"$name<${generics.mkString(", ")}>"
}
case class TVariable(index : Int) extends Type { 
  override def toString = s"$$$index" 
}

sealed abstract class Constraint
case class CEquality(t1 : Type, t2 : Type) extends Constraint


/////////////////////////////////
// Type inference
/////////////////////////////////

case class TypeError(message : String) extends RuntimeException(message)

class Inference() {

    val typeConstraints = ArrayBuffer[Constraint]()
    val substitution = ArrayBuffer[Type]()

    def freshTypeVariable() : TVariable = {
        val result = TVariable(substitution.length)
        substitution += result
        result
    }

    def infer(
        environment : Map[String, Type],
        expectedType : Type,
        expression : Expression
    ) : Expression = expression match {

        case ELambda(parameters, returnType, body) =>
            val newReturnType = returnType.getOrElse(freshTypeVariable())
            val newParameterTypes = parameters.map(_.typeAnnotation.getOrElse(freshTypeVariable()))
            val newParameters = parameters.zip(newParameterTypes).map { case (p, t) =>
                p.copy(typeAnnotation = Some(t))
            }
            val newEnvironment = environment ++ newParameters.map { p =>
                p.name -> p.typeAnnotation.get
            }
            val newBody = infer(newEnvironment, newReturnType, body)
            typeConstraints += CEquality(expectedType,
                TConstructor(s"Function${parameters.size}", newParameterTypes ++ List(newReturnType))
            )
            ELambda(newParameters, Some(newReturnType), newBody)

        case EApply(function, arguments) =>
            val argumentTypes = arguments.map(_ => freshTypeVariable())
            val functionType = TConstructor(s"Function${arguments.size}", argumentTypes ++ List(expectedType))
            val newFunction = infer(environment, functionType, function)
            val newArguments = arguments.zip(argumentTypes).map { case (argument, t) =>
                infer(environment, t, argument)
            }
            EApply(newFunction, newArguments)

        case EVariable(name) =>
            val variableType = environment.getOrElse(name,
                throw TypeError("Variable not in scope: " + name)
            )
            typeConstraints += CEquality(expectedType, variableType)
            expression

        case ELet(name, typeAnnotation, value, body) =>
            val newTypeAnnotation = typeAnnotation.getOrElse(freshTypeVariable())
            val newValue = infer(environment, newTypeAnnotation, value)
            val newEnvironment = environment.updated(name, newTypeAnnotation)
            val newBody = infer(newEnvironment, expectedType, body)
            ELet(name, Some(newTypeAnnotation), newValue, newBody)

        case EInt(_) =>
            typeConstraints += CEquality(expectedType, TConstructor("Int"))
            expression

        case EString(_) =>
            typeConstraints += CEquality(expectedType, TConstructor("String"))
            expression

        case EArray(itemType, items) =>
            val newItemType = itemType.getOrElse(freshTypeVariable())
            val newItems = items.map(item => infer(environment, newItemType, item))
            typeConstraints += CEquality(expectedType, TConstructor("Array", List(newItemType)))
            EArray(Some(newItemType), newItems)

    }

    def solveConstraints() : Unit = {
        for(CEquality(t1, t2) <- typeConstraints) unify(t1, t2)
        typeConstraints.clear()
    }

    def unify(t1 : Type, t2 : Type) : Unit = (t1, t2) match {
        case (TVariable(i1), TVariable(i2)) if i1 == i2 =>
        case (TVariable(i), _) if substitution(i) != TVariable(i) =>
            unify(substitution(i), t2)
        case (_, TVariable(i)) if substitution(i) != TVariable(i) =>
            unify(t1, substitution(i))
        case (TVariable(i), _) =>
            if(occursIn(i, t2)) throw TypeError("Infinite type: $" + i + " = " + substitute(t2))
            substitution(i) = t2
        case (_, TVariable(i)) =>
            if(occursIn(i, t1)) throw TypeError("Infinite type: $" + i + " = " + substitute(t1))
            substitution(i) = t1
        case (TConstructor(name1, generics1), TConstructor(name2, generics2)) =>
            if(name1 != name2 || generics1.size != generics2.size) {
                throw TypeError("Type mismatch: " + substitute(t1) + " vs. " + substitute(t2))
            }
            for((t1, t2) <- generics1.zip(generics2)) unify(t1, t2)
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

    def substituteExpression(
        expression : Expression
    ) : Expression = expression match {

        case ELambda(parameters, returnType, body) =>
            val newReturnType = returnType.map(substitute)
            val newParameters = parameters.map(p => p.copy(typeAnnotation = p.typeAnnotation.map(substitute)))
            val newBody = substituteExpression(body)
            ELambda(newParameters, newReturnType, newBody)

        case EApply(function, arguments) =>
            val newFunction = substituteExpression(function)
            val newArguments = arguments.map(substituteExpression)
            EApply(newFunction, newArguments)

        case EVariable(_) =>
            expression

        case ELet(name, typeAnnotation, value, body) =>
            val newTypeAnnotation = typeAnnotation.map(substitute)
            val newValue = substituteExpression(value)
            val newBody = substituteExpression(body)
            ELet(name, newTypeAnnotation, newValue, newBody)

        case EInt(_) =>
            expression

        case EString(_) =>
            expression

        case EArray(itemType, items) =>
            val newItemType = itemType.map(substitute)
            val newItems = items.map(substituteExpression)
            EArray(newItemType, newItems)

    }

}


/////////////////////////////////
// Tests
/////////////////////////////////

val initialEnvironment =
    List("+", "-", "*", "/").map(
        _ -> TConstructor("Function2", List(TConstructor("Int"), TConstructor("Int"), TConstructor("Int")))
    ).toMap

def infer(expression : Expression) : Expression = {
    val inference = new Inference()
    val newExpression = inference.infer(Map(), inference.freshTypeVariable(), expression)
    inference.solveConstraints()
    inference.substituteExpression(newExpression)
}

def printInfer(expression : Expression) : String = {
    try {
        infer(expression).toString
    } catch {
        case e : TypeError => e.message
    }
}

printInfer(
    ELet("singleton", None,
        ELambda(List(Parameter("x", None)), None,
            EArray(None, List(EVariable("x")))
        ),
        EApply(EVariable("singleton"), List(EInt(42)))
    )
)
