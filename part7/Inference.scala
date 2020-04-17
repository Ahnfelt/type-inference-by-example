import scala.collection.immutable.SortedSet
import scala.collection.mutable.ArrayBuffer

/////////////////////////////////
// Syntax tree
/////////////////////////////////

sealed abstract class Expression

case class EFunctions(
    functions : List[GenericFunction],
    body : Expression
) extends Expression

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
    name : String,
    generics : List[Type] = List()
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

case class ESemicolon(
    before : Expression,
    after : Expression
) extends Expression


case class GenericFunction(
    name : String,
    typeAnnotation : Option[GenericType],
    lambda : Expression
)

case class GenericType(
    generics : List[String],
    uninstantiatedType : Type
)

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

    val genericParameterNames = Iterator.iterate(('A', 0)) {
        case ('Z', i) => ('A', i + 1)
        case (x, i) => ((x + 1).toChar, i)
    }.map { case (x, i) =>
        if(i == 0) x.toString else x.toString + i.toString
    }

    def freshTypeVariable() : TVariable = {
        val result = TVariable(substitution.length)
        substitution += result
        result
    }

    def infer(
        environment : Map[String, GenericType],
        expectedType : Type,
        expression : Expression
    ) : Expression = expression match {

        case EFunctions(functions, body) =>
            val recursiveEnvironment = environment ++ functions.map { function =>
                function.name -> function.typeAnnotation.getOrElse(GenericType(List(), freshTypeVariable()))
            }.toMap
            val ungeneralizedFunctions = functions.map { function =>
                val uninstantiatedType = recursiveEnvironment(function.name).uninstantiatedType
                function.copy(lambda = infer(recursiveEnvironment, uninstantiatedType, function.lambda))
            }
            solveConstraints()
            val newFunctions = ungeneralizedFunctions.map { function =>
                if(function.typeAnnotation.nonEmpty) function else {
                    val functionType = recursiveEnvironment(function.name).uninstantiatedType
                    val (newTypeAnnotation, newLambda) = generalize(environment, functionType, function.lambda)
                    function.copy(typeAnnotation = Some(newTypeAnnotation), lambda = newLambda)
                }
            }
            val newEnvironment = environment ++ newFunctions.map { function =>
                function.name -> function.typeAnnotation.get
            }.toMap
            val newBody = infer(newEnvironment, expectedType, body)
            EFunctions(newFunctions, newBody)

        case ELambda(parameters, returnType, body) =>
            val newReturnType = returnType.getOrElse(freshTypeVariable())
            val newParameterTypes = parameters.map(_.typeAnnotation.getOrElse(freshTypeVariable()))
            val newParameters = parameters.zip(newParameterTypes).map { case (p, t) =>
                p.copy(typeAnnotation = Some(t))
            }
            val newEnvironment = environment ++ newParameters.map { p =>
                p.name -> GenericType(List(), p.typeAnnotation.get)
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

        case EVariable(name, generics) =>
            val genericType = environment.getOrElse(name,
                throw TypeError("Variable not in scope: " + name)
            )
            val newGenerics = genericType.generics.map(_ => freshTypeVariable())
            val instantiation = genericType.generics.zip(newGenerics).toMap
            val variableType = instantiate(instantiation, genericType.uninstantiatedType)
            if(generics.nonEmpty) {
                if(generics.size != genericType.generics.size) {
                    throw TypeError("Wrong number of generics: " + expression + " vs. " + genericType)
                }
                for((t, v) <- generics.zip(newGenerics)) typeConstraints += CEquality(t, v)
            }
            typeConstraints += CEquality(expectedType, variableType)
            EVariable(name, newGenerics)

        case ELet(name, typeAnnotation, value, body) =>
            val newTypeAnnotation = typeAnnotation.getOrElse(freshTypeVariable())
            val newValue = infer(environment, newTypeAnnotation, value)
            val newEnvironment = environment.updated(name, GenericType(List(), newTypeAnnotation))
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

        case ESemicolon(before, after) =>
            val newBefore = infer(environment, freshTypeVariable(), before)
            val newAfter = infer(environment, expectedType, after)
            ESemicolon(newBefore, newAfter)

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
            if(occursIn(i, t2)) throw TypeError("Infinite type: $" + i + " = " + substitute(substitution, t2))
            substitution(i) = t2
        case (_, TVariable(i)) =>
            if(occursIn(i, t1)) throw TypeError("Infinite type: $" + i + " = " + substitute(substitution, t1))
            substitution(i) = t1
        case (TConstructor(name1, generics1), TConstructor(name2, generics2)) =>
            if(name1 != name2 || generics1.size != generics2.size) {
                throw TypeError(
                    "Type mismatch: " + substitute(substitution, t1) + " vs. " + substitute(substitution, t2)
                )
            }
            for((t1, t2) <- generics1.zip(generics2)) unify(t1, t2)
    }

    def occursIn(index : Int, t : Type) : Boolean = t match {
        case TVariable(i) if substitution(i) != TVariable(i) => occursIn(index, substitution(i))
        case TVariable(i) => i == index
        case TConstructor(_, generics) => generics.exists(t => occursIn(index, t))
    }

    def freeInType(t : Type) : SortedSet[Int] = t match {
        case TVariable(i) if substitution(i) != TVariable(i) => freeInType(substitution(i))
        case TVariable(i) => SortedSet(i)
        case TConstructor(_, generics) => generics.map(freeInType).fold(SortedSet[Int]()) { _ ++ _ }
    }

    def freeInGenericType(t : GenericType) : SortedSet[Int] = {
        freeInType(t.uninstantiatedType)
    }

    def freeInEnvironment(environment : Map[String, GenericType]) : SortedSet[Int] = {
        environment.values.map(freeInGenericType).fold(SortedSet[Int]()) { _ ++ _ }
    }

    def generalize(
        environment : Map[String, GenericType],
        t : Type,
        expression : Expression
    ) : (GenericType, Expression) = {
        val genericTypeVariables = freeInType(t) -- freeInEnvironment(environment)
        val genericNames = genericTypeVariables.map(_ -> genericParameterNames.next()).toList
        val localSubstitution = substitution.clone()
        for((i, name) <- genericNames) localSubstitution(i) = TConstructor(name)
        val newExpression = substituteExpression(localSubstitution, expression)
        val newType = substitute(localSubstitution, t)
        GenericType(genericNames.map { case (_, name) => name }, newType) -> newExpression
    }

    def instantiate(instantiation : Map[String, Type], t : Type) : Type = t match {
        case _ if instantiation.isEmpty => t
        case TVariable(i) if substitution(i) != TVariable(i) => instantiate(instantiation, substitution(i))
        case TConstructor(name, generics) =>
            instantiation.get(name).map { instantiationType =>
                if(generics.nonEmpty) throw TypeError("Higher kinded type encountered: " + substitute(substitution, t))
                instantiationType
            }.getOrElse {
                TConstructor(name, generics.map(t => instantiate(instantiation, t)))
            }
        case _ => t
    }

    def substitute(substitution : ArrayBuffer[Type], t : Type) : Type = t match {
        case TVariable(i) if substitution(i) != TVariable(i) => substitute(substitution, substitution(i))
        case TConstructor(name, generics) => TConstructor(name, generics.map(t => substitute(substitution, t)))
        case _ => t
    }

    def substituteExpression(
        substitution : ArrayBuffer[Type],
        expression : Expression
    ) : Expression = expression match {

        case EFunctions(functions, body) =>
            val newFunctions = functions.map { case GenericFunction(name, typeAnnotation, lambda) =>
                val newTypeAnnotation = typeAnnotation.map(genericType => genericType.copy(
                    uninstantiatedType = substitute(substitution, genericType.uninstantiatedType)
                ))
                GenericFunction(name, newTypeAnnotation, substituteExpression(substitution, lambda))
            }
            val newBody = substituteExpression(substitution, body)
            EFunctions(newFunctions, newBody)

        case ELambda(parameters, returnType, body) =>
            val newReturnType = returnType.map(substitute(substitution, _))
            val newParameters = parameters.map(p =>
                p.copy(typeAnnotation = p.typeAnnotation.map(substitute(substitution, _)))
            )
            val newBody = substituteExpression(substitution, body)
            ELambda(newParameters, newReturnType, newBody)

        case EApply(function, arguments) =>
            val newFunction = substituteExpression(substitution, function)
            val newArguments = arguments.map(substituteExpression(substitution, _))
            EApply(newFunction, newArguments)

        case EVariable(name, generics) =>
            val newGenerics = generics.map(substitute(substitution, _))
            EVariable(name, newGenerics)

        case ELet(name, typeAnnotation, value, body) =>
            val newTypeAnnotation = typeAnnotation.map(substitute(substitution, _))
            val newValue = substituteExpression(substitution, value)
            val newBody = substituteExpression(substitution, body)
            ELet(name, newTypeAnnotation, newValue, newBody)

        case EInt(_) =>
            expression

        case EString(_) =>
            expression

        case EArray(itemType, items) =>
            val newItemType = itemType.map(substitute(substitution, _))
            val newItems = items.map(substituteExpression(substitution, _))
            EArray(newItemType, newItems)

        case ESemicolon(before, after) =>
            val newBefore = substituteExpression(substitution, before)
            val newAfter = substituteExpression(substitution, after)
            ESemicolon(newBefore, newAfter)

    }

}


/////////////////////////////////
// Tests
/////////////////////////////////

object Inference {

    val initialEnvironment =
        List("+", "-", "*", "/").map(
            _ -> GenericType(List(),
                TConstructor("Function2", List(TConstructor("Int"), TConstructor("Int"), TConstructor("Int")))
            )
        ).toMap ++
        List("==", "!=", "<", ">").map(
            _ -> GenericType(List(),
                TConstructor("Function2", List(TConstructor("Int"), TConstructor("Int"), TConstructor("Bool")))
            )
        ).toMap ++
        List("false", "true").map(_ -> GenericType(List(), TConstructor("Bool"))).toMap ++
        List(
            "if" -> GenericType(List("T"),
                TConstructor("Function3", List(
                    TConstructor("Bool"),
                    TConstructor("Function0", List(TConstructor("T"))),
                    TConstructor("Function0", List(TConstructor("T"))),
                    TConstructor("T")
                ))
            )
        ).toMap

    def infer(expression : Expression) : Expression = {
        val inference = new Inference()
        val newExpression = inference.infer(initialEnvironment, inference.freshTypeVariable(), expression)
        inference.solveConstraints()
        inference.substituteExpression(inference.substitution, newExpression)
    }

    def printInfer(expression : Expression) : String = {
        try {
            infer(expression).toString
        } catch {
            case e : TypeError => e.message
        }
    }

    // function singleton(x) { return [x]; }
    // singleton(42);
    // singleton("foo")
    val e1 = EFunctions(
        List(
            GenericFunction("singleton", None,
                ELambda(List(Parameter("x", None)), None,
                    EArray(None, List(EVariable("x", List())))
                )
            )
        ),
        ESemicolon(
            EApply(EVariable("singleton", List()), List(EInt(42))),
            EApply(EVariable("singleton", List()), List(EString("foo"))),
        )
    )

    // function even(x : Int) { odd(x - 1) }
    // function odd(x : Int) { even(x - 1) }
    // even(42)
    val e2 = EFunctions(
        List(
            GenericFunction("even", None,
                ELambda(List(Parameter("x", None)), None,
                    EApply(
                        EVariable("odd", List()),
                        List(EApply(EVariable("-", List()), List(EVariable("x", List()), EInt(1))))
                    )
                )
            ),
            GenericFunction("odd", None,
                ELambda(List(Parameter("x", None)), None,
                    EApply(
                        EVariable("even", List()),
                        List(EApply(EVariable("-", List()), List(EVariable("x", List()), EInt(1))))
                    )
                )
            )
        ),
        EApply(EVariable("even", List()), List(EInt(42)))
    )

    // function even(x : Int) { if(x == 0, () => true, () => odd(x - 1)) }
    // function odd(x : Int) { if(x == 0, () => false, () => even(x - 1)) }
    // even(42)
    val e3 = EFunctions(
        List(
            GenericFunction("even", None,
                ELambda(List(Parameter("x", None)), None,
                    EApply(
                        EVariable("if", List()),
                        List(
                            EApply(EVariable("==", List()), List(EVariable("x", List()), EInt(0))),
                            ELambda(List(), None, EVariable("true")),
                            ELambda(List(), None, EApply(
                                EVariable("odd", List()),
                                List(EApply(EVariable("-", List()), List(EVariable("x", List()), EInt(1))))
                            )),
                        )
                    )
                )
            ),
            GenericFunction("odd", None,
                ELambda(List(Parameter("x", None)), None,
                    EApply(
                        EVariable("if", List()),
                        List(
                            EApply(EVariable("==", List()), List(EVariable("x", List()), EInt(0))),
                            ELambda(List(), None, EVariable("false")),
                            ELambda(List(), None, EApply(
                                EVariable("even", List()),
                                List(EApply(EVariable("-", List()), List(EVariable("x", List()), EInt(1))))
                            )),
                        )
                    )
                )
            )
        ),
        EApply(EVariable("even", List()), List(EInt(42)))
    )

    // function id<A>(x : A) : A { return x; }
    // id("foo")
    val e4 = EFunctions(
        List(
            GenericFunction("id", Some(GenericType(List("A"), TConstructor("Function1", List(TConstructor("A"), TConstructor("A"))))),
                ELambda(List(Parameter("x", None)), None, EVariable("x"))
            )
        ),
        EApply(EVariable("id"), List(EString("foo")))
    )

    // x => x(x)
    val e5 = ELambda(List(Parameter("x", None)), None, EApply(EVariable("x"), List(EVariable("x"))))

    // function compose(f, g) { return x => f(g(x)); }
    // compose
    val e6 = EFunctions(
        List(
            GenericFunction("compose", None,
                ELambda(List(Parameter("f", None), Parameter("g", None)), None,
                    ELambda(List(Parameter("x", None)), None,
                        EApply(EVariable("f"), List(
                            EApply(EVariable("g"), List(
                                EVariable("x")
                            ))
                        ))
                    )
                )
            )
        ),
        EVariable("compose")
    )

    def main(args : Array[String]) : Unit = {
        println(printInfer(
            e3
        ))
    }

}
