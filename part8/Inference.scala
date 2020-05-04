package com.github.ahnfelt.alua.stuff.byexample6

import scala.collection.immutable.{IntMap, SortedSet}
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
    generics : List[Type] = List(),
    traits : List[Type] = List()
) extends Expression

case class ELet(
    name : String,
    typeAnnotation : Option[Type],
    value : Expression,
    body : Expression
) extends Expression

case class EField(
    record : Expression,
    label : String,
    recordType : Option[Type]
) extends Expression

case class EPair(
    first : Expression,
    second : Expression,
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

case class Parameter(
    name : String,
    typeAnnotation : Option[Type]
)


case class GenericType(
    generics : List[String],
    traits : List[Type],
    uninstantiatedType : Type
)


sealed abstract class Type { override def toString = Type.pretty(this) }
case class TConstructor(name : String, generics : List[Type] = List()) extends Type
case class TVariable(index : Int) extends Type


object Type {
    def pretty(t : Type) : String = t match {
        case TConstructor(name, generics) => if(generics.isEmpty) name else s"$name<${generics.mkString(", ")}>"
        case TVariable(index) => s"$$$index"
    }
}


case class TraitConstraint(environment : Map[String, GenericType], constraint : Type)


/////////////////////////////////
// Type inference
/////////////////////////////////

case class TypeError(message : String) extends RuntimeException(message)


class Substitution(private var typeVariables : IntMap[Type] = IntMap()) {

    def copy() = new Substitution(typeVariables)

    def freshTypeVariable() : TVariable = {
        val result = TVariable(typeVariables.size)
        typeVariables += (typeVariables.size -> result)
        result
    }

    def get(index : Int) : Type = typeVariables(index) match {
        case TVariable(i) if i != index =>
            val t = get(i)
            typeVariables += (index -> t)
            t
        case t => t
    }

    def has(index : Int) : Boolean = typeVariables(index) match {
        case TVariable(i) => i != index
        case _ => true
    }

    def substitute(t : Type) : Type = t match {
        case TVariable(i) => if(has(i)) substitute(get(i)) else t
        case TConstructor(name, generics) => TConstructor(name, generics.map(t => substitute(t)))
    }

    def substituteExpression(
        expression : Expression
    ) : Expression = expression match {

        case EFunctions(functions, body) =>
            val newFunctions = functions.map { case GenericFunction(name, typeAnnotation, lambda) =>
                val newTypeAnnotation = typeAnnotation.map(genericType => genericType.copy(
                    uninstantiatedType = substitute(genericType.uninstantiatedType)
                ))
                GenericFunction(name, newTypeAnnotation, substituteExpression(lambda))
            }
            val newBody = substituteExpression(body)
            EFunctions(newFunctions, newBody)

        case ELambda(parameters, returnType, body) =>
            val newReturnType = returnType.map(substitute)
            val newParameters = parameters.map(p =>
                p.copy(typeAnnotation = p.typeAnnotation.map(substitute))
            )
            val newBody = substituteExpression(body)
            ELambda(newParameters, newReturnType, newBody)

        case EApply(function, arguments) =>
            val newFunction = substituteExpression(function)
            val newArguments = arguments.map(substituteExpression)
            EApply(newFunction, newArguments)

        case EVariable(name, generics, traits) =>
            val newGenerics = generics.map(substitute)
            val newTraits = traits.map(substitute)
            EVariable(name, newGenerics, newTraits)

        case ELet(name, typeAnnotation, value, body) =>
            val newTypeAnnotation = typeAnnotation.map(substitute)
            val newValue = substituteExpression(value)
            val newBody = substituteExpression(body)
            ELet(name, newTypeAnnotation, newValue, newBody)

        case EField(record, label, recordType) =>
            val newRecord = substituteExpression(record)
            val newRecordType = recordType.map(substitute)
            EField(newRecord, label, newRecordType)

        case EPair(first, second) =>
            val newFirst = substituteExpression(first)
            val newSecond = substituteExpression(second)
            EPair(newFirst, newSecond)

        case EInt(_) =>
            expression

        case EString(_) =>
            expression

        case EArray(itemType, items) =>
            val newItemType = itemType.map(substitute)
            val newItems = items.map(substituteExpression)
            EArray(newItemType, newItems)

        case ESemicolon(before, after) =>
            val newBefore = substituteExpression(before)
            val newAfter = substituteExpression(after)
            ESemicolon(newBefore, newAfter)

    }

    def unify(t1 : Type, t2 : Type) : Unit = (t1, t2) match {
        case (TVariable(i1), TVariable(i2)) if i1 == i2 =>
        case (TVariable(i), _) if has(i) => unify(get(i), t2)
        case (_, TVariable(i)) if has(i) => unify(t1, get(i))
        case (TVariable(i), _) =>
            if(occursIn(i, t2)) throw TypeError("Infinite type: $" + i + " = " + substitute(t2))
            typeVariables += (i -> t2)
        case (_, TVariable(i)) =>
            if(occursIn(i, t1)) throw TypeError("Infinite type: $" + i + " = " + substitute(t1))
            typeVariables += (i -> t1)
        case (TConstructor(name1, generics1), TConstructor(name2, generics2)) =>
            if(name1 != name2 || generics1.size != generics2.size) {
                throw TypeError(
                    "Type mismatch: " + substitute(t1) + " vs. " + substitute(t2)
                )
            }
            for((t1, t2) <- generics1.zip(generics2)) unify(t1, t2)
    }

    def occursIn(index : Int, t : Type) : Boolean = t match {
        case TVariable(i) if has(i) => occursIn(index, get(i))
        case TVariable(i) => i == index
        case TConstructor(_, generics) => generics.exists(t => occursIn(index, t))
    }

    def freeInType(t : Type) : SortedSet[Int] = t match {
        case TVariable(i) if has(i) => freeInType(get(i))
        case TVariable(i) => SortedSet(i)
        case TConstructor(_, generics) => generics.map(freeInType).fold(SortedSet[Int]()) { _ ++ _ }
    }

    def freeInGenericType(t : GenericType) : SortedSet[Int] = {
        freeInType(t.uninstantiatedType) ++ t.traits.map(freeInType).fold(SortedSet[Int]()) { _ ++ _ }
    }

    def freeInEnvironment(environment : Map[String, GenericType]) : SortedSet[Int] = {
        environment.values.map(freeInGenericType).fold(SortedSet[Int]()) { _ ++ _ }
    }

    def traitKey(t : Type) : Option[String] = t match {
        case TConstructor(traitName, TConstructor(typeName, _) :: _) =>
            Some(traitName + "_" + typeName)
        case TConstructor(traitName, TVariable(i) :: rest) if has(i) =>
            traitKey(TConstructor(traitName, get(i) :: rest))
        case TVariable(i) if has(i) =>
            traitKey(get(i))
        case _ =>
            None
    }

}


class Inference() {

    val substitution = new Substitution()

    var traitConstraints = Set[TraitConstraint]()

    val genericParameterNames = Iterator.iterate(('A', 0)) {
        case ('Z', i) => ('A', i + 1)
        case (x, i) => ((x + 1).toChar, i)
    }.map { case (x, i) =>
        if(i == 0) x.toString else x.toString + i.toString
    }

    def infer(
        environment : Map[String, GenericType],
        expectedType : Type,
        expression : Expression
    ) : Expression = expression match {

        case EFunctions(functions, body) =>
            val recursiveEnvironment = environment ++ functions.map { function =>
                function.name ->
                    function.typeAnnotation.getOrElse(GenericType(List(), List(), substitution.freshTypeVariable()))
            }.toMap
            val ungeneralizedFunctions = functions.map { function =>
                val uninstantiatedType = recursiveEnvironment(function.name).uninstantiatedType
                function.copy(lambda = infer(recursiveEnvironment, uninstantiatedType, function.lambda))
            }
            simplifyTraitConstraints()
            val untouchedTraitConstraints = traitConstraints
            val newFunctions = ungeneralizedFunctions.map { function =>
                if(function.typeAnnotation.nonEmpty) function else {
                    val functionType = recursiveEnvironment(function.name).uninstantiatedType
                    val (newTypeAnnotation, newLambda) =
                        generalize(untouchedTraitConstraints, environment, functionType, function.lambda)
                    function.copy(typeAnnotation = Some(newTypeAnnotation), lambda = newLambda)
                }
            }
            val newEnvironment = environment ++ newFunctions.map { function =>
                function.name -> function.typeAnnotation.get
            }.toMap
            val newBody = infer(newEnvironment, expectedType, body)
            EFunctions(newFunctions, newBody)

        case ELambda(parameters, returnType, body) =>
            val newReturnType = returnType.getOrElse(substitution.freshTypeVariable())
            val newParameterTypes = parameters.map(_.typeAnnotation.getOrElse(substitution.freshTypeVariable()))
            val newParameters = parameters.zip(newParameterTypes).map { case (p, t) =>
                p.copy(typeAnnotation = Some(t))
            }
            val newEnvironment = environment ++ newParameters.map { p =>
                p.name -> GenericType(List(), List(), p.typeAnnotation.get)
            }
            val newBody = infer(newEnvironment, newReturnType, body)
            substitution.unify(expectedType,
                TConstructor(s"Function${parameters.size}", newParameterTypes ++ List(newReturnType))
            )
            ELambda(newParameters, Some(newReturnType), newBody)

        case EApply(function, arguments) =>
            val argumentTypes = arguments.map(_ => substitution.freshTypeVariable())
            val functionType = TConstructor(s"Function${arguments.size}", argumentTypes ++ List(expectedType))
            val newFunction = infer(environment, functionType, function)
            val newArguments = arguments.zip(argumentTypes).map { case (argument, t) =>
                infer(environment, t, argument)
            }
            EApply(newFunction, newArguments)

        case EVariable(name, generics, traits) =>
            if(traits.nonEmpty) throw TypeError("Explicit dictionary passing not allowed: " + name)
            val genericType = environment.getOrElse(name,
                throw TypeError("Variable not in scope: " + name)
            )
            val newGenerics = genericType.generics.map(_ => substitution.freshTypeVariable())
            val instantiation = genericType.generics.zip(newGenerics).toMap
            val newTraits = genericType.traits.map(instantiate(instantiation, _))
            for(traitConstraint <- newTraits) {
                traitConstraints += TraitConstraint(environment, traitConstraint)
            }
            val variableType = instantiate(instantiation, genericType.uninstantiatedType)
            if(generics.nonEmpty) {
                if(generics.size != genericType.generics.size) {
                    throw TypeError("Wrong number of generics: " + expression + " vs. " + genericType)
                }
                for((t, v) <- generics.zip(newGenerics)) substitution.unify(t, v)
            }
            substitution.unify(expectedType, variableType)
            EVariable(name, newGenerics, newTraits)

        case ELet(name, typeAnnotation, value, body) =>
            val newTypeAnnotation = typeAnnotation.getOrElse(substitution.freshTypeVariable())
            val newValue = infer(environment, newTypeAnnotation, value)
            val newEnvironment = environment.updated(name, GenericType(List(), List(), newTypeAnnotation))
            val newBody = infer(newEnvironment, expectedType, body)
            ELet(name, Some(newTypeAnnotation), newValue, newBody)

        case EField(record, label, recordType) =>
            val newRecordType = recordType.getOrElse(substitution.freshTypeVariable())
            val newRecord = infer(environment, newRecordType, record)
            traitConstraints += TraitConstraint(environment, TConstructor(label, List(newRecordType, expectedType)))
            EField(newRecord, label, Some(newRecordType))

        case EPair(first, second) =>
            val t1 = substitution.freshTypeVariable()
            val t2 = substitution.freshTypeVariable()
            substitution.unify(expectedType, TConstructor("Pair", List(t1, t2)))
            val newFirst = infer(environment, t1, first)
            val newSecond = infer(environment, t2, second)
            EPair(newFirst, newSecond)

        case EInt(_) =>
            substitution.unify(expectedType, TConstructor("Int"))
            expression

        case EString(_) =>
            substitution.unify(expectedType, TConstructor("String"))
            expression

        case EArray(itemType, items) =>
            val newItemType = itemType.getOrElse(substitution.freshTypeVariable())
            val newItems = items.map(item => infer(environment, newItemType, item))
            substitution.unify(expectedType, TConstructor("Array", List(newItemType)))
            EArray(Some(newItemType), newItems)

        case ESemicolon(before, after) =>
            val newBefore = infer(environment, substitution.freshTypeVariable(), before)
            val newAfter = infer(environment, expectedType, after)
            ESemicolon(newBefore, newAfter)

    }

    def generalize(
        untouchedTraitConstraints : Set[TraitConstraint],
        environment : Map[String, GenericType],
        t : Type,
        expression : Expression
    ) : (GenericType, Expression) = {

        val genericTypeVariables =
            determinedBy(substitution.freeInType(t)) --
            determinedBy(substitution.freeInEnvironment(environment))

        val genericNames = genericTypeVariables.map(_ -> genericParameterNames.next()).toList

        val ungeneralizedTraits = untouchedTraitConstraints.filter { c =>
            substitution.freeInType(c.constraint).intersect(genericTypeVariables).nonEmpty
        }
        traitConstraints --= ungeneralizedTraits

        val localSubstitution = substitution.copy()
        for((i, name) <- genericNames) localSubstitution.unify(localSubstitution.get(i), TConstructor(name))
        val newExpression = localSubstitution.substituteExpression(expression)
        val newType = localSubstitution.substitute(t)
        val newTraits = ungeneralizedTraits.map(_.constraint).map(localSubstitution.substitute).toList // Sort?

        GenericType(genericNames.map { case (_, name) => name }, newTraits, newType) -> newExpression

    }

    def instantiate(instantiation : Map[String, Type], t : Type) : Type = t match {
        case _ if instantiation.isEmpty => t
        case TVariable(i) if substitution.has(i) => instantiate(instantiation, substitution.get(i))
        case TConstructor(name, generics) =>
            instantiation.get(name).map { instantiationType =>
                if(generics.nonEmpty) throw TypeError("Higher kinded type encountered: " + substitution.substitute(t))
                instantiationType
            }.getOrElse {
                TConstructor(name, generics.map(t => instantiate(instantiation, t)))
            }
        case _ => t
    }

    def simplifyTraitConstraints() : Unit = {

        traitConstraints = traitConstraints.flatMap { case c@TraitConstraint(environment, constraint) =>
            substitution.traitKey(constraint).map { key =>
                environment.get(key).map { genericType =>
                    val newGenerics = genericType.generics.map(_ => substitution.freshTypeVariable())
                    val instantiation = genericType.generics.zip(newGenerics).toMap
                    substitution.unify(constraint, instantiate(instantiation, genericType.uninstantiatedType))
                    val newTraits = genericType.traits.map(instantiate(instantiation, _))
                    newTraits.map(TraitConstraint(environment, _)).toSet
                }.getOrElse {
                    throw TypeError("No such instance: " + substitution.substitute(constraint))
                }
            }.getOrElse(Set(c))
        }

        var collisionMap = Map[(String, Int), List[Type]]()
        def collide(c : Type) : Unit = c match {
            case TVariable(i) if substitution.has(i) =>
                collide(substitution.get(i))
            case TConstructor(traitName, TVariable(i) :: rest) if substitution.has(i) =>
                collide(TConstructor(traitName, substitution.get(i) :: rest))
            case TConstructor(traitName, TVariable(i) :: rest) =>
                val key = (traitName, i)
                collisionMap.get(key) match {
                    case None =>
                        collisionMap += key -> rest
                    case Some(collision) =>
                        if(rest.size != collision.size) {
                            val c2 = TConstructor(traitName, TVariable(i) :: collision)
                            throw TypeError(
                                s"Mismatch: ${substitution.substitute(c)} vs. ${substitution.substitute(c2)}"
                            )
                        }
                        for((a, b) <- collision.zip(rest)) substitution.unify(a, b)
                }
            case _ =>
        }
        for(c <- traitConstraints) collide(c.constraint)

    }

    def determinedBy(determined : SortedSet[Int]) : SortedSet[Int] = {
        val newDetermined = traitConstraints.collect {
            case TraitConstraint(_, TConstructor(_, first::rest)) =>
                val firstFree = substitution.freeInType(first)
                if(!firstFree.subsetOf(determined)) SortedSet[Int]() else {
                    rest.map(substitution.freeInType).fold(SortedSet[Int]()) { _ ++ _ }
                }
        }.fold(SortedSet[Int]()) { _ ++ _ }
        if(newDetermined.subsetOf(determined)) determined
        else determinedBy(determined ++ newDetermined)
    }

}


/////////////////////////////////
// Tests
/////////////////////////////////

object Inference {

    val initialEnvironment =
        List("+", "-", "*", "/").map(
            _ -> GenericType(List("T"), List(TConstructor("Number", List(TConstructor("T")))),
                TConstructor("Function2", List(TConstructor("T"), TConstructor("T"), TConstructor("T")))
            )
        ).toMap ++
        List("==", "!=", "<", ">").map(
            _ -> GenericType(List("T"), List(TConstructor("Order", List(TConstructor("T")))),
                TConstructor("Function2", List(TConstructor("T"), TConstructor("T"), TConstructor("Bool")))
            )
        ).toMap ++
        List("false", "true").map(_ -> GenericType(List(), List(), TConstructor("Bool"))).toMap ++
        List(
            "if" -> GenericType(List("T"), List(),
                TConstructor("Function3", List(
                    TConstructor("Bool"),
                    TConstructor("Function0", List(TConstructor("T"))),
                    TConstructor("Function0", List(TConstructor("T"))),
                    TConstructor("T")
                ))
            )
        ).toMap ++
        List(
            "Number_Int" -> GenericType(List(), List(), TConstructor("Number", List(TConstructor("Int")))),
            "Number_Float" -> GenericType(List(), List(), TConstructor("Number", List(TConstructor("Float")))),
            "Order_Int" -> GenericType(List(), List(), TConstructor("Order", List(TConstructor("Int")))),
        ).toMap

    def infer(expression : Expression) : Expression = {
        val inference = new Inference()
        val newExpression = inference.infer(initialEnvironment, inference.substitution.freshTypeVariable(), expression)
        inference.simplifyTraitConstraints()
        for(c <- inference.traitConstraints) {
            throw TypeError("Ambiguous type variable: " + inference.substitution.substitute(c.constraint))
        }
        inference.substitution.substituteExpression(newExpression)
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

    // function even(x) { if(x == 0, () => true, () => odd(x - 1)) }
    // function odd(x) { if(x == 0, () => false, () => even(x - 1)) }
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
            GenericFunction("id",
                Some(GenericType(List("A"),  List(),
                    TConstructor("Function1", List(TConstructor("A"), TConstructor("A")))
                )),
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

    // function add(x, y) { return x + y; }
    // add(1, 2)
    val e7 = EFunctions(
        List(
            GenericFunction("add", None,
                ELambda(List(Parameter("x", None), Parameter("y", None)), None,
                    EApply(EVariable("+"), List(EVariable("x"), EVariable("y")))
                )
            )
        ),
        EApply(EVariable("add"), List(EInt(1), EInt(2)))
    )

    // function f(x) { return x.y.z; }
    // EInt(42)
    val e8 = EFunctions(
        List(
            GenericFunction("f", None,
                ELambda(List(Parameter("x", None)), None,
                    EField(EField(EVariable("x"), "y", None), "z", None)
                )
            )
        ),
        EInt(42)
    )

    // function f(x) { return (x.y, x.y); }
    // EInt(42)
    val e9 = EFunctions(
        List(
            GenericFunction("f", None,
                ELambda(List(Parameter("x", None)), None,
                    EPair(
                        EField(EVariable("x"), "y", None),
                        EField(EVariable("x"), "y", None)
                    )
                )
            )
        ),
        EInt(42)
    )

    def main(args : Array[String]) : Unit = {
        println(printInfer(
            e9
        ))
    }

}

