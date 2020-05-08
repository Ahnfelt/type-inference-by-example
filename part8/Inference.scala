package com.github.ahnfelt.alua.stuff.byexample6

import scala.collection.immutable.{IntMap, SortedSet}
import scala.collection.mutable.ArrayBuffer

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
                val functionEnvironment = recursiveEnvironment ++
                    function.typeAnnotation.toList.flatMap(_.traits).map { t =>
                        substitution.traitKey(t).get -> GenericType(List(), List(), t)
                    }.toMap
                function.copy(lambda = infer(functionEnvironment, uninstantiatedType, function.lambda))
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
