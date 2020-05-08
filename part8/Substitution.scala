package com.github.ahnfelt.alua.stuff.byexample6

import scala.collection.immutable.{IntMap, SortedSet}

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
