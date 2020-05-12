class Lowering(environment : Map[String, GenericType]) {

    private def traitKey(t : Type) = new Substitution().traitKey(t)

    def lower(expression : Expression) : Expression = expression match {
        case EFunctions(functions, body) =>
            val newFunctions = functions.map { case GenericFunction(name, typeAnnotation, lambda) =>
                val Some(GenericType(typeParameters, traits, TConstructor(_, parameterAndReturnTypes))) = typeAnnotation
                val ELambda(parameters, lambdaReturnType, body) = lambda
                val extraParameters = traits.map { p => Parameter(traitKey(p).get, Some(p)) }
                val newParameterAndReturnTypes = extraParameters.map(_.typeAnnotation.get) ++ parameterAndReturnTypes
                val newTypeAnnotation = GenericType(
                    typeParameters,
                    traits,
                    TConstructor(s"Function${newParameterAndReturnTypes.size - 1}", newParameterAndReturnTypes)
                )
                val newLambda = ELambda(extraParameters ++ parameters, lambdaReturnType, lower(body))
                GenericFunction(name, Some(newTypeAnnotation), newLambda)
            }
            val newBody = lower(body)
            EFunctions(newFunctions, newBody)
        case ELambda(parameters, returnType, body) =>
            ELambda(parameters, returnType, lower(body))
        case EVariable(name, generics, traits, typeAnnotation) =>
            if(traits.isEmpty) expression else {
                val TConstructor(_, parametersAndReturnType) = typeAnnotation.get
                val parameters = parametersAndReturnType.init.zipWithIndex.map { case (t, i) =>
                    Parameter("_x" + (i + 1), Some(t))
                }
                val (extraArguments, extraArgumentTypes) = buildTraitArguments(traits).unzip
                val newParameterAndReturnTypes = extraArgumentTypes ++ parametersAndReturnType
                val newTypeAnnotation =
                    TConstructor(s"Function${newParameterAndReturnTypes.size - 1}", newParameterAndReturnTypes)
                ELambda(parameters, Some(parametersAndReturnType.last), EApply(
                    EVariable(name, generics, traits, Some(newTypeAnnotation)),
                    extraArguments ++ parameters.map { p => EVariable(p.name, List(), List(), p.typeAnnotation) }
                ))
            }
        case EApply(EVariable(name, generics, traits, typeAnnotation), arguments) =>
            val TConstructor(_, parametersAndReturnType) = typeAnnotation.get
            val (extraArguments, extraArgumentTypes) = buildTraitArguments(traits).unzip
            val newParameterAndReturnTypes = extraArgumentTypes ++ parametersAndReturnType
            val newTypeAnnotation =
                TConstructor(s"Function${newParameterAndReturnTypes.size - 1}", newParameterAndReturnTypes)
            val newArguments = extraArguments ++ arguments.map(lower)
            EApply(EVariable(name, generics, traits, Some(newTypeAnnotation)), newArguments)
        case EApply(function, arguments) =>
            EApply(lower(function), arguments.map(lower))
        case ELet(name, typeAnnotation, value, body) =>
            ELet(name, typeAnnotation, lower(value), lower(body))
        case EField(record, label, recordType) =>
            EField(lower(record), label, recordType)
        case EPair(first, second) =>
            EPair(lower(first), lower(second))
        case EInt(_) =>
            expression
        case EString(_) =>
            expression
        case EArray(itemType, items) =>
            EArray(itemType, items.map(lower))
        case ESemicolon(before, after) =>
            ESemicolon(lower(before), lower(after))
    }

    private def buildTraitArguments(traits : List[Type]) : List[(Expression, Type)] = {
        val inference = new Inference()
        traits.map { p =>
            var newGenerics = List[Type]()
            val newTraits = traitKey(p).flatMap(environment.get).toList.flatMap { genericType =>
                val freshTypeVariables = genericType.generics.map(_ => inference.substitution.freshTypeVariable())
                val instantiation = genericType.generics.zip(freshTypeVariables).toMap
                inference.substitution.unify(p, inference.instantiate(instantiation, genericType.uninstantiatedType))
                newGenerics = freshTypeVariables.map(inference.substitution.substitute)
                genericType.traits.map(t =>
                    inference.substitution.substitute(inference.instantiate(instantiation, t))
                )
            }
            val newReturnType = inference.substitution.substitute(p)
            val (arguments, argumentTypes) = buildTraitArguments(newTraits).unzip
            val newType =
                if(argumentTypes.isEmpty) newReturnType
                else TConstructor(s"Function${newTraits.size}", argumentTypes ++ List(newReturnType))
            val variable = EVariable(traitKey(p).get, newGenerics, newTraits, Some(newType))
            (if(arguments.isEmpty) variable else {
                EApply(variable, arguments)
            }) -> newReturnType
        }
    }

}
