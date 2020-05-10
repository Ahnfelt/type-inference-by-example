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
                    Parameter("_p" + i, Some(t))
                }
                val extraArguments = buildTraitArguments(traits)
                ELambda(parameters, Some(parametersAndReturnType.last), EApply(
                    EVariable(name, generics, traits),
                    extraArguments ++ parameters.map { p => EVariable(p.name, List(), List(), p.typeAnnotation) }
                ))
            }
        case e@EApply(EVariable(_, _, traits, _), _) =>
            val extraArguments = buildTraitArguments(traits)
            e.copy(arguments = extraArguments ++ e.arguments.map(lower))
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

    private def buildTraitArguments(traits : List[Type]) : List[Expression] = {
        traits.map { p =>
            val arguments = buildTraitArguments(traitKey(p).flatMap(environment.get).toList.flatMap(_.traits))
            val variable = EVariable(traitKey(p).get, List(), List(), None)
            // TODO: Type, possibly with arguments
            // TODO: Order_A vs Order_T
            if(arguments.isEmpty) variable else {
                EApply(variable, arguments)
            }
        }
    }

}
