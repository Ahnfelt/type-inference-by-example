class Emitter() {

    private val emptySubstitution = new Substitution()

    def emit(expression : Expression) : String = ((expression match {
        case EFunctions(functions, body) =>
            val functionCode = functions.map { case GenericFunction(name, typeAnnotation, lambda) =>
                val ELambda(parameters, _, body) = lambda
                List(
                    "function ", escapeName(name),
                    "(", parameters.map(_.name).map(escapeName).mkString(", "), ") {\n",
                    "return ", emit(body), "\n}"
                ).mkString
            }.mkString
            List("function() {\n", functionCode, "\nreturn ", emit(body), "\n}()")
        case ELambda(parameters, _, body) =>
            List("((", parameters.map(_.name).map(escapeName).mkString(", "), ") => ", emit(body), ")")
        case EVariable(name, _, traits, _) =>
            List(escapeName(name))
        case EApply(function, arguments) =>
            List(emit(function), "(", arguments.map(emit).mkString(", "), ")")
        case ELet(name, _, value, body) =>
            List("function() {\nlet ", escapeName(name), " = ", emit(value), ";\nreturn ", emit(body), "\n}()")
        case EField(record, label, recordType) =>
            val traitType = TConstructor(label, recordType.toList)
            List(emptySubstitution.traitKey(traitType).get, "(", emit(record), ")")
        case EPair(first, second) =>
            List("{first: ", emit(first), ", second: ", emit(second), "}")
        case EInt(value) =>
            List(value.toString)
        case EString(value) =>
            List("\"", value.flatMap[Char] {
                case '"' => "\\\""
                case '\\' => "\\\\"
                case c if c < 0x10 => "\\u000" + c.toHexString
                case c if c < 0x20 => "\\u001" + (c - 0x10).toHexString
                case c => c.toString
            }.mkString, "\"")
        case EArray(_, items) =>
            List("[", items.map(emit).mkString(", "), "]")
        case ESemicolon(before, after) =>
            List("(", emit(before), ",\n", emit(after), ")")
    }) : List[String]).mkString

    def escapeName(name : String) : String = {
        name.flatMap {
            case c if c >= 'a' && c <= 'z' => c.toString
            case c if c >= 'A' && c <= 'Z' => c.toString
            case c if c >= '0' && c <= '9' => c.toString
            case '_' => "_"
            case c => "_" + c.toInt
        }
    }

}
