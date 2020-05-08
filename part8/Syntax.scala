package com.github.ahnfelt.alua.stuff.byexample6

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


case class TypeError(message : String) extends RuntimeException(message)
