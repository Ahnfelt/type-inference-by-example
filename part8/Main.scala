object Main {

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
            val e1 = infer(expression)
            val e2 = new Lowering().lower(e1)
            e1.toString + "\n\n" + e2.toString + "\n\n" + new Emitter().emit(e2)
        } catch {
            case error : TypeError => error.message
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

    // function f[T](x : T) : Int where y<T, Int> { return x.y + x.y; }
    // EInt(42)
    val e10 = EFunctions(
        List(
            GenericFunction("f",
                Some(GenericType(
                    List("T"),
                    List(TConstructor("y", List(TConstructor("T"), TConstructor("Int")))),
                    TConstructor("Function1", List(TConstructor("T"), TConstructor("Int")))
                )),
                ELambda(List(Parameter("x", None)), None,
                    EApply(EVariable("+"), List(
                        EField(EVariable("x"), "y", None),
                        EField(EVariable("x"), "y", None)
                    ))
                )
            )
        ),
        EInt(42)
    )

    def main(args : Array[String]) : Unit = {
        println(printInfer(
            e10
        ))
    }

}
