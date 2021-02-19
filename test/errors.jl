@testset "Errors" begin
    #=
    not_in_scope(x) = x + y
    =#
    not_in_scope = flet(:not_in_scope, DataType[Any], lam([(:x, Any)], op(:+, DMTerm[var(:x, Any), var(:y, Any)])), var(:not_in_scope, Any))
    @test_throws NotInScope infer_sensitivity(not_in_scope)

    #=
    function num_of_args(x)
        f(x,y) = 1 + y
        f(x)
    end
    =#
    num_of_args = flet(:num_of_args, [Any], lam([(:x, Any)], flet(:f, [Any, Any], lam([(:x, Any), (:y, Any)], op(:+, DMTerm[sng(1), var(:y, Any)])), apply(var(:f, Any), DMTerm[var(:x, Any)]))), var(:num_of_args, Any))
    @test_throws WrongNoOfArgs infer_sensitivity(num_of_args)

    #=
    function expect_numeric(x)
        f(x,y) = 1 + y
        f + x
    end
    =#
    expect_numeric = flet(:expect_numeric, DataType[Any], lam([(:x, Any)], flet(:f, DataType[Any, Any], lam([(:x, Any), (:y, Any)], op(:+, DMTerm[sng(1), var(:y, Any)])), op(:+, DMTerm[var(:f, Any), var(:x, Any)]))), var(:expect_numeric, Any))
    @test_throws NotNumeric infer_sensitivity(expect_numeric)

    #=
    function wrong_argtype(x)
        f(x::Integer) = 1 + x
        f(0.23)
    end
    =#
    wrong_argtype = flet(:wrong_argtype, DataType[Any], lam(Tuple{Symbol,DataType}[(:x, Any)], flet(:f, DataType[Integer], lam(Tuple{Symbol,DataType}[(:x, Integer)], op(:+, DMTerm[sng(1), var(:x, Any)])), apply(var(:f, Any), DMTerm[sng(0.23)]))), var(:wrong_argtype, Any))
    @test_throws NotSubtype infer_sensitivity(wrong_argtype)

    #=
    function no_arrow(x)
        f(g) = g(x)
        f(0.23)
    end
    =#
    no_arrow = flet(:no_arrow, DataType[Any], lam(Tuple{Symbol,DataType}[(:x, Any)], flet(:f, DataType[Any], lam(Tuple{Symbol,DataType}[(:g, Any)], apply(var(:g, Any), DMTerm[var(:x, Any)])), apply(var(:f, Any), DMTerm[sng(0.23)]))), var(:no_arrow, Any))
    @test_throws NotSubtype infer_sensitivity(no_arrow)

    #=
    function no_arrow_2(x)
        f(g::Integer) = g
        f(x -> x+1)
    end
    =#
    no_arrow2 = flet(:no_arrow_2, DataType[Any], lam(Tuple{Symbol,DataType}[(:x, Any)], flet(:f, DataType[Integer], lam(Tuple{Symbol,DataType}[(:g, Integer)], var(:g, Any)), apply(var(:f, Any), DMTerm[lam(Tuple{Symbol,DataType}[(:x, Any)], op(:+, DMTerm[var(:x, Any), sng(1)]))]))), var(:no_arrow_2, Any))
    @test_throws NotSubtype infer_sensitivity(no_arrow2)

    #=
    function no_matching_choice()
        f(y) = 10
        f(x::Integer, y) = 10
        f(x::Integer, y::Integer) = 10
        f(23.42, 0)
    end
    =#
    no_matching_choice = flet(:no_matching_choice, DataType[], lam(Tuple{Symbol,DataType}[], flet(:f, DataType[Any], lam(Tuple{Symbol,DataType}[(:y, Any)], sng(10)), flet(:f, DataType[Integer, Any], lam(Tuple{Symbol,DataType}[(:x, Integer), (:y, Any)], sng(10)), flet(:f, DataType[Integer, Integer], lam(Tuple{Symbol,DataType}[(:x, Integer), (:y, Integer)], sng(10)), apply(var(:f, Any), DMTerm[sng(23.42), sng(0)]))))), var(:no_matching_choice, Any))
    @test_throws NoChoiceFound infer_sensitivity(no_matching_choice)

    @test_throws UnificationError DiffPrivacyInference.unify_DMType(DMReal(), DMInt())
    @test_throws WrongNoOfArgs DiffPrivacyInference.unify_DMType(Arr([(1, DMInt())], Constant(DMReal(), 23.42)),  Arr([], Constant(DMReal(), 23.42)))
    @test_throws UnificationError DiffPrivacyInference.unify_Sensitivity(23, 42)
end;
