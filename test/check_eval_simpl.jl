


@testset "simpl_dispatch" begin

    # the terms are this lam with T in {Int, Real, Num}
    # λ (i::T).{
    #    flet f = λ (x::Integer, c).{ 1 * x } in {
    #    flet f = λ (x::Number, c).{ 2 * x } in {
    #    flet f = λ (x::Real, c).{ 3 * x } in {
    # f(i, 1) } } } }

    # julia function is
    # function g(i::T)
    #   f(x::Integer, b) = 1*x
    #   f(x::Number, c) = 2*x
    #   f(x::Real, c) = 3*x
    #   f(i,1)
    # end

    tint =  lam(Tuple{Symbol,DataType}[(:i, Integer)], flet(:f, DataType[Integer, Any], lam(Tuple{Symbol,DataType}[(:x, Integer), (:c, Any)], op(:*, DMTerm[sng(1), var(:x, Any)])), flet(:f, DataType[Number, Any], lam(Tuple{Symbol,DataType}[(:x, Number), (:c, Any)], op(:*, DMTerm[sng(2), var(:x, Any)])), flet(:f, DataType[Real, Any], lam(Tuple{Symbol,DataType}[(:x, Real), (:c, Any)], op(:*, DMTerm[sng(3), var(:x, Any)])), apply(var(:f, Any), DMTerm[var(:i, Any), sng(1)])))))
    τint = Arr([(1, DMInt())], DMInt())
    @test isequal(infer_sensitivity(tint), τint)

    treal =  lam(Tuple{Symbol,DataType}[(:i, Real)], flet(:f, DataType[Integer, Any], lam(Tuple{Symbol,DataType}[(:x, Integer), (:c, Any)], op(:*, DMTerm[sng(1), var(:x, Any)])), flet(:f, DataType[Number, Any], lam(Tuple{Symbol,DataType}[(:x, Number), (:c, Any)], op(:*, DMTerm[sng(2), var(:x, Any)])), flet(:f, DataType[Real, Any], lam(Tuple{Symbol,DataType}[(:x, Real), (:c, Any)], op(:*, DMTerm[sng(3), var(:x, Any)])), apply(var(:f, Any), DMTerm[var(:i, Any), sng(1)])))))
    τreal = Arr([(3, DMReal())], DMReal())
    @test isequal(infer_sensitivity(treal), τreal)

    tnum =  lam(Tuple{Symbol,DataType}[(:i, Number)], flet(:f, DataType[Integer, Any], lam(Tuple{Symbol,DataType}[(:x, Integer), (:c, Any)], op(:*, DMTerm[sng(1), var(:x, Any)])), flet(:f, DataType[Number, Any], lam(Tuple{Symbol,DataType}[(:x, Number), (:c, Any)], op(:*, DMTerm[sng(2), var(:x, Any)])), flet(:f, DataType[Real, Any], lam(Tuple{Symbol,DataType}[(:x, Real), (:c, Any)], op(:*, DMTerm[sng(3), var(:x, Any)])), apply(var(:f, Any), DMTerm[var(:i, Any), sng(1)])))))
    τnum = Arr([(DiffPrivacyInference.symbols(:sens_0), TVar(:sub_atype_23))], TVar(:ret20))
    @test isequal(infer_sensitivity(tnum), τnum)

end;


@testset "simpl_arith" begin
    ∞ = DiffPrivacyInference.∞

    # flet arith = λ (w, x, y, z).{ 3 * x + y - z * x + y rem 4 - 3 / x + w / 3 } in { arith }
    # julia: arith(w,x,y,z) = 3*(x+y) - z*ceil(x) + ceil(y) % 4 - 3/x + w/3
    t = flet(:arith, DataType[Any, Any, Any, Any], lam(Tuple{Symbol,DataType}[(:w, Any), (:x, Any), (:y, Any), (:z, Any)], op(:+, DMTerm[op(:-, DMTerm[op(:+, DMTerm[op(:-, DMTerm[op(:*, DMTerm[sng(3), op(:+, DMTerm[var(:x, Any), var(:y, Any)])]), op(:*, DMTerm[var(:z, Any), op(:ceil, DMTerm[var(:x, Any)])])]), op(:rem, DMTerm[op(:ceil, DMTerm[var(:y, Any)]), sng(4)])]), op(:/, DMTerm[sng(3), var(:x, Any)])]), op(:/, DMTerm[var(:w, Any), sng(3)])])), var(:arith, Any))

    τ = Arr([(0.3333333333333333, TVar(:op_arg_43)), (3 + 2∞, TVar(:op_arg_39)), (7, TVar(:op_arg_34)), (∞, TVar(:op_arg_22))], DMReal())
    @test isequal(infer_sensitivity(t), τ)
end;


@testset "simpl_slet_scope" begin
    #=
    the julia function is
    function scope(y)
        v = 100
        x = 10*v
        v = 100*y
        v = v+v
        v
    end
    yielding DMTerm
    flet scope = λ (y).{ let v = 100 in { let x = 10 * v in { let v = 100 * y in { let v = v + v in { v } } } } } in { scope }
    =#

    t = flet(:scope, DataType[Any], lam(Tuple{Symbol,DataType}[(:y, Any)], slet((:v, Any), sng(100), slet((:x, Any), op(:*, DMTerm[sng(10), var(:v, Any)]), slet((:v, Any), op(:*, DMTerm[sng(100), var(:y, Any)]), slet((:v, Any), op(:+, DMTerm[var(:v, Any), var(:v, Any)]), var(:v, Any)))))), var(:scope, Any))

    τ = Arr([(200, TVar(:op_arg_10))], TVar(:sup_23))
    @test isequal(infer_sensitivity(t), τ)
end;

@testset "simpl_capture" begin
    #=
    julia function:
        function capture(y)
            g(x) = x+2
            test(a) = b -> g(x) * a
            x = 1
            tt = test(y)
            x = 3
            tt(y)
        end
        =#

    t = flet(:capture, DataType[Any], lam(Tuple{Symbol,DataType}[(:y, Any)], flet(:g, DataType[Any], lam(Tuple{Symbol,DataType}[(:x, Any)], op(:+, DMTerm[var(:x, Any), sng(2)])), flet(:test, DataType[Any], lam(Tuple{Symbol,DataType}[(:a, Any)], lam(Tuple{Symbol,DataType}[(:b, Any)], op(:*, DMTerm[apply(var(:g, Any), DMTerm[var(:x, Any)]), var(:a, Any)]))), slet((:x, Any), sng(1), slet((:tt, Any), apply(var(:test, Any), DMTerm[var(:y, Any)]), slet((:x, Any), sng(3), apply(var(:tt, Any), DMTerm[var(:y, Any)]))))))), var(:capture, Any))

    τ = Arr([(5, TVar(:any_17))], TVar(:sup_31))
    @test isequal(infer_sensitivity(t), τ)
end;


@testset "simpl_higher_order" begin
    #=
    julia function:
    function higherorder(x)
        f(k) = k*x
        g(f1) = 2*f1(100)
        h(g1) = 2*g1(f)
        h(g)
    end
    =#

    t = flet(:higherorder, DataType[Any], lam(Tuple{Symbol,DataType}[(:x, Any)], flet(:f, DataType[Any], lam(Tuple{Symbol,DataType}[(:k, Any)], op(:*, DMTerm[var(:k, Any), var(:x, Any)])), flet(:g, DataType[Any], lam(Tuple{Symbol,DataType}[(:f1, Any)], op(:*, DMTerm[sng(2), apply(var(:f1, Any), DMTerm[sng(100)])])), flet(:h, DataType[Any], lam(Tuple{Symbol,DataType}[(:g1, Any)], op(:*, DMTerm[sng(2), apply(var(:g1, Any), DMTerm[var(:f, Any)])])), apply(var(:h, Any), DMTerm[var(:g, Any)]))))), var(:higherorder, Any))

    τ = Arr([(400,TVar(:op_arg_11))], TVar(:sup_31))
    @test isequal(infer_sensitivity(t), τ)
end;
