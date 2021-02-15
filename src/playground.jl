
#############################################################
# Test here

include("parsing/parse.jl")
include("typechecking/typecheck.jl")
include("typechecking/simplify.jl")
include("typechecking/lose_generality.jl")
include("utils/logging.jl")

#Arr(Tuple{Union{Number, SymbolicUtils.Sym, SymbolicUtils.Term},DMType}[(6, TVar(:any_0))], DMReal())))
function add2(x)
    2*(x+x+x)
end

# Arr(Tuple{Union{Number, SymbolicUtils.Sym, SymbolicUtils.Term},DMType}[(12, DMInt())], DMReal())))
function call_add22(y::Int)
    add2(y+y)
end

# Arr(Tuple{Basic,DMType}[(0, TVar(:any_0)), (0, TVar(:any_1)), (0, TVar(:any_2))], Constant(DMInt(), 10))
cons(x,y,z) = 10

#[(0.3333333333333333, TVar(:any_0)), (3 + (2 * ∞), TVar(:any_1)), (7, TVar(:any_2)), (∞, TVar(:any_3))], DMReal())))
arith(w,x,y,z) = 3*(x+y) - z*ceil(x) + ceil(y) % 4 - 3/x + w/3

# Arr(Tuple{Basic,DMType}[(∞, TVar(:any_0)), (∞, TVar(:any_1))], DMReal())
div(x,y) = x/y

# Arr(Tuple{Basic,DMType}[(0, TVar(:any_0)), (0, TVar(:any_1))], Constant(DMInt(), 30))
sub(x,y) = 33-3

# Arr(Tuple{Union{Number, SymbolicUtils.Sym, SymbolicUtils.Term},DMType}[(1, TVar(:any_0))], TVar(:any_0))))
function apply_lam(x)
    ((a,b) -> a)(x, (z->z)(x))
end

function apply_ifun(x)
    g(a,b) = a
    f(z) = z
    g(x, f(x))
end

# Arr(Tuple{Basic,DMType}[(∞, TVar(:any_1)), (∞, TVar(:any_1))], DMInt())
function conds(a, b)
    if(a == b)
        return 1
    else
        return 2
    end
end

# Computing the supremum of Constant(Int, 1) and Constant(Real, 2.3)
# Arr(Tuple{Basic,DMType}[(∞, TVar(:any_0)), (∞, TVar(:any_1))], DMReal())
function condsd(a, b)
    if(a == b)
        return 1
    else
        return 2.3
    end
end

# TODO why is the last one a real?
# Arr(Tuple{Basic,DMType}[(∞, TVar(:any_0)), (∞, TVar(:any_1)), (1, TVar(:any_2)), (2, DMReal())], DMReal())
function cond4(a, b, c, d)
    if(a == b)
        return c+d
    else
        return d
    end
end

function condi(a,b)
    x = 4
    if a == b
        x = a+a # error here.
        if x == b
            return x+b
        end
    else
        x += b
    end
    return x
end



# TODO allow multimethod inner functions?
function innerf(x)
    x += 1
    g(b) = b+100
    g(b,s) = b+s+100
    g(x)
end

function innermod(x)
    x += 1
    function g(b)
        x += t # error here
        return b+100
    end
    g(x)
end

function innerlmod(x)
    x += 1
    ((b) -> begin
        x += t # error here
        return b+100
    end)(x)
    x
end

# TODO parser is broken...
function innerscope(x)
    x += 1
    function g(y)
        return x+100
    end
    g(x + 10)
end

# TODO parser does not find the illegal modification!
function loopillegal(a)
    it = 1:a
    for i in it
        if i == 12
           a += i*a
       else
           a *= a
       end
    end
    return a
end

#TODO Arr(Tuple{Basic,DMType}[(∞, DMInt()), (∞, DMInt())], DMInt())
# this is very pessimistic...
function innercap(x,y)
    x += 1
    k = 10
    (b->return b*y+k+100)(x)
end

function rec(a)
    if(a==1)
        return 1
    else
        return rec(a-1)+10 # error here
    end
end

function rec2(a)
    if(a==10)
        return a
    else
        return rec(a) # error here
    end
end

function rec3(a)
    if(a==4)
        return a-1
    else
        return rec2(a) # error here
    end
end

# Arr(Tuple{Basic,DMType}[(6, TVar(:any_0)), (3, TVar(:any_0))], DMVec(3, TVar(:any_0)))
function vectc(a, b)
    v = [a,a,b]
    return v
end

# Arr(Tuple{Basic,DMType}[(12, TVar(:vecelem_5)), (4, TVar(:vecelem_5))], TVar(:vecelem_5))
function vectind(a, b)
    v = [a,a,a,b]
    return v[2]
end

# TODO implement len
function loopivec(a)
    x,y = (1, a*18)
    for i in [1,3,5,6,8, a, a]
        x += 2*i
    end
    return x+y
end

#TODO same
function loopi2(a,b)
    x,y = (b + 1, a*18)
    for i in [1,3,5,6,8]
        x += 2*i
        bla = 0
        for j in 2:4, k in 1:10
            y += k + bla
            x += j
        end
    end
    return x+y
end

function loopsimple(a)
    for i in 1:10
        a = i
    end
    return a
end

# Arr(Tuple{Union{Number, SymbolicUtils.Sym, SymbolicUtils.Term},DMType}[(1.0, DMInt()), (1.0, DMInt())], DMInt())))
function loopsimple2(a,b)
    for i in 1:10
        b = i+a
        a = i
    end
    return a
end

# Arr(Tuple{Union{Number, SymbolicUtils.Sym, SymbolicUtils.Term},DMType}[(1.0, DMReal())], DMReal())))
function loopsimplem(a)
    for i in 1:2:10
        a += i
    end
    return a
end

#Arr(Tuple{Union{Number, SymbolicUtils.Sym, SymbolicUtils.Term},DMType}[(1.073741824e9, DMReal())], DMReal())))
function loopdouble(a)
    for j in 2:4, i in 1:10
        a += j + i
    end
    return a
end

# TODO implement len
function looptest(a::Int64)
    for j in 2:4, i in 1:2:5
        g(x) = j + x + x + 5
        a += j + i
        for k in [1,3,i,j]
            if i+j+k == 4
                a += g(k)
            else
                a += g(k) + i
            end
        end
    end
    return a
end


function cap_test2()
    test(a) = b -> x + a
    x = 1
    tt = test(1)
    x = 3
    tt(1)
end

function cap_test3()
    y = 9
    x = 3
    x = 4
    y
end

function testingpoly(f)
    return f(4) + f(3.1)
end

using CodeTracking
function test_all(f::Function)
    code = ""
    for m in methods(f).ms
        code *= definition(String, m)[1] * "\n"
    end
    file, line = functionloc(f)
    t = string_to_dmterm(code, LineNumberNode(Int64(line), file))
    println("\n\n======== term parsed:\n$t\n\n")
    test_all(t)
end


# make variable (ie, in lambda)
function mvar(s :: String) :: TAsgmt
    Symbol(s), DMDUnknown()
end

# use variable (ie, in the term)
function uvar(s :: String) :: DMTerm
    var(Symbol(s), DMDUnknown())
end

# Testing lets
testlet = lam(TAsgmt[mvar("a"), mvar("b")], tup(DMTerm[(op(+, [uvar("a"), uvar("b")])), uvar("b")]))
testlet2 = lam([mvar("x")], tlet([mvar("y"), mvar("z")], uvar("x"), tup([op(+, [uvar("y"), uvar("y")])
                                                                            , op(+, [uvar("z"), uvar("z")])])))
testlet3 = lam([mvar("a"),mvar("b")], apply(testlet2, [apply(testlet, [uvar("a"), uvar("b")])]))

testlet4 = lam([mvar("a"),mvar("b")], tlet([mvar("x0"), mvar("x1")],
                                             apply(testlet3, [uvar("a"), uvar("b")]),
                                             op(+, [uvar("x0"), uvar("x1")])))

testtup = lam(TAsgmt[mvar("a")], tlet([mvar("x"), mvar("y")], uvar("a"), op(+, [op(+, [uvar("x"), uvar("y")]), uvar("y")])))
testtup2 = lam(TAsgmt[mvar("a")], apply(testtup, [tup(DMTerm[sng(1), uvar("a")])]))

# Testing flets
tflet1 = flet(Symbol("f1"), lam([mvar("x")],
                                uvar("x")),
              flet(Symbol("f2"), lam([mvar("a"), mvar("b")],
                                     apply(uvar("f1"), [uvar("a")])),
                   flet(Symbol("f2"), lam([mvar("a")],
                                          sng(1.4)),
                        apply(uvar("f2"), [sng(2), sng(3)]) # calling first instance
                        )))

tflet2 = flet(Symbol("f1"), lam([mvar("x")],
                                uvar("x")),
              flet(Symbol("f2"), lam([mvar("a"), mvar("b")],
                                     apply(uvar("f1"), [uvar("a")])),
                   flet(Symbol("f2"), lam([mvar("a")],
                                          sng(1.4)),
                        apply(uvar("f2"), [sng(2)]) # calling second instance
                        )))

breaks_choices_1 = flet(:add2, lam(Tuple{Symbol,DMDispatch}[(:x, DMDInt())], op(*, DMTerm[sng(2), op(+, DMTerm[var(:x, DMDUnknown()), var(:x, DMDUnknown())])])), flet(:add2, lam(Tuple{Symbol,DMDispatch}[(:x, DMDUnknown())], op(*, DMTerm[sng(2), op(+, DMTerm[op(+, DMTerm[var(:x, DMDUnknown()), var(:x, DMDUnknown())]), var(:x, DMDUnknown())])])), flet(:call_add22, lam(Tuple{Symbol,DMDispatch}[(:y, DMDInt())], apply(var(:add2, DMDUnknown()), DMTerm[op(+, DMTerm[var(:y, DMDUnknown()), var(:y, DMDUnknown())])])), apply(var(:call_add22, DMDUnknown()), [sng(3)]))))

# flets without full abstraction:
t_no_forall = flet(Symbol("f1"), lam([mvar("x")],
                                     uvar("x")),
                   op(+, [apply(uvar("f1"), [sng(1)]), apply(uvar("f1"), [sng(1.4)])]))

t_with_forall = flet(Symbol("f1"), abstr(lam([mvar("x")],
                                             uvar("x"))),
                     op(+, [apply(uvar("f1"), [sng(1)]), apply(uvar("f1"), [sng(1.4)])]))

t_with_forall2 = flet(Symbol("f1"), abstr(lam([mvar("x"),mvar("y")],
                                              uvar("y"))),
                      lam([mvar("a")],op(+, [apply(uvar("f1"), [sng(1),uvar("a")]), apply(uvar("f1"), [sng(1.4),uvar("a")])])))

# applying the same id function to different vars
# Recursive subtyping constraints => infinite loop
forall_t2 = slet((Symbol("f1"),DMDUnknown()), abstr(lam([mvar("x")],
                                                        uvar("x"))),
                 lam([mvar("a")], apply(apply(uvar("f1"),[uvar("f1")]),[uvar("a")])))
                 # op(+, [apply(uvar("f1"), [sng(1)]), apply(uvar("f1"), [sng(1.4)])]))


function test_all(t::DMTerm)
    G, tau = check_sens(t)
    println("\n\n======== term checked:\n$G\n$tau\n\n")
    G, tau = simplify_constraints(G, tau)
    println("\n\n======== constraints evaluated:\n$G\n$tau\n\n")
    G, tau = simplify_constraints_lose_generality(G, tau)
    println("\n\n======== constraints simplified:\n$G\n$tau\n\n")
    return G, tau
end

global global_LogCategories = Set([Log_TypecheckPhases(), Log_SubstitutionDetails(), Log_ResolveCaptures(), Log_ResolveCapturesSubstitutions()])
# test_all(cap_test3)

# r1 = test_all(tflet1)

#############################################################
# Test here
#=
anyvar(x) = var(x, DMDUnknown())

# t1 = lam_star([(:a , Native(Any))] , ret(anyvar(:a)))
# t2 = lam((:b, Native(Int)), t1)
t3 = lam([(:x, DMDInt())], lam([(:y, DMDInt())], op(+, [anyvar(:x), op(+, [anyvar(:x), anyvar(:y)])])))
t4 = lam([(:x, DMDInt()), (:y, DMDInt())], op(+, [anyvar(:x), op(+, [anyvar(:x), anyvar(:y)])]))

t5 = lam([(:x, DMDUnknown()), (:y, DMDUnknown())], lam([], op(*, [anyvar(:x), op(+, [anyvar(:x), anyvar(:y)])])))
t5_ = lam([(:x, DMDUnknown()), (:y, DMDUnknown())], lam([], op(*, [op(*, [anyvar(:x), anyvar(:x)]), op(+, [anyvar(:x), anyvar(:y)])])))
t6 = apply(t5_, [sng(3), sng(4)])
t7 = lam([(:z, DMDUnknown()), (:a, DMDUnknown())], apply(t5, [anyvar(:z), anyvar(:z)]))

tfi = lam([(:x, DMDUnknown()), (:y, DMDUnknown())], phi(op(==, [anyvar(:x), anyvar(:y)]), t7, t6))

fci = tfi

println("------------------------")

println("term: ",fci)

Γ , τ, _ = check_sens((emptySVarCtx(),emptyTVarCtx(),emptyConstraints(),TypeContext()), fci)
println("------------------------")
println("Type: $τ")

println("------------------------")
println("Context: $Γ")

Γ2, τ2 = evaluateConstraints(Γ, τ)
println("------------------------")
println("reduced context: $Γ2")
println("reduced type: $τ2")

#Γ3, τ3 = simplifyConstraints_LoseGenerality(Γ2, τ2)
#println("------------------------")
#println("simplified (heuristically) context: $Γ3")
#println("simplified (heuristically) type: $τ3")
=#
