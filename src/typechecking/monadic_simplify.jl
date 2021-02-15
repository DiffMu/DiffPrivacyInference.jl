include("../core/DMIR.jl")
include("../core/contexts.jl")
include("../core/monads.jl")

using SimplePosets


"An error to throw upon finding a constraint that is violated."
struct ConstraintViolation <: Exception
msg::String
end

function mtry_simplify_Constr(c::Constr) :: TC#{Maybe Tuple{}}

    println("\n=== simplifying constraint $c\n")

    "If `τ` is numeric, return `()`. If it's unclear, return nothing. If it's not numeric, error."
    function check_numeric(τ::DMType) :: Union{Nothing,Tuple{}}
        @match τ begin
            TVar(_) => nothing
            DMInt() => ()
            DMReal() => ()
            #Idx(_) => ()
            Constant(τ2, a) => check_numeric(τ2)
            _ => throw(ConstraintViolation("Expected $τ to be a numeric type."));
        end
    end

    function set_or_unify(a :: SymbolOrSens, b :: Sensitivity) :: Constraints
        if a isa Symbol
            [isEqual(symbols(a),b)]
        else
            (_, co) = unify_Sensitivity_nosubs(a, b)
            co
        end
    end

    function set_or_unify(a :: SymbolOrType, b :: DMType) :: Constraints
        if a isa Symbol
            [isEqualType(TVar(a),b)]
        else
            (_, co) = unify_nosubs(a, b)
            co
        end
    end

    # This means the constraint could not be simplified.
    return_nothing() :: TC = mreturn(TC,nothing)

    # This means the constraint was successfully discharged
    # and no new constraints or substitutions apply
    return_discharge() :: TC = return_simple(Constraints())


    # This means the simplification yielded new constraints.
    function return_simple(newCs :: Constraints) :: TC
        function mconstr(S,T,C) :: MType{Tuple{}}
            filter!(x -> !isequal(x, c), C)
            C = union(C,newCs)
            (S,T,C,SCtx()), ()
        end
        TC(mconstr)
    end

    # this means it was an isEqual or isEqualType constraint, so it might have yielded new
    # constraints as well as substitutions, and we actually want to substitute.
    function return_substitute(newCs :: Constraints, σs :: Substitutions) :: TC
        @match (newCs, σs) begin
            ([],[]) => return_discharge() # they were equal to begin with, we can toss the constraint
            _ => let
                function mconstr(S,T,C) :: MType{Union{Nothing,Tuple{}}}
                    # remove c before substitute, we put it back later.
                    C_noc = Constr[cc for cc in C if !isequal(cc,c)]
                    Cs = apply_subs(C_noc,σs)

                    newCs = union(newCs, substitutions_to_constraints(σs))

                    if isequal(Cs,C_noc) && issubset(newCs, [Cs; c])
                        # substitutions did not change anything and we knew all constraints alredy -> nothing happened.
                        return (S,T,C,SCtx()), nothing
                    else
                        # don't forget to put c back
                        return (S,T,union(Cs,newCs,[c]),SCtx()), ()
                    end
                end
                TC(mconstr)
            end;
        end
    end

    @match c begin
        isEqual(s1,s2) => let
            _, co, σ = unify_Sensitivity(s1,s2)
            return_substitute(co,σ)
        end;
        isEqualType(t1, t2) => begin
            _, co, σ = unify_DMType(t1, t2)
            return_substitute(co,σ)
        end

        isLessOrEqual(s1, s2) => let
            n1 , n2 = (try_destructure_Sensitivity(s1), try_destructure_Sensitivity(s2))

            @match (n1, n2) begin
                (::EvaluatedNumber, ::EvaluatedNumber) => n1 <= n2 ? return_discharge() : throw(ConstraintViolation("exprected $n1 <= $n2"))
                (_ , _) => return_nothing()
            end
        end
        isNumeric(a) => let
            if check_numeric(a) isa Nothing
                return_nothing()
            else
                return_discharge()
            end
        end;
        isNotConstant(a) => @match a begin
            Constant(_, _) => throw(ConstraintViolation("Expected $a not to be a singleton type."))
            TVar(_) => return_nothing()
            _ => return_discharge()
        end;
        isTypeOpResult(sv, τres, op) => let #TODO clean this up
            function mconstr(S,T,C) :: MType{Union{Nothing, Tuple{}}}
                otherCs = filter!(x -> !isequal(x, c), deepcopy(C))
                res = signature((S,T,otherCs,SCtx()), op)
                if res isa Nothing
                    return (S,T,C,SCtx()), nothing
                else
                    (vs, vt, (S,T,co,Σ)) = res
                    @assert length(vs) == length(sv) "operator argument number mismatch"

                    co = [co; map(x->set_or_unify(x...), zip([sv; τres], [vs; vt]))...]

                    return ((S,T,co,Σ), ())
                end
            end
            TC(mconstr)
        end;
        isSubtypeOf(τ1, τ2) =>
        let
            function mconstr(S::SVarCtx,T::TVarCtx,C::Constraints) :: MType{Union{Nothing, Tuple{}}}
                newC = filter(c -> !isequal(c,isSubtypeOf(τ1, τ2)), C)
                res = try_eval_isSubtypeOf((S,T,newC,SCtx()), τ1, τ2)
                if isnothing(res)
                    return (S,T,C,SCtx()), nothing
                else
                    return res, ()
                end
            end
            TC(mconstr)
        end;
        isSupremumOf(τ1, τ2, ρ) =>
        let
            res = try_eval_isSupremumOf_nosubs(τ1, τ2, ρ)
            if res isa Nothing
                return_nothing()
            else
                return_simple(res)
            end

        end;
        isChoice(τ, choices) => begin
            @match τ begin
                Arr(args, _) => let
                    newchoices = Dict((s,c) for (s,c) in deepcopy(choices) if choice_could_match(args, s))

                    if isempty(newchoices)
                        error("no matching choice for $τ found in $choices.");
                    else
                        # if we don't know all types we cannot throw out more general methods, as eg for two methods
                        # (Int, Int) => T
                        # (Real, Number) => T
                        # and arg types (TVar, DMInt), both methods are in newchoices, but if we later realize the TVar
                        # is a DMReal, the first one does not match even though it's less general.
                        if all(map(t->isempty(free_TVars(t)), args)) # no free tvars in the args
                            newchoices = keep_least_general(newchoices)

                            if length(newchoices) == 1 # only one left, we can pick that one
                                return_simple(Constr[isSubtypeOf(first(values(newchoices)), τ)])
                            end
                        end

                        if length(newchoices) == length(choices)
                            return_nothing() # no choices were discarded, the constraint could not be simplified.
                        else
                            return_simple(Constr[isChoice(τ, newchoices)])
                        end
                    end
                end;
                TVar(_) => return_nothing(); #TODO in case there is only one choice, we could resolve...
                _ => error("invalid constraint: $τ cannot be a choice.")
            end
        end
    end
end

"""See if a call with argument types `args` would fit a method with signature `cs`."""
function choice_could_match(args::Vector{Tuple{Sensitivity, DMType}}, cs::Vector{<:DataType}) :: Bool
    if length(args) != length(cs)
        return false # no. of arguments differs
    else
        could_match(t,c) = t isa TVar ? true : juliatype(t) <: c
        return all(map((((_,t),c),) -> could_match(t,c), zip(args,cs)))
    end
end

#=
"""See if a call with argument types `args` would fit a method with signature `cs`."""
function choice_matches(args::Vector{Tuple{Sensitivity, DMType}}, cs::Vector{<:DataType}) :: Bool
    if length(args) != length(cs)
        return false # no. of arguments differs
    else
        τs = map(((_,t),) -> juliatype(t), args)
        return Tuple{τs...} <: Tuple{cs...}
    end
end
=#

"""Remove entries from `cs` that are supertypes of some other entry."""
function keep_least_general(cs::Dict{<:Vector{<:DataType}, Arr}) :: Dict{Vector{DataType}, Arr}
    # make a poset from the subtype relation of signatures
    P = SimplePoset(Vector{DataType})
    sign = keys(cs)
    map(((x,y),) -> add!(P,x,y), [(x,y) for x in sign for y in sign if Tuple{x...}<:Tuple{y...}])

    # pick the ones that are not supertype of any of the others
    mins = minimals(P)
    return Dict((k, cs[k]) for k in mins)
end


"""
simplify_constraints() :: TC{Tuple{}}

Evaluate all constraints that can be simplified.
"""
function msimplify_constraints() :: TC#{Tuple{}}

    extract_Cs() = TC((S,T,C) -> ((S,T,C,SCtx()), deepcopy(C)))

    # try to simplify the first constraint in Ci.
    # in case there is a simplification, recurse msimplify_constraints with the new state.
    # else pop the constraint and recurse try_simplify_constraints with the next one in Ci.
    function try_simplify_constraints(Ci::Constraints) :: TC
        if isempty(Ci)
            mreturn(TC, ())
        else
            @mdo TC begin
                simpl <- mtry_simplify_Constr(Ci[1])
                ret <- (isnothing(simpl) ? try_simplify_constraints(Ci[2:end]) : msimplify_constraints())
                return ret
            end
        end
    end

    @mdo TC begin
        Cs <- extract_Cs()
        _ <-mreturn(println("---------> simplifying constraints $Cs\n\n"))
        _ <- try_simplify_constraints(Cs) # see if the constraints changed. recurse, if so.
        return ()
    end
end

"""Apply all substitutions encoded in the constraints of the TC monad `m` to the DMType `τ`."""
function apply_subs(τ::DMType, m::TC) :: TC
    function mconstr(S,T,C) :: MType{DMType}
        (S,T,C,Σ), _ = m.func(S,T,C)
        for c in C
            τ = @match c begin
                isEqual(s1, s2) => let
                    _, _, σ = unify_Sensitivity(s1, s2)
                    apply_subs(τ, σ)
                end
                isEqualType(t1, t2) => let
                    _, _, σ = unify_DMType(t1, t2)
                    apply_subs(τ, σ)
                end
                _ => τ;
            end
        end
        return (S,T,C,Σ), τ
    end
    TC(mconstr)
end
