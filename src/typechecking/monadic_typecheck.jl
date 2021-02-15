include("../core/DMIR.jl")
include("../core/contexts.jl")
include("../core/monads.jl")
include("../core/unification.jl")
include("../typechecking/subtyping.jl")


function add_op(opf::Function, nargs::Int) :: TC#{Tuple{DMType, Vector{DMType}, Vector{Sensitivity}}}
    function mconstr(S,T,C) :: MType{Tuple{DMType, Vector{DMType}, Vector{Sensitivity}}}
        function makeType()
            T, tv = addNewName(T, Symbol("op_arg_"))
            TVar(tv)
        end
        τs = [makeType() for _ in 1:nargs]
        dmop = getDMOp(opf)(τs)
        (S,T,C), τ, sv = add_TypeOp((S,T,C), dmop)
        ((S,T,C,SCtx()), (τ, τs, sv))
    end
    TC(mconstr)
end

function unify(τ1::DMType, τ2::DMType) :: TC#{DMType}
    function mconstr(S,T,C) :: MType{DMType}
        τ, nC = unify_nosubs(τ1, τ2)
        C = [C; nC]
        (S,T,C,SCtx()), τ
    end
    TC(mconstr)
end

function subtype_of(τ1::DMType, τ2::DMType) :: TC#{Nothing}
    function mconstr(S,T,C) :: MType{Nothing}
        C = [C; isSubtypeOf(τ1, τ2)]
        (S,T,C,SCtx()), nothing
    end
    TC(mconstr)
end

function add_Cs(Cs::Constraints) :: TC
    function mconstr(S,T,C) :: MType{Tuple{}}
        (S,T,union(C,Cs), SCtx()), ()
    end
    TC(mconstr)
end

scale(s, m::TC) :: TC = apply_sctx(Σ -> scale(s, Σ), m)

# delete x/xs from m's context
# careful, this executes the monad.
remove_var(x::Symbol, m::TC) :: TC = apply_sctx(((S,T,C,Σ),) -> (S,T,C,delete!(deepcopy(Σ), x)), m)
remove_vars(xs::Vector{Symbol}, m::TC) :: TC = foldr((x, mx) -> remove_var(x, mx), xs, init=m)


# return the type of the variable x, or nothing if it's not in the monad's scope.
function lookup_var_type(x::Symbol, m::TC) :: TC#{Maybe DMType}
    function mconstr(S,T,C) :: MType{Union{DMType, Nothing}}
        (S,T,C,Σ), τ = m.func(S,T,C)

        (S,T,C,Σ), haskey(Σ, x) ? Σ[x][2] : nothing
    end
    TC(mconstr)
end


# look up the types and sensitivities of the xs from m's context
# if it does not have one (this means it was not used in the lambda body),
# create a new type/typevar according to type hint given in xs
# then remove the xs from Σ
function get_arglist(xτs::Vector{<:TAsgmt}, m::TC) :: TC#{Vect{DMType x Sens} x A} where m::TC{DMType}
    function mconstr(S,T,C) :: MType
        (S,T,C,Σ), τ = m.func(S,T,C)

        function make_type(dτ::DataType)
            # if the type hint is DMDUnkown, we just add a typevar. otherwise we can be more specific
            τx, S, T, C = create_DMType(dτ, S, T, C)
            (0, τx)
        end

        nxτs = [haskey(Σ, x) ? Σ[x] : make_type(τx) for (x,τx) in xτs]
        for (x,_) in xτs
            if haskey(Σ,x)
                delete!(Σ, x)
            end
        end
        (S,T,C,Σ), (nxτs ,τ)
    end
    TC(mconstr)
end


# just an empty context and a new type, made by calling make_type::NameCtx => NameCtx x DMType
function add_type(make_type::Function) :: TC#{DMType}
    function mconstr(S,T,C) :: MType
        T, τ = make_type(T)

        (S,T,C,SCtx()), τ
    end
    TC(mconstr)
end

function add_svar() :: TC#{Sensitivity}
    function mconstr(S,T,C) :: MType
        S, s = addNewName(S, Symbol("sens_"))
        s = symbols(s)

        (S,T,C,SCtx()), s
    end
    TC(mconstr)
end

function mcreate_DMType(dτ::DataType)
    function mconstr(S,T,C) :: MType{DMType}
        # if the type hint is DMDUnkown, we just add a typevar. otherwise we can be more specific
        τ, S, T, C = create_DMType(dτ, S, T, C)
        (S,T,C,SCtx()), τ
    end
    TC(mconstr)
end


function mcheck_sens(t::DMTerm, scope::Dict{Symbol, Vector{DMTerm}}) :: TC#{DMType}

    println("checking $t, scope $scope\n")

    #=
    # make a sensitivity context where all variables in scope have sensitivity 0
    function zero_context(T, names)
        # a new type var for everything in scope. TODO can we do this differently?
        function make_type(name)
            T, tv = addNewName(T, Symbol("$name", "_"))
            TVar(tv)
        end
        # they all get sensitivity 0
        Σ = SCtx(i => (0, make_type(i)) for i in names)
        T, Σ
    end
    =#


    result = @match t begin
        sng(n) => let
            # maybe n actually is a constant. get n's type
            function make_type(T)
                T, τ = @match n begin
                    ::Int => (T, DMInt())
                    ::Real => (T, DMReal())
                    _ => add_new_type(T, Symbol(n))
                end;
                T, Constant(τ, n)
            end
            add_type(make_type)
        end;

        lam(xτs, body) => let
            scope = deepcopy(scope)

            for (x,τ) in xτs
                # put a special term to memorize the type signature
                scope[x] = [arg(τ)]
            end

            @mdo TC begin
                (xrτs, r) <- get_arglist(xτs, mcheck_sens(body, scope))
                return Arr(xrτs, r)
            end

        end

        flet(f, s, l, b) => let

            scope = deepcopy(scope)

            present = haskey(scope,f)

            if present
                println("---found additional choice $s for $f")
                choice = @match scope[f] begin
                    [chce(Cs)] => Cs;
                    _ => "error invalid term for choice $f: $(scope[f])"
                end
                choice[s] = l # add choice entry with the term l for this signature s
            else
                println("---found choice $s for $f")
                scope[f] = [chce(Dict(s => l))] # make a new scope entry for f with only one choice
            end

            # check the body
            result = mcheck_sens(b, scope)

            # remove f from the return context
            present ? result : remove_var(f, result) #TODO really??
        end;

        chce(Cs) => let # a special term for storing choices, can only appear during typechecking (not from parsing)

            println("checking choices $Cs")
            # check a single choice, append the resulting (Sensitivity, DMType, Constraints) tuple to sτs
            function check_choice(sτs, (sign,choice)::Pair{Vector{<:DataType}, DMTerm}) :: TC#{Vector{DMTerm}}
                println("-------single $choice with $sτs")
                @mdo TC begin
                    τ_choice <- mcheck_sens(choice, scope)
                    return [sτs..., (sign, τ_choice)]
                end
            end

            println("checking choices $Cs")
            # check all choices, collect result in a DMChoice type.
            @mdo TC begin
                sτs <- mloop(check_choice, Cs, mreturn(Tuple{Vector{<:DataType}, Arr}[]))
                τ <- add_type(T -> add_new_type(T, :chce)) # create a tvar for the choice type
                _ <- add_Cs(Constraints([isChoice(τ, Dict(sτs))]))
                return τ
            end
        end;

        slet((v, dτ), t, b) => let

            # we're very lazy, only adding the new term for v to its scope entry
            scope = deepcopy(scope)
            present = haskey(scope,v)
            present ? push!(scope[v], t) : scope[v] = [t]

            # check the body
            M = mcheck_sens(b, scope)

            # unify inferred type of v with user-annotated type dτ
            result = @mdo TC begin
                τ <- M
                τv <- lookup_var_type(v, M)
                dτd <- mcreate_DMType(dτ)
                _ <- (isnothing(τv) ? nothing : subtype_of(τv, dτd))
                return τ
            end

            # remove v from the return context
            # if it was present we need to keep it in the scope:
            # x = y
            # x = x+x
            # x
            # should be 2-sensitive in x.
            present ? result : remove_var(v, result) #TODO really??
        end;

        var(x,dτ) => let
            # set sensitivity of x to 1 and type to τ. all other vars in scope get sensitivity 0
            function set_var(x::Symbol, s, τ::DMType) :: TC#{DMType} # make_type :: T -> (T, τ)
                function mconstr(S,T,C) :: MType
                    # only x gets sensitivity 1, and the inferred type
                    Σ = SCtx(x => (s,τ))

                    (S,T,C,Σ), τ
                end
                TC(mconstr)
            end

            if haskey(scope, x)
                scope = deepcopy(scope)
                # get the term that corresponds to this variable
                vt = @match scope[x] begin
                    [t] => let
                        delete!(scope, x)
                        t
                    end;
                    ts => pop!(scope[x]) # x was overwritten at some point; we take the most recent term.
                end

                @mdo TC begin
                    τ <- mcheck_sens(vt, scope) # check the term
                    τ <- set_var(x, 1, τ) # set sensitivity = 1 and type = τ for x
                    dτd <- mcreate_DMType(dτ) # unify with the user-annotated type
                    _ <- subtype_of(τ, dτd)
                    return τ
                end

            else
                error("Variable $x not in scope!")
            end
        end;

        arg(dτ) => let # a special term recording user-given function argument types (τ :: DataType)
            mcreate_DMType(dτ)
        end;

        op(opf, args) => let

            # handle a single argument. τ and s are the typevar and sensitivity scalar
            # belonging to this arg, as assigned to by the typeOp.
            # ghost argument is so we can plug it into mloop. it will discard the types
            # and just remember the result context
            function check_op_arg(_, (arg, τ, s)::Tuple{DMTerm, DMType, Sensitivity}) :: TC
                @mdo TC begin
                    τ_arg <- scale(s, mcheck_sens(arg, scope)) # check term and scale
                    τ_arg <- unify(τ_arg, τ) # unify with type from the typeOp
                    return τ_arg
                end
            end

            nargs = length(args)

            # add typeop, loop check_op_arg over all arguments
            @mdo TC begin
                (τ_res, τs, vs) <- add_op(opf, nargs)
                n <- mloop(check_op_arg, zip(args,τs,vs), mreturn(τ_res))
                return τ_res
            end
        end;

        apply(f, args) => let

            # check a single argument, append the resulting (Sensitivity, DMType) tuple to sτs
            function check_arg(sτs, arg::DMTerm) :: TC
                @mdo TC begin
                    s <- add_svar() # add a new svar for this argument's sensitivity
                    τ_res <- scale(s, mcheck_sens(arg, scope))
                    sτs <- fmap(t -> push!(Any[sτs...], (s, t)), mreturn(τ_res)) # check term, scale, and push to array
                    return sτs
                end
            end

            @mdo TC begin
                sτs_args <- mloop(check_arg, args, mreturn([])) # check args, compute result context
                τ_ret <- add_type(T -> add_new_type(T, :ret)) # create a tvar for the return type
                τ_lam <- mcheck_sens(f, scope) # check the function
                n <- subtype_of(τ_lam, Arr(sτs_args,τ_ret))
                return τ_ret
            end
        end;

        _ => error("something unsupported: $t")

    end

    println("done checking $t\n")

    result

end

mcheck(t::DMTerm) = mcheck_sens(t, Dict{Symbol, Vector{DMTerm}}()).func((emptySVarCtx(),emptyTVarCtx(),emptyConstraints(),TypeContext()))

# just for testing
include("monadic_simplify.jl")
#include("lose_generality.jl")
function mtest_all(t::DMTerm)
     G, τ, _ = mcheck_sens(t, Dict{Symbol, Vector{DMTerm}}()).func((emptySVarCtx(),emptyTVarCtx(),emptyConstraints(),TypeContext()))
    println("\n\n======== term checked:\n$G\n$τ\n\n")
    G, τ = simplify_constraints(G, τ)
    println("\n\n======== constraints evaluated:\n$G\n$τ\n\n")
#    G, τ = simplify_constraints_lose_generality(G, τ)
    println("\n\n======== constraints simplified:\n$G\n$τ\n\n")
    G, τ
end

