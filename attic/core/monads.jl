
import Base.==

#########################################################################################
# monads

abstract type Monad end

## Extra combinators
mthen(k::Monad, m::Monad) = mbind(_ -> k, m)
(==)(m::Monad, k::Monad) = m.value == k.value

## Friendly monad blocks/mdo
macro mdo(mtype, body)
    #println("mdo says: ",esc(mdo_desugar(mdo_patch(mtype, deepcopy(body)))))
    esc(mdo_desugar(mdo_patch(mtype, body)))
end

## patch up functions to insert the right monad
mdo_patch(mtype, expr) = expr
function mdo_patch(mtype, expr::Expr)
    expr.args = map(arg->mdo_patch(mtype, arg), expr.args)
    # replace return with call to mreturn
    if expr.head == :return
        expr.head = :call
        insert!(expr.args, 1, :mreturn)
    end
    if expr.head == :call && any(expr.args[1] .== [:mreturn, :mzero, :guard, :liftM])
        insert!(expr.args, 2, mtype)
    end
    expr
end

## desugaring mdo syntax is a right fold
mdo_desugar(exprIn) = foldr(mdo_desugar_helper, exprIn.args)
mdo_desugar_helper(expr, rest) = rest
function mdo_desugar_helper(expr::Expr, rest)
    if (expr.head == :call
      && expr.args[1] == Symbol("<")
        && expr.args[3].args[1] == Symbol("-"))
        # replace "<-" with monadic binding
        newExpr = expr.args[3].args[2:end];
        quote
            mbind($(newExpr...)) do $(expr.args[2])
                $rest
            end
        end
    elseif expr.head == :(=)
        # replace assignment with let binding
        quote
            let
                $expr
                $rest
            end
        end
    elseif expr.head == :line
        rest
    elseif rest == :()
        expr
    else
        # replace with sequencing
        :(mthen($rest, $expr))
    end
end

# fmap(f::Function, m::M) where {M<:Monad} = mbind(x->mreturn(M, f(x)), m)


#########################################################################################
# type context state monad

# TC has a hidden type parameter A that i cannot express. i use MType{A} as a cheap substitute...
struct TC <: Monad
func :: Function # (Full{Ctx}) -> (Full{Ctx} x A)
end

MType{A} = Tuple{Full, A}

# execute the computation within a TC monad.
run(m::TC) = m.func(emptySVarCtx(),emptyTVarCtx(),emptyConstraints(),SCtx())

# bind just passes the result context of executing m on into f(τ)
function mbind(f::Function, m::TC) :: TC # f :: A -> TC{B}
    function mconstr(S,T,C,Σ) :: MType # it's actually MType{B}
        # TODO func should not be modifying Σ, but deepcopy just in case...
        (S,T,C,Σm), τm = m.func(S,T,C,deepcopy(Σ))
        return f(τm).func(S,T,C,Σm)
    end
    TC(mconstr)
end

# map f over as, returning the collected results.
# mapM ::(a -> m b) -> [a] -> m [b]
function mapM(f::Function, as::Vector) :: TC#{Vector}
    function k(a, r)
        @mdo TC begin
            x <- f(a)
            xs <- r
            return [x; xs]
        end
    end
    return foldr(k, [as; mreturn(TC, [])])
end

# map f over as, returning the collected results.
# mapM ::(a -> m b) -> (a) -> m (b)
function mapM(f::Function, as::Tuple) :: TC#{Tuple}
    @mdo TC begin
        res <- mapM(f, [as...])
        return (res...,)
    end
end

# execute all monads in args seperately with the same input Σ, only passing on S,T,C
# then sum the resulting contexts and return execution results as a vector
function msum(args::Vector{TC}) :: TC#{Vector}
    function mconstr(S,T,C,Σ) :: MType{Vector}
        (S,T,C,Σ1), τ = args[1].func(S,T,C,deepcopy(Σ))
        τs = Any[τ]
        for arg in args[2:end]
             # TODO func should not be modifying Σ, but deepcopy just in case...
            (S,T,C,Σ2), τ = arg.func(S,T,C,deepcopy(Σ))
            τs = push!(τs, τ)
            (S,T,C,Σ1) = add(S,T,C,Σ1,Σ2)
        end
        return (S,T,C,Σ1), τs
    end
    TC(mconstr)
end

# msum args, return execution results as tuple
function msum(args::TC...) :: TC#{Tuple}
    @mdo TC begin
        sum <- msum([args...])
        return (sum...,)
    end
end

# this must satisfy mbind(mreturn, M) = M
function mreturn(::Type{TC}, val) :: TC # A -> TC{A}
    @assert !(val isa Monad) "are you sure you want to return the monad $val?"

    TC((S,T,C,Σ) -> ((S,T,C,Σ), val))
end

#########################################################################################
# convenience functions for TC monad

mtruncate(s::Annotation) = TC((S,T,C,Σ) -> ((S,T,C,truncate(Σ, s)), ()))
mtruncate_restrict(vars::Vector{Symbol}, s::Annotation) = TC((S,T,C,Σ) -> ((S,T,C,truncate(restrict(Σ, vars), s)), ()))
mcomplement(vars::Vector{Symbol}) = TC((S,T,C,Σ) -> ((S,T,C,complement(Σ, vars)), ()))

"Construct a `TC` monad containing the computation of inferring `t`'s sensitivity."
function build_tc(t::DMTerm) :: TC
    @mdo TC begin
        checkr <- check_term(t) # typecheck the term
        _ = println("type after check: $checkr")
        tau <- simplify_constraints_lose_generality() # simplify all constraints
        _ = println("type after simpl: $checkr")
        r <- apply_subs(checkr) # apply substitutions made during simplification
        _ = println("type after subs: $r")
        return r
    end
end

function check_nosim(t::DMTerm)
    m = @mdo TC begin
        checkr <- check_term(t) # typecheck the term
        _ = println("type after check: $checkr")
        _ <- mprint()
        return nothing
    end
    run(m)
end

"Add a `DMTypeOp` constraint for the  `nargs`-ary operation accoding to `opf`."
function add_op(opf::Symbol) :: TC#{Tuple{DMType, Vector{DMType}, Vector{Sensitivity}}}
    function mconstr(S,T,C,Σ) :: MType{Tuple{DMType, Vector{DMType}, Vector{Sensitivity}}}
        function makeType(i::Int)
            T, tv = addNewName(T, Symbol("op$(opf)$(i)_arg_"))
            TVar(tv)
        end
        nargs, dmop = getDMOp(opf)
        τs = [makeType(i) for i in 1:nargs]
        (S,T,C), τ, sv = add_TypeOp((S,T,C), dmop(τs))
        ((S,T,C,Σ), (τ, τs, sv))
    end
    TC(mconstr)
end

"Unify `DMTypes` `τ1` and `τ2` within a `TC` monad."
function unify(τ1::DMType, τ2::DMType) :: TC#{DMType}
    function mconstr(S,T,C,Σ) :: MType{DMType}
        τ, nC = unify_nosubs(τ1, τ2)
        C = [C; nC]
        (S,T,C,Σ), τ
    end
    TC(mconstr)
end

"Add a subtype constraint `τ1 ⊑ τ2` to the monad's constraint list."
subtype_of(τ1::DMType, τ2::DMType) = TC((S,T,C,Σ) -> ((S,T,union(C, [isSubtypeOf(τ1, τ2)]),Σ), ()))

"Get the supremum of `τ1` and `τ2`, without simplifying constraints."
msupremum(τ1 :: DMType, τ2 :: DMType) = TC((S,T,C,Σ) -> getSupremumOf((S,T,C,Σ), τ1, τ2))


"Return the current constraint list."
extract_Cs() = TC((S,T,C,Σ) -> ((S,T,C,Σ), deepcopy(C)))

"Add the given constraints to the monad's constraint list."
function add_Cs(Cs::Constraints) :: TC
    function mconstr(S,T,C,Σ) :: MType{Tuple{}}
        (S,T,union(C,Cs),Σ), ()
    end
    TC(mconstr)
end

function mprint() :: TC
    function mconstr(S,T,C,Σ) :: MType{Nothing}
        println("monad content:\nS:\n$S\nT:\n$T\n:C\n$C\nΣ:\n$Σ\n\n")
        (S,T,C,Σ), nothing
    end
    TC(mconstr)
end



"Convert a given julia type into a `DMType` and return it."
function mcreate_DMType(dτ::DataType) :: TC
    function mconstr(S,T,C,Σ) :: MType{DMType}
        # if the type hint is DMDUnkown, we just add a typevar. otherwise we can be more specific
        τ, S, T, C = create_DMType(dτ, S, T, C)
        (S,T,C,Σ), τ
    end
    TC(mconstr)
end

"Scale a TC Monad's sensitivity context by `s`."
mscale(s) = TC((S,T,C,Σ) -> ((S,T,C,scale(s,deepcopy(Σ))), ()))

"""
   add_type(make_type::Function) :: TC

Add a newly created typevar to the monad's type variable context `T`, made by calling
`make_type::TVarCtx => TVarCtx x DMType`. Return the new type.
"""
function add_type(make_type::Function) :: TC#{DMType}
    function mconstr(S,T,C,Σ) :: MType{DMType}
        T, τ = make_type(T)

        (S,T,C,Σ), τ
    end
    TC(mconstr)
end

function add_var(sym, prefix::String) :: TC#{Sensitivity}
    function mconstr(S,T,C,Σ) :: MType{Sensitivity}
        S, s = addNewName(S, Symbol(prefix))
        s = sym(s)

        (S,T,C,Σ), s
    end
    TC(mconstr)
end

"Add a newly created sensitivity variable to the monad's sensitivity variable context `S` and return it."
add_svar(name = "sens_") = add_var(symbols,name)
add_nvar() = add_var(SymbolicUtils.Sym{Norm},"norm_")
add_cvar() = add_var(SymbolicUtils.Sym{Clip},"clip_")

"Set annotation of `x` to `s` and type to `τ`."
function set_var(x::Symbol, s::Annotation, τ::DMType, i=true) :: TC#{DMType}
    function mconstr(S,T,C,Σ) :: MType{DMType}
        Σ = deepcopy(Σ)
        # x gets annotation s type τ
        Σ[x] = (s,τ,i)
        (S,T,C,Σ), τ
    end
    TC(mconstr)
end

"Set annotation of `x` to `s`."
function set_annotation(x::Symbol, s::Annotation) :: TC#{DMType}
    function mconstr(S,T,C,Σ) :: MType{DMType}
        Σ = deepcopy(Σ)
        # x gets annotation s type τ
        if haskey(Σ, x)
            (_, τ, i) = Σ[x]
        else
            T,τ = make_type(T)
        end
        Σ[x] = (s,τ,i)
        (S,T,C,Σ), τ
    end
    TC(mconstr)
end



"Delete `x` from the current context and return it's former annotation and type."
function remove_var(x::Symbol) :: TC
    function mconstr(S,T,C,Σ) :: MType{Tuple{Annotation, DMType, Bool}}
        if haskey(Σ,x)
            r = Σ[x]
        else
            T, τ = add_new_type(T,:unused_)
            r = (0, τ, true)
        end
        (S,T,C,delete!(deepcopy(Σ), x)), r
    end
    TC(mconstr)
end

"Return variable `x`'s current sensitivity."
lookup_var_sens(x::Symbol) = TC((S,T,C,Σ) -> ((S,T,C,Σ), haskey(Σ,x) ? Σ[x][1] : nothing))

"Return variable `x`'s current type."
lookup_var_type(x::Symbol) = TC((S,T,C,Σ) -> ((S,T,C,Σ), haskey(Σ,x) ? Σ[x][2] : nothing))

function get_interesting() :: TC
    function mconstr(S,T,C,Σ) :: MType{Tuple{Vector{Symbol},Vector{Annotation}, Vector{DMType}}}
        names, annotations, types = ([], [], [])
        for (x, (a, τ, i)) in Σ
            if i
                names = [names; x]
                annotations = [annotations; a]
                types = [types; τ]
            end
        end
        return (S,T,C,Σ), (names, annotations, types)
    end
    TC(mconstr)
end

"""
    get_arglist(xτs::Vector{<:TAsgmt}) :: TC

Look up the types and sensitivities/privacies of the variables in `xτs` from the current context.
If a variable is not present in Σ (this means it was not used in the lambda body),
create a new type/typevar according to type hint given in `xτs` and give it zero annotation
"""
# then remove the xs from Σ
function get_arglist(xτs::Vector{<:TAsgmt}) :: TC#{Vect{Sens x DMType}}
    function mconstr(S,T,C,Σ) :: MType{Vector{Tuple{Annotation, DMType}}}

        function make_type(dτ::DataType)
            # if the type hint is DMDUnkown, we just add a typevar. otherwise we can be more specific
            τx, S, T, C = create_DMType(dτ, S, T, C)
            (zero(Σ), τx) # set variable sensitivity/privacy to zero and interestingness to false
        end

        Σ = deepcopy(Σ)
        nxτs = [haskey(Σ, x) ? Σ[x][1:2] : make_type(τx) for (x,τx) in xτs]
        for (x,_) in xτs
            if haskey(Σ,x)
                delete!(Σ, x)
            end
        end
        (S,T,C,Σ), nxτs
    end
    TC(mconstr)
end



#########################################################################################
# stuff stilen from Monads.jl that we might need
#abstract type MonadPlus <: Monad end
# types
#export Monad, Identity, MList, Maybe, State, MPromise
# combinators
#export mreturn, join, fmap, mbind, mcomp, mthen, (>>)
# utilities
#export liftM
# do syntax
#export @mdo
# MonadPlus
#export MonadPlus, mzero, mplus, guard
# State
#export runState, put, get, evalState, execState

## Buy two monad combinators, get the third free!
#mreturn(::Type{M}, val) where {M<:Monad} = M(val)
#mjoin(m::Monad) = mbind(identity, m)
#fmap(f::Function, m::M) where {M<:Monad} = mbind(x->mreturn(M, f(x)), m)
#mbind(f::Function, m::Monad) = mjoin(fmap(f, m))


## A MonadPlus function
#guard(::Type{M}, c::Bool) where {M<:MonadPlus} = c ? mreturn(M, nothing) : mzero(M)

#(>>)(m::Monad, k::Monad) = mthen(k, m)

#mcomp(g::Function, f::Function) = x -> mbind(g, f(x))

#=
## Function lifting
liftM(::Type{M}, f::Function) where {M<:Monad} = m1 -> @mdo M begin
    x1 <- m1
    return f(x1)
end

## Starting slow: Identity
struct Identity{T} <: Monad
    value :: T
end

mbind(f::Function, m::Identity) = f(m.value)

## List
struct MList <: MonadPlus
    value :: Vector

    MList(x::Array) = new(vec(x))
    MList(x) = new([x])
end

function join(m::MList)
    if !isempty(m.value)
        val = nothing
        for arr in m.value[1:end]
            if !isempty(arr.value)
                if val === nothing
                    val = arr.value
                else
                    append!(val, arr.value)
                end
            end
        end
        if val === nothing
            mzero(MList)
        else
            mreturn(MList, val)
        end
    else
        mzero(MList)
    end
end
fmap(f::Function, m::MList) = MList(map(f, m.value))

mbind(f::Function, m::MList) = join(fmap(f, m))

# It's also a MonadPlus
mzero(::Type{MList}) = MList([])
mplus(m1::MList, m2::MList) = join(MList([m1, m2]))

struct Nothing end

## Maybe
struct Maybe{T} <: Monad
    value :: Union{T, Nothing}
end

mbind(f::Function, m::Maybe) = isa(m.value, Nothing) ? Maybe(nothing) : f(m.value)

## State
struct State <: Monad
    runState :: Function # s -> (a, s)
end
state(f) = State(f)

runState(s::State) = s.runState
runState(s::State, st) = s.runState(st)

function mbind(f::Function, s::State)
      state(st -> begin
          (x, stp) = runState(s, st)
          runState(f(x), stp)
            end
            )
end
mreturn(::Type{State}, x) = state(st -> (x, st))

put(newState) = state(_ -> (nothing, newState))
get() = state(st -> (st, st))

evalState(s::State, st) = runState(s, st)[1]
execState(s::State, st) = runState(s, st)[2]

end
=#