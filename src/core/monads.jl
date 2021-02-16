
import Base.==

#########################################################################################
# monads

abstract type Monad end

## Extra combinators
mthen(k::Monad, m::Monad) = mbind(_ -> k, m)
(==)(m::Monad, k::Monad) = m.value == k.value

## Friendly monad blocks/mdo
macro mdo(mtype, body)
    #println("mdo says: ",mdo_desugar(mdo_patch(mtype, body)))
    println("mdo says: ",esc(mdo_desugar(mdo_patch(mtype, deepcopy(body)))))
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
            println("mdo dings: mbind($newExpr) do $expr")
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
func :: Function # (Full{SCtx}) -> (Full{SCtx} x A)
end

MType{A} = Tuple{Full{SCtx}, A}

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

# execute all monads in args seperately with the same input Σ, only passing on S,T,C
# then sum the resulting contexts and return execution results as a vector
function msum(args::Vector{TC}) :: TC#{Vector}
    function mconstr(S,T,C,Σ) :: MType{Vector}
        Σ1 = SCtx()
        τs = []
        for arg in args
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

"Add a `DMTypeOp` constraint for the  `nargs`-ary operation accoding to `opf`."
function add_op(opf::Symbol, nargs::Int) :: TC#{Tuple{DMType, Vector{DMType}, Vector{Sensitivity}}}
    function mconstr(S,T,C,Σ) :: MType{Tuple{DMType, Vector{DMType}, Vector{Sensitivity}}}
        function makeType()
            T, tv = addNewName(T, Symbol("op_arg_"))
            TVar(tv)
        end
        τs = [makeType() for _ in 1:nargs]
        dmop = getDMOp(opf)(τs)
        (S,T,C), τ, sv = add_TypeOp((S,T,C), dmop)
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

"Return the current constraint list."
extract_Cs() = TC((S,T,C,Σ) -> ((S,T,C,Σ), deepcopy(C)))

"Add the given constraints to the monad's constraint list."
function add_Cs(Cs::Constraints) :: TC
    function mconstr(S,T,C,Σ) :: MType{Tuple{}}
        (S,T,union(C,Cs),Σ), ()
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

"Add a newly created sensitivity variable to the monad's sensitivity variable context `S` and return it."
function add_svar() :: TC#{Sensitivity}
    function mconstr(S,T,C,Σ) :: MType{Sensitivity}
        S, s = addNewName(S, Symbol("sens_"))
        s = symbols(s)

        (S,T,C,Σ), s
    end
    TC(mconstr)
end

"Set sensitivity of `x` to `s` and type to `τ`."
function set_var(x::Symbol, s, τ::DMType) :: TC#{DMTypen}
    function mconstr(S,T,C,Σ) :: MType{DMType}
        # x gets sensitivity s, and the inferred type
        Σ = deepcopy(Σ)
        Σ[x] = (s,τ)
        (S,T,C,Σ), τ
    end
    TC(mconstr)
end

"Delete `x` from the current context."
remove_var(x::Symbol) :: TC = TC((S,T,C,Σ) -> ((S,T,C,delete!(deepcopy(Σ), x)),()))

"Return variable `x`'s current sensitivity."
lookup_var_sens(x::Symbol) = TC((S,T,C,Σ) -> ((S,T,C,Σ), haskey(Σ,x) ? Σ[x][1] : nothing))

"Return variable `x`'s current type."
lookup_var_type(x::Symbol) = TC((S,T,C,Σ) -> ((S,T,C,Σ), haskey(Σ,x) ? Σ[x][2] : nothing))


"""
    get_arglist(xτs::Vector{<:TAsgmt}) :: TC

Look up the types and sensitivities of the variables in `xτs` from the current context.
If a variable is not present in Σ (this means it was not used in the lambda body),
create a new type/typevar according to type hint given in `xτs`
"""
# then remove the xs from Σ
function get_arglist(xτs::Vector{<:TAsgmt}) :: TC#{Vect{Sens x DMType}}
    function mconstr(S,T,C,Σ) :: MType{Vector{Tuple{Sensitivity, DMType}}}

        function make_type(dτ::DataType)
            # if the type hint is DMDUnkown, we just add a typevar. otherwise we can be more specific
            τx, S, T, C = create_DMType(dτ, S, T, C)
            (0, τx)
        end

        Σ = deepcopy(Σ)
        nxτs = [haskey(Σ, x) ? Σ[x] : make_type(τx) for (x,τx) in xτs]
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
