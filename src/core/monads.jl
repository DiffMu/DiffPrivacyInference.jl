import Base.==


abstract type Monad end

# TC has a hidden type parameter A that i cannot express. i use MType{A} as a cheap substitute...
struct TC <: Monad
    func :: Function # (SVarCtx, TVarCtx, Constraints) -> (Full{SCtx} x A)
end

MType{A} = Tuple{Full{SCtx}, A}


function mbind(f::Function, m::TC) :: TC # f :: A -> TC{B}
    #m = deepcopy(m) # otherwise very weird things happen.
    function mconstr(S::SVarCtx,T::TVarCtx,C::Constraints) :: MType # it's actually MType{B}
        (S,T,C,Σm), τm = m.func(S,T,C)
        (S,T,C,Σf), τf = f(τm).func(S,T,C)
        (S,T,C,Σ) = add(S,T,C, Σm, Σf)
        ((S,T,C,Σ), τf)
    end
    TC(mconstr)
end


# this must satisfy mbind(mreturn, M) = M
# hence the empty SCtx, being the neutral element of context addition
function mreturn(::Type{TC}, val) :: TC # A -> TC{A}
    @assert !(val isa Monad) "are you sure you want to return the monad $val?"

    TC((S,T,C) -> ((S,T,C,SCtx()), val))
end


# this is foldM in haskell
# foldM :: (Monad m) => (b -> a -> m b) -> b -> [a] -> m b
# do some crazy bind(v->f(v,args[n]), bind(v-> f(v,args[n-1]), ... , bind(v->f(v,args[1]), M)...)) action, it's like
# do
#   V <- M
#   for a in args
#     V <- f(V,a)     # throwing away the type, only keeping the state.
#   end
#   return V
function mloop(f :: Function, args, M::Monad)
    println("looping on $args, start with $M")
    foldr((a, m) -> mbind(v->f(v,a), m), Iterators.reverse(args), init = M)
end
# miloop(f :: Function, n ::Int, M) = foldr((i, m) -> mbind(v->f(v,i), m), reverse(1:n), init = mreturn(TC,M)) # indexed loop

fmap(f::Function, m::M) where {M<:Monad} = mbind(x->mreturn(M, f(x)), m)


# apply f to Σ, return a monad with the result context
function apply_sctx(f::Function, m::TC) :: TC#{A} where f :: Full{SCtx} -> Full{SCtx}, m :: TC{A}
    function mconstr(S,T,C) :: MType
        STCΣ, τ = m.func(S,T,C)
        (f(STCΣ), τ)
    end
    TC(mconstr)
end

extract_Cs() = TC((S,T,C) -> ((S,T,C,SCtx()), deepcopy(C)))

## Extra combinators
mthen(k::Monad, m::Monad) = mbind(_ -> k, m)
(==)(m::Monad, k::Monad) = m.value == k.value

## Friendly monad blocks
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
