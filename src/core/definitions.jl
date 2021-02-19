
# This file contains most of the data types which are used in the delmu typechecker.
# This means above all the typesystem,
# whose components such as types, sensitivities, constraints, contexts are defined below.

####################################################################
## Sensitivity & Privacy

"""
This is the type of sensitivity terms. That is, formal terms for real numbers,
possibly containing free variables.

It is implemented as a wrapper around the `Term`-type
of SymbolicUtils, but also allows a term to be either simply a single symbol,
or an evaluated number.
"""
STerm = Union{SymbolicUtils.Term, <:SymbolicUtils.Sym, SymbolicUtils.Symbolic, Number}

"""
Given a julia symbol `x`, we create a sensitivity term which simply contains this single variable.
"""
symbols(x::Symbol) = SymbolicUtils.Sym{Number}(x)

"""
A privacy term is a tuple (ϵ,δ) of two formal expressions, here simply implemented as
a pair of sensitivity terms.
"""
Privacy = Tuple{STerm, STerm} # we say (Inf,Inf) for ∞, as union types are annoying.

"We may use `Sensitivity` instead of `STerm`."
Sensitivity = STerm

"An annotation is either a sensitivity, or a privacy term."
Annotation = Union{Sensitivity, Privacy}

####################################################################
## Sensitivity & Privacy Variables

Names = Set{Symbol}

"""
A container for keeping track of active metavariables.
See also: [`addNewName`](@ref)
"""
struct NameCtx
    names :: Set{Symbol}
    current_ctr :: Int
end

"We override the equality on name contexts to be comparing by value instead of by reference."
Base.isequal(a::NameCtx, aa::NameCtx) = isequal(a.names, aa.names) && isequal(a.current_ctr, aa.current_ctr)

Base.show(io::IO, a::NameCtx) = print(io, "  ", join(map(string, collect(a.names)), ", "))

"A context of type metavariables is simply a name context."
TVarCtx = NameCtx

"A context of sensitivity metavariables is simply a name context."
SVarCtx = NameCtx

####################################################################
## DMTypes

# NOTE: We have to "forward declare" the `Constr` type since julia isn't able to deal
#       with mutually recursive structs.
"Alternative name for Constr"
abstract type ConstrAbstr end

"""
We sometimes want to track differences of sensitivity, and type metavariable contexts.
A value `(ΔS,ΔT) :: DeltaNames` is meant to express that `ΔS` and `ΔT` are the sensitivity,
and type variable sets which were added/substracted.
"""
DeltaNames = Tuple{Names,Names}

"Alternative name for Constraints"
ConstraintsAbstr = Vector{<:ConstrAbstr}

# The definition of the types in our type system.
# This is mostly based on the description of the duet language in:
# http://david.darais.com/assets/papers/duet/duet.pdf
#
# With the following main changes:
# - The constructor for sensitivity arrow types, `Arr`, takes a vector of Types, instead of a single one,
# in order to respect Julia's distinction between curried and uncurried function types.
#
# Note: Some type constructors are not implemented yet, for example `Idx`, or `ArrStar`
#
# Note: These types are those used during typechecking. Another set of types,
# used during parsing is `DMDispatch`.
#
# See also: [`DMDispatch`](@ref)
@data DMType begin
    # Type of an integer.
    DMInt :: () => DMType

    # Type of a real number.
    DMReal :: () => DMType

    # Type of a constant value (factually of type `DMInt` or `DMReal`).
    # E.g., `Constant(DMInt(),3)`, or `Constant(TVar("a"), symbols("s"))`
    Constant :: (DMType, Sensitivity) => DMType # We allow any DMType here, in order to allow type variables

    # Type for indexing into vectors.
    # Idx :: STerm => DMType

    # Type of an n-tuple, whose entries are of the given types in the vector.
    DMTup :: Vector{DMType} => DMType # tuple

    # 'Transparent' tuple type, intended for having better, transparent sensitivity of tuples.
    # DMTrtProduct :: Vector{Tuple{Sensitivity, DMType}} => DMType # Transparent Product

    # Type of vectors. `DMVec(n,A)` means a vector with elements of type `A`, of size `n`.
    DMVec :: (Sensitivity, DMType) => DMType # vector of fixed length

    # A (meta-) typevariable.
    TVar :: Symbol => DMType

    # Type of privacy functions. Currently not implemented.
    # ArrStar :: (Dict{Symbol, Tuple{Tuple{STerm, STerm}, DMType}}, DMType) => DMType
    Arr :: (Vector{Tuple{Sensitivity, DMType}}, DMType) => DMType
end





####################################################################
## SymEngine
"We introduce a symbol for infinite sensitivity values. This are implemented as a free variable with the name ∞"
∞ = symbols(:∞)

"""
    free_symbols(ex::STerm)
Computes the free variables of the sensitivity term `ex`.
"""
free_symbols(ex::STerm) = @match ex begin
    ::SymbolicUtils.Sym => [ex.name]
    ::SymbolicUtils.Symbolic => vcat(map(free_symbols, [keys(ex.dict)...])...)
    ::SymbolicUtils.Term => vcat(map(free_symbols, ex.arguments)...)
    ::Number => []
end;


####################################################################
## Substitutions

"A single type substitution, e.g. `(x, τ)` means `x := τ`"
TSSub = Tuple{Symbol, DMType}

"A single sensitivity substitution, e.g. `(x, η)` means `x := η`"
SSSub = Tuple{Symbol, STerm}

"A substitution which might be either a type- or a sensitivity substitution."
AnySSub = Union{SSSub, TSSub}

"A list of multiple substitutions (of any kind)."
Substitutions = Vector{AnySSub}

####################################################################
## Type Operations
# It is often the case that we cannot say what type a simple operation
# such as `a + b` will have, since this depends on the types of `a` and `b`,
# which apriori seldom are going to be known.
# Thus we introduce 'type operations' encoding these unknown types,
# If `a : A` and `b : B`, then `a + b : Binary(DMOpAdd(), A, B)`.
# Further along while typechecking, we will compute the actual value of that type.

# The type of all possible unary type operations.
@data DMTypeOps_Unary begin
   DMOpCeil :: () => DMTypeOps_Unary
end

# "The type of all possible binary type operations."
@data DMTypeOps_Binary begin
   DMOpAdd :: () => DMTypeOps_Binary
   DMOpSub :: () => DMTypeOps_Binary
   DMOpMul :: () => DMTypeOps_Binary
   DMOpDiv :: () => DMTypeOps_Binary
   DMOpMod :: () => DMTypeOps_Binary
   DMOpEq :: () => DMTypeOps_Binary
end

# The type of all possible ternary type operations.
@data DMTypeOps_Ternary begin
   DMOpLoop :: () => DMTypeOps_Ternary
end

# An application of a type operation to an appropriate number of type arguments
@data DMTypeOp begin
   Unary :: (DMTypeOps_Unary, DMType) => DMTypeOp
   Binary :: (DMTypeOps_Binary, DMType, DMType) => DMTypeOp
   Ternary :: (DMTypeOps_Ternary, DMType, DMType, DMType) => DMTypeOp
end

# julia interface

builtin_ops = Dict(
                   :ceil => τs -> Unary(DMOpCeil(), τs...),
                   :+ => τs -> Binary(DMOpAdd(), τs...),
                   :- => τs -> Binary(DMOpSub(), τs...),
                   :* => τs -> Binary(DMOpMul(), τs...),
                   :/ => τs -> Binary(DMOpDiv(), τs...),
                   :% => τs -> Binary(DMOpMod(), τs...),
                   :rem => τs -> Binary(DMOpMod(), τs...),
                   :(==) => τs -> Binary(DMOpEq(), τs...)
                  )

is_builtin_op(f::Symbol) = haskey(builtin_ops,f)

"Get a map from some argument `DMType`s to the `DMTypeOp` corresponding to the input julia function."
getDMOp(f::Symbol) = is_builtin_op(f) ? builtin_ops[f] : error("Unsupported builtin op $f.")

# pretty printing

"We override equality of type operations to be by value instead of by reference."
Base.isequal(a::T, aa::T) where {T<:DMTypeOp} = all(map(t->isequal(t...), [(getfield(a, i), getfield(aa, i)) for i in 1:(fieldcount(T))]))

"Pretty printing unary type operations."
function prettyString(op :: DMTypeOps_Unary)
    @match op begin
        DMOpCeil() => "ceil"
    end
end

"Pretty printing binary type operations."
function prettyString(op :: DMTypeOps_Binary)
    @match op begin
        DMOpAdd() => "+"
        DMOpSub() => "-"
        DMOpMul() => "*"
        DMOpDiv() => "/"
        DMOpMod() => "%"
        DMOpEq() => "=?="
    end
end

"Pretty printing ternary type operations."
function prettyString(op :: DMTypeOps_Ternary)
    @match op begin
        DMOpLoop() => "loop"
    end
end

"Pretty printing applied type operations"
function showPretty(io::IO, op :: DMTypeOp)
    @match op begin
        Unary(op, arg) => print(io, prettyString(op), "(", arg, ")")
        Binary(op, a1, a2) => print(io, a1, " ", prettyString(op), " ", a2)
        Ternary(op, a1, a2, a3) => print(io, prettyString(op), "(", a1, ", ", a2, ", ", a3, ")")
    end
end


####################################################################
## Constraints
# During typechecking not all type variables can always be given an explicit value.
# Sometimes we only get a set of constraints which have to hold for the solutions of these variables.
# Here we define all possible such constraints.

SymbolOrSens = Union{Symbol, Sensitivity}
SymbolOrType = Union{Symbol, DMType}

# The possible constraints in our type system.
@data Constr <: ConstrAbstr begin
    # `isNumeric(τ)` means that `τ` needs to be numeric, i.e., either an integer or a real.
    isNumeric :: (DMType) => Constr

    # `isLessOrEqual(s₁, s₂)` means that `s₁ ≤ s₂` has to hold.
    isLessOrEqual :: (SymbolOrSens, SymbolOrSens) => Constr

    # `isTypeOpResult(sv,τ,op)` means that the result of executing the operation as encoded in `op`,
    # on operands of the types as encoded in `op`, will be a value of type `τ`, and it will depend with
    # sensitivities `sv` on the operands given in `op`.
    # Note: In particular, this means that `sv` should always have exactly as many entries, as there are
    # operands in `op.`
    isTypeOpResult :: (Vector{Sensitivity}, DMType, DMTypeOp) => Constr

    # `isEqual(s₁, s₂)` means that the sensitivities `s₁` and `s₂` should be equal.
    isEqual :: (Sensitivity, Sensitivity) => Constr

    # `isEqual(τ₁, τ₂)` means that the types `τ₁` and `τ₂` should be equal.
    isEqualType :: (DMType, DMType) => Constr

    # `isSubTypeOf(τ₁, τ₂)` means that τ₁ ⊑ τ₂ should hold.
    isSubtypeOf :: (DMType, DMType) => Constr

    # `isSupremumOf(τ₁, τ₂, σ)` means that `sup{τ₁, τ₂} = σ` should hold.
    isSupremumOf :: (DMType, DMType, DMType) => Constr

    # for dispatch, dict maps user-given signature to a flag variable and the inferred function type.
    # flag will be set to 0 or 1 according to which choice was picked.
    isChoice :: (DMType, Dict{<:Vector{<:DataType}, <:Tuple{SymbolicUtils.Sym{Number},Arr}}) => Constr
end

"The type of constraints is simply a list of individual constraints."
Constraints = Vector{Constr}

"We override the equality on constraints to be comparing by value instead of by reference."
Base.isequal(a::T, aa::T) where {T<:Constr} = all(map(t->isequal(t...), [(getfield(a, i), getfield(aa, i)) for i in 1:(fieldcount(T))]))
Base.isequal(c::isChoice, cc::isChoice) = isequal(c._1,cc._1) &&  isequal(keys(c._2), keys(cc._2)) && all([isequal(c._2[e],cc._2[e]) for e in keys(c._2)])

"Pretty printing for constraints."
Base.show(io::IO, C::Constraints) =
    print(io, "  ",  join(sort(map(string, C)), "\n  "))

"Pretty printing for a single constraint."
Base.show(io::IO, c::Constr) =
    @match c begin
        isNumeric(a) => print(io, a, " is numeric")
        isLessOrEqual(a,b) => print(io, a, " ≤ ", b)
        isTypeOpResult(sens, τ, op) =>
            let
                print(io, "(", join(map(string, sens), ", "), ", ", τ, ") = ")
                showPretty(io, op)
            end
        isEqual(s1, s2) => print(io, s1, " == ", s2)
        isSubtypeOf(τ1, τ2) => print(io, τ1, " ⊑ ", τ2)
        isSupremumOf(τ1, τ2, σ) => print(io, σ, " = sup{", τ1, ", ", τ2, "}")
        isEqualType(s1,s2) => print(io, s1, " == ", s2)
        isChoice(τ,cs) => print(io, τ, " is chosen from ", cs)
    end

#--- insert
# NOTE: We have to do this after `Constr` is defined
DeltaCtx = Tuple{DeltaNames,Constraints}
#--- insert end

"An error to throw upon finding a constraint that is violated."
struct ConstraintViolation <: Exception
msg::String
end

####################################################################
## Interface of DMType and julia DataType.
#TODO thoroughly review this

"Make a proper `DMType` out of `τ`, adding sensitivity and type variables to `S` and `T` if necessary."
function create_DMType(τ::DataType, S::SVarCtx, T::TVarCtx, C::Constraints) :: Tuple{DMType, SVarCtx, TVarCtx, Constraints}
    if τ <: Integer
        return DMInt(), S, T, C
    elseif τ <: Real
        return DMReal(), S, T, C
    elseif τ <: Number
        (T, tvar) = addNewName(T, Symbol("num_"))
        return TVar(tvar), S, T, [C; isNumeric(TVar(tvar))]
    elseif τ <: Tuple
        # get DMType for every tuple element type
        for τp in τ.parameters
            τp, S, T, C = create_DMType(τp, S, T, C)
            push!(τs, τp)
        end
        return DMTup(τs), S, T, C
    elseif τ <: Vector
        # add sens var for length
        (S, svar) = addNewName(S, Symbol("veclen_"))
        # get element type DMType
        τelem, S, T, C = create_DMType(τ.parameters[1], S, T, C)
        return DMVec(symbols(svar), τelem), S, T, C
    elseif τ == Any
        # just a type var.
        (T, tvar) = addNewName(T, Symbol("any_"))
        return TVar(tvar), S, T, C
    else
        error("unsupported type $τ")
    end
end

function juliatype(τ::DMType) :: DataType
   @match τ begin
      DMInt() => Integer
      DMReal() => Real
      Constant(Y, a) => juliatype(Y)
      DMTup(Ts) => Tuple{map(juliatype, Ts)...}
      DMVec(l,A) => Vector{juliatype(A)}
      TVar(Y) => error("unknown type")
      Arr(As,B) => Function
      _ => error("not implemented")
  end
end



####################################################################
## Contexts
# Contexts assign a type to each variable in scope. In the case of duet/delmu,
# we have different kinds of contexts, used in different situations.

"A simple context, assigning to a variable a type."
TypeContext = Dict{Symbol, DMType}

"A privacy context assigns not only a type, but also a privacy term to every variable."
PrivacyContext = Dict{Symbol, Tuple{Privacy, DMType}}

"A sensitivity context assigns not only a type, but also a sensitivity term to every variable."
SensitivityContext = Dict{Symbol, Tuple{Sensitivity, DMType}}

"Usually, a context is either a privacy-, or a sensitivity context."
Context = Union{PrivacyContext, SensitivityContext}

# Abbreviations for contexts.
PCtx = PrivacyContext
SCtx = SensitivityContext
TCtx = TypeContext

"""
We usually carry around not only a context `Γ`, but additionaly a sensitivity variable context `S`,
and a type variable context `T`, which track all free type/sens variables occuring in `Γ`.
And additionally also a vector of constraints `C`, which express all constraints which have to
hold for those free variables.

An element of type `Full`, i.e., a 'full context' is a combination of all of these, that is:
    (S,T,C,Γ) :: Full{TypeCtx}

Note: we accept different kinds of contexts here, the one intended is stated in curly braces after `Full`.

See also: [`TypeContext`](@ref), [`PrivacyContext`](@ref), [`SensitivityContext`](@ref)
"""
const Full = Tuple{SVarCtx,TVarCtx,Constraints,A} where {A}

"Pretty printing for full contexts."
pretty_print((S,T,C,A)::Full) =  join(["\n S: ", S, "\n\n T: ", T, "\n\n C: ", C, "\n\n G: ", A, "\n"])

"Pretty printing for sensitivity contexts."
function Base.show(io::IO, G::SCtx)
    for (s, t) in G
        print(io, "  ", t, " @(", s, ")\n")
    end
end

"Pretty printing for full contexts."
function Base.show(io::IO, (S,T,C,G)::Full{SCtx})
    print(io, "Sensitivity vars:\n", S, "\n")
    print(io, "Type vars:\n", T, "\n")
    print(io, "Constraints:\n", C, "\n")
    print(io, "Context:\n", G, "\n")
end

"Creates an empty type context."
emptyTVarCtx() = TVarCtx(Set(), 0)

"Creates an empty sensitivity context."
emptySVarCtx() = SVarCtx(Set(), 0)

"Creates an empty set of constraints."
emptyConstraints() = Vector{Constr}()


"""
    addNewName(N::NameCtx,hint::Symbol) :: Tuple{NameCtx,Symbol}

Requests a fresh metavariable name from `N`. The hint is used as a basis
from which to generate the name. Returns it, as well as a modified instance
of `N`, which should be the only one used from now on.
"""
function addNewName(N::NameCtx,hint::Symbol) :: Tuple{NameCtx,Symbol}
   new_names = copy(N.names)
   new_name = Symbol((hint),N.current_ctr)
   push!(new_names,new_name)
   NameCtx(new_names, N.current_ctr + 1), new_name
end

function add_new_type(T::NameCtx, hint::Symbol) :: Tuple{NameCtx, DMType}
    T, τ = addNewName(T, hint)
    T, TVar(τ)
end

####################################################################
## free variables
# In this section we compute the occuring free sens/type variables in various
# containers.
# These functions are mostly used for error tracking purposes.

### For Sens
"""
    free_SVars(s :: Sensitivity) :: Vector{Symbol}
Computes the free sensitivity variables in a sensitivity term.
"""
function free_SVars(s :: Sensitivity) :: Vector{Symbol}
    Vector(free_symbols(s))
end

"""
    free_TVars(s :: Sensitivity) :: Vector{Symbol}
Computes the free sensitivity variables in a type. Always returns an empty vector.
"""
function free_TVars(s :: Sensitivity) :: Vector{Symbol}
    Vector()
end


### For Sens which might be just a symbol
"""
    free_SVars(s :: SymbolOrSens) :: Vector{Symbol}
Computes the free sensitivity variables in a sensitivity term, which also might just be a symbol.
"""
function free_SVars(s :: SymbolOrSens) :: Vector{Symbol}
    if s isa Sensitivity
        free_SVars(s)
    else
        Vector([s])
    end
end

"""
    free_SVars(s :: SymbolOrSens) :: Vector{Symbol}
Computes the free type variables in a sensitivity term, which also might just be a symbol.
Always returns the empty vector.
"""
function free_TVars(s :: SymbolOrSens) :: Vector{Symbol}
    Vector()
end

### For Type Sensitivity Declarations
"Computes the free sensitivity variables in an assignment."
function free_SVars((s,τ) :: Tuple{Sensitivity,DMType}) :: Vector{Symbol}
    union(free_SVars(s),free_SVars(τ))
end

"Computes the free sensitivity variables in an assignment."
function free_TVars((s,τ) :: Tuple{Sensitivity,DMType}) :: Vector{Symbol}
    union(free_TVars(s),free_TVars(τ))
end


### For Type (!) Assignment
# function free_SVars((s,τ) :: TAsgmt) :: Vector{Symbol}
#     free_SVars(τ)
# end

# function free_TVars((s,τ) :: TAsgmt) :: Vector{Symbol}
#     free_TVars(τ)
# end

### For Types
"""
    free_SVars(t :: DMType) :: Vector{Symbol}
Computes the free sensitivity variables in a type `t`.
"""
function free_SVars(t :: DMType) :: Vector{Symbol}
    @match t begin
        DMInt()        => Vector()
        DMReal()       => Vector()
        Constant(τ,s)  => union(free_SVars(τ), free_SVars(s))
        DMTup(v)       => union(map(free_SVars,v)...)
        DMVec(n,v)     => union(free_SVars(n),union(free_SVars(v)...))
        TVar(_)        => Vector()
        Arr(v, τ)   => union(map(free_SVars, v)... , free_SVars(τ))
    end
end

"""
    free_TVars(t :: DMType) :: Vector{Symbol}
Computes the free type variables in a type `t`.
"""
function free_TVars(t :: DMType) :: Vector{Symbol}
    @match t begin
        DMInt()        => Vector()
        DMReal()       => Vector()
        Constant(τ,s)  => union(free_TVars(τ), free_TVars(s))
        DMTup(v)       => union(map(free_TVars,v)...)
        DMVec(n,v)     => union(free_TVars(n),union(free_TVars(v)...))
        TVar(a)        => Vector([a]) # THIS LINE IS different from the SVars version above (!)
        Arr(v, τ)   => union(map(free_TVars, v)... , free_TVars(τ))
    end
end

### For a single constraint

"""
    free_SVars(c :: Constr) :: Vector{Symbol}
Computes the free sens variables in a constraint `c`.
"""
function free_SVars(c :: Constr) :: Vector{Symbol}
    @match c begin
        isNumeric(τ)             => free_SVars(τ)
        isLessOrEqual(n,m)       => union(free_SVars(n),free_SVars(m))
        isTypeOpResult(v, s, τ)  => union(map(free_SVars, v)..., free_SVars(s), free_SVars(τ))
        isEqual(s1, s2)          => union(free_SVars(s1), free_SVars(s2))
        isEqualType(s1, s2)      => union(free_SVars(s1), free_SVars(s2))
        isSubtypeOf(s1, s2)      => union(free_SVars(s1), free_SVars(s2))
        isSupremumOf(s1, s2, s3) => union(free_SVars(s1), free_SVars(s2), free_SVars(s3))
    end
end

"""
    free_TVars(c :: Constr) :: Vector{Symbol}
Computes the free type variables in a constraint `c`.
"""
function free_TVars(c :: Constr) :: Vector{Symbol}
    @match c begin
        isNumeric(τ)             => free_TVars(τ)
        isLessOrEqual(n,m)       => union(free_TVars(n),free_TVars(m))
        isTypeOpResult(v, s, τ)  => union(map(free_TVars, v)..., free_TVars(s), free_TVars(τ))
        isEqual(s1, s2)          => union(free_TVars(s1), free_TVars(s2))
        isEqualType(s1, s2)      => union(free_TVars(s1), free_TVars(s2))
        isSubtypeOf(s1, s2)      => union(free_TVars(s1), free_TVars(s2))
        isSupremumOf(s1, s2, s3) => union(free_TVars(s1), free_TVars(s2), free_TVars(s3))
    end
end

### For multiple constraints

"""
    free_SVars(c :: Constr) :: Vector{Symbol}
Computes the free sens variables in a list of constraint `c`.
"""
function free_SVars(c :: Constraints) :: Vector{Symbol}
    union(map(free_SVars, c)...)
end

"""
    free_TVars(c :: Constr) :: Vector{Symbol}
Computes the free type variables in a list of constraint `c`.
"""
function free_TVars(c :: Constraints) :: Vector{Symbol}
    free_inside = map(free_TVars, c)
    isempty(free_inside) ? [] : union(free_inside)
end

