"""
This is the type of sensitivity terms. That is, formal terms for real numbers,
possibly containing free variables.

It is implemented as a wrapper around the `Term`-type
of SymbolicUtils, but also allows a term to be either simply a single symbol,
or an evaluated number.
"""
STerm = Union{SymbolicUtils.Term, <:SymbolicUtils.Sym, SymbolicUtils.Symbolic, Number}

"""
A privacy term is a tuple (ϵ,δ) of two formal expressions, here simply implemented as
a pair of sensitivity terms.
"""
Privacy = Tuple{STerm, STerm} # we say (Inf,Inf) for ∞, as union types are annoying.

"We may use `Sensitivity` instead of `STerm`."
Sensitivity = STerm

"An annotation is either a sensitivity, or a privacy term."
Annotation = Union{Sensitivity, Privacy}

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

"""
Given a julia symbol `x`, we create a sensitivity term which simply contains this single variable.
"""
symbols(x::Symbol) = SymbolicUtils.Sym{Number}(x)

"We introduce a symbol for infinite sensitivity values. This are implemented as a free variable with the name ∞"
∞ = symbols(:∞)

# custom rewrite rules for infinity
INF_RULES = [
 @acrule ~x + ∞ => ∞
 @acrule ∞ * ∞ => ∞
 @acrule ~x::(x -> x isa Number && iszero(x)) * ∞ => 0
 @acrule ~x::(x -> x isa Number && !iszero(x)) * ∞ => ∞
]

rw = SymbolicUtils.Chain([SymbolicUtils.default_simplifier(), SymbolicUtils.Postwalk(SymbolicUtils.Chain(INF_RULES))])

"Simplification of sensitivity terms."
simplify_sensitivity(s::STerm) = simplify(s; rewriter = rw)

