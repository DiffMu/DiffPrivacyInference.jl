
##### substitutions
# In this file, we define functions for substituting metavariables by types or sensitivity terms.
# Furthermore, these operations are extended to work on constraints, contexts, etc., i.e.,
# every container which might contain such metavariables.

## type substitutions
# In this section we list all functions necessary for substituting type variables.

"""
Replace every occurence of the type variable `X` by the type `ξ` in the type `τ`.
That is, compute the substitution `τ`[`X` := `ξ`].
"""
function singleTSub(τ :: DMType, (X,ξ) :: TSSub) :: DMType
   @match τ begin
      DMInt() => DMInt()
      DMReal() => DMReal()
      #Idx(η) => Idx(η)
      Constant(Y, a) => Constant(singleTSub(Y, (X, ξ)), a)
      DMTup(Ts) => DMTup(map(T->singleTSub(T, (X, ξ)), Ts));
      #DMTrtProduct(Ts) => DMTrtProduct(map(ηT -> (first(ηT), singleTSub(last(ηT), (X, ξ))), Ts));
      DMVec(l,A) => DMVec(l, singleTSub(A, (X, ξ)));
      TVar(Y) => X == Y ? ξ : TVar(Y);
      Arr(As,B) => Arr([(s, singleTSub(A, (X, ξ))) for (s,A) in As], singleTSub(B , (X, ξ)));
      ArrStar(As,B) => ArrStar([(p, singleTSub(A, (X, ξ))) for (p,A) in As], singleTSub(B , (X, ξ)));
   end
end

"""
Remove the type variable `x` from the context `T` containing active type variables.
This function exists out of correctness purposes. We always carry the contexts `T` and `S`
of type- and sens-metavariables, and when substituting a meta-variable, we remove it from `T`,
resp. `S`.
This allows us to catch errors where a substitution is applied multiple times, by throwing an
error here, if the `x` is not element of the currently active names (that is, was already substituted once).
"""
function singleTSub(T :: TVarCtx, (x, τ) :: TSSub) :: TVarCtx
    # println("## Have subst: $x := $τ")
    if x in T.names && all(map(t->t in T.names, free_TVars(τ)))
      T = deepcopy(T)
      # if it's not the identity substitution, delete the subtitutee
      if TVar(x) != τ
          delete!(T.names, x)
      end
      T
   else
      error("INTERNAL ERROR: Trying to use substitution ($x, $τ) on a (t-)context which does not contain this variable ($T).")
   end
end

"""
Apply the single type substitution `σ` to the type operation `op`.
"""
function singleTSub(op :: DMTypeOp, σ :: TSSub) :: DMTypeOp
   @match op begin
      Unary(uop, τ) => Unary(uop, singleTSub(τ, σ))
      Binary(bop, τ1, τ2) => Binary(bop, singleTSub(τ1, σ), singleTSub(τ2, σ))
      Ternary(top, τ1, τ2, τ3) => Ternary(top, map(x->singleTSub(x, σ), (τ1, τ2, τ3))...)
   end
end

"""
Apply the single type substitution `σ` to the constraint `c`.
"""
function singleTSub(c :: Constr, σ :: TSSub) :: Constr
    @match c begin
        isNumeric(s) => isNumeric(singleTSub(s, σ))
        isTypeOpResult(sv, τ, op) => isTypeOpResult(sv, singleTSub(τ, σ), singleTSub(op, σ))
        isEqualSens(s1, s2) => isEqualSens(s1, s2)
        isEqualPriv(s1, s2) => isEqualPriv(s1, s2)
        isLessOrEqual(s1, s2) => isLessOrEqual(s1, s2)
        isSubtypeOf(τ1, τ2) => isSubtypeOf(singleTSub(τ1, σ), singleTSub(τ2, σ))
        isSupremumOf(τ1, τ2, ρ) => isSupremumOf(singleTSub(τ1, σ), singleTSub(τ2, σ), singleTSub(ρ, σ))
        isEqualType(t1, t2) => isEqualType(singleTSub(t1, σ) , singleTSub(t2, σ))
        isChoice(t, ts) => isChoice(singleTSub(t, σ), Dict((s,(flag, singleTSub(tt, σ))) for (s,(flag, tt)) in ts))
    end
end

"""
Apply the single type substitution `σ` to the list of constraints `C`.
"""
function singleTSub(C :: Constraints, σ :: TSSub) :: Constraints
    map(c -> singleTSub(c, σ), C)
end

"""
Apply the single type substitution `(x := ξ)` the type variable `a`. That is,
if `a` is exactly `x`, we replace it by `ξ`. Else, we do nothing.
"""
function singleTSub(a :: Symbol, (x, ξ) :: TSSub) :: SymbolOrType
   if (a == x)
      ξ
   else
      a
   end
end

"""
Apply a type substitution to a sensitivity term. Since sensitivities do not
contain type variables, this does nothing.
"""
function singleTSub(a :: Sensitivity, _ :: TSSub) :: Sensitivity
   a
end

"""
Apply a type substitution to a value of type Nothing.
This does nothing.
"""
function singleTSub(a :: Nothing, _ :: TSSub) :: Nothing
   a
end

"""
Apply a single type substitution `σ` to a sensitivity context `Γ`, by substituting
all types in this context with `σ`.
"""
function singleTSub(Γ :: SCtx, σ :: TSSub) :: SCtx
   SCtx((a => (s, singleTSub(X, σ))) for (a, (s , X)) in Γ)
end

"""
Apply a single type substitution `σ` to a type context `Γ`, by substituting
all types in this context with `σ`.
"""
function singleTSub(Γ :: TCtx, σ :: TSSub) :: TCtx
   TCtx((a => singleTSub(X, σ)) for (a, X) in Γ)
end

"""
Apply a single type substitution `σ` to a full context `(S,T,C,Γ)`, by applying it to all parts.
"""
function singleTSub((S, T, C, Γ) :: Full{A}, σ :: TSSub) :: Full{A} where {A}
   (S, singleTSub(T, σ), singleTSub(C, σ), singleTSub(Γ, σ))
end

## sensitivity substitutions
# In this section we list all types necessary for substituting sensitivity variables.

"""
Remove the sens variable `x` from the context `S` containing active sens variables.
This function exists out of correctness purposes. We always carry the contexts `T` and `S`
of type- and sens-metavariables, and when substituting a meta-variable, we remove it from `T`,
resp. `S`.
This allows us to catch errors where a substitution is applied multiple times, by throwing an
error here, if the `x` is not element of the currently active names (that is, was already substituted once).
"""
function singleSSub(S :: SVarCtx, (x, s) :: SSSub) :: SVarCtx
    if x in S.names && all(map(n -> n in union([:∞], S.names), free_symbols(s)))
      S = deepcopy(S)
      # if it's not the identity subtitution, delete the substitutee
      if !isequal(symbols(x), s)
          delete!(S.names, x)
      end

      S
   else
       error("INTERNAL ERROR: Trying to use substitution ($x, $s) on a (s-)context which does not contain this variable ($S).")
   end
end

"""
Replace every occurence of the sens variable `X` by the term `η` in the term `s`.
That is, compute the substitution `s`[`X` := `η`].
Since `s` or `η` might be already fully evaluated numbers, we simplify the resulting
term in those cases as much as possible.
"""
function singleSSub(s :: Sensitivity, (X, η) :: SSSub) :: Sensitivity
#    println("### SUBSTITUTING:\n  in $s we do $X := $η\n")
   if s isa STerm
       s = substitute(s, Dict((symbols(X)=> η)))
       η isa Number ? simplify_sensitivity(s) : s
   elseif (s isa Real) || (s isa Int)
      s
   else
      error("INTERNAL ERROR: Encountered a sensitivity $s of type " ++ typeof(s) ++ " when trying to substitute with $σ.")
   end
end

singleSSub((e,d) :: Privacy, σ :: SSSub) :: Privacy = (singleSSub(e,σ), singleSSub(d,σ))

"""
Apply the single sensitivity substition `σ` to the type `T`. This is necessary, since types
may contain sensitivity terms.
"""
function singleSSub(T :: DMType, σ :: SSSub) :: DMType
   @match T begin
      DMInt() => DMInt()
      DMReal() => DMReal()
      #Idx(η) => Idx(singleSSub(η, σ))
      Constant(X, n) => Constant(singleSSub(X, σ), singleSSub(n, σ))
      TVar(a) => TVar(a)
      Arr(τs, τ2) => Arr([(singleSSub(s, σ),singleSSub(τ, σ)) for (s,τ) in τs], singleSSub(τ2, σ))
      ArrStar(τs, τ2) => ArrStar([(singleSSub((ϵ,δ), σ),singleSSub(τ, σ)) for ((ϵ,δ),τ) in τs], singleSSub(τ2, σ))
      DMTup(τs) => DMTup(map(τ->singleSSub(τ, σ), τs))
      #DMTrtProduct(Ts) => DMTrtProduct(map(ηT -> (singleSSub(first(ηT), σ), singleSSub(last(ηT), σ)), Ts))
      DMVec(l, τ) => DMVec(singleSSub(l, σ), singleSSub(τ, σ))
   end
end

"""
Apply the single sensitivity substitution `σ` to the type operation `op`.
"""
function singleSSub(op :: DMTypeOp, σ :: SSSub) :: DMTypeOp
   @match op begin
      Unary(uop, τ) => Unary(uop, singleSSub(τ, σ))
      Binary(bop, τ1, τ2) => Binary(bop, singleSSub(τ1, σ), singleSSub(τ2, σ))
      Ternary(top, τ_n, τ_c, τ_b) => Ternary(top, singleSSub(τ_n, σ), singleSSub(τ_c, σ), singleSSub(τ_b, σ))
   end
end

"""
Apply the single sensitivity substitution `σ` to the constraint `c`.
"""
function singleSSub(c :: Constr, σ::SSSub) :: Constr
    @match c begin
        isEqualSens(s1, s2) => isEqualSens(singleSSub(s1, σ), singleSSub(s2, σ))
        isEqualPriv(p1, p2) => isEqualPriv(singleSSub(p1, σ), singleSSub(p2, σ))
        isLessOrEqual(s1, s2) => isLessOrEqual(singleSSub(s1, σ), singleSSub(s2, σ))
        isNumeric(τ) => isNumeric(singleSSub(τ, σ))
        isTypeOpResult(sv, τ, op) => isTypeOpResult(map(x->singleSSub(x, σ), sv), singleSSub(τ, σ), singleSSub(op, σ))
        isSubtypeOf(τ1, τ2) => isSubtypeOf(singleSSub(τ1, σ), singleSSub(τ2, σ))
        isSupremumOf(τ1, τ2, ρ) => isSupremumOf(singleSSub(τ1, σ), singleSSub(τ2, σ), singleSSub(ρ, σ))
        isEqualType(t1, t2) => isEqualType(singleSSub(t1, σ) , singleSSub(t2, σ))
        isChoice(t, ts) => isChoice(singleSSub(t, σ), Dict((s,(singleSSub(flag, σ), singleSSub(tt, σ))) for (s,(flag,tt)) in ts))
    end
end

"""
Apply the single sensitivity substitution `σ` to the list of constraint `C`.
"""
function singleSSub(C :: Constraints, σ :: SSSub) :: Constraints
    map(c->singleSSub(c,σ), C)
end

"""
Apply a single sensitivity substitution `σ` to a sensitivity context `Σ`, by substituting
all types in this context with `σ`.
"""
function singleSSub(Σ :: SCtx, σ :: SSSub) :: SCtx
   SCtx((a => (singleSSub(s, σ), singleSSub(X, σ))) for (a, (s , X)) in Σ)
end

"""
Apply a single sensitivity substitution `σ` to a type context `Γ`, by substituting
all types in this context with `σ`.
"""
function singleSSub(Γ :: TCtx, σ :: SSSub) :: TCtx
   TCtx((a => singleSSub(X, σ)) for (a, X) in Γ)
end

"""
Apply a single sensitivity substitution `σ` to a full context `(S,T,C,Γ)`, by applying it to all parts.
"""
function singleSSub((S, T, C, Γ) :: Full{A}, σ :: SSSub) :: Full{A} where {A}
   (singleSSub(S, σ), T, singleSSub(C, σ), singleSSub(Γ, σ))
end

"""
Apply the single sensitivity substitution `(x := η)` the sens variable `a`. That is,
if `a` is exactly `x`, we replace it by `η`. Else, we do nothing.
"""
function singleSSub(a :: Symbol, (x, η) :: SSSub) :: SymbolOrSens
   if (a == x)
      η
   else
      a
   end
end

"""
Substitute in a value of type Nothing. This does nothing.
"""
function singleSSub(a :: Nothing, _ :: SSSub) :: Nothing
   a
end

"""
Apply a list of substitutions (which might be either type or sensitivity substitutions) to
a value `X` of type `A`, for which these substitutions are defined.
"""
function apply_subs(X :: A, σs :: Substitutions) where {A}
   for σ in σs
      if σ isa TSSub
         X = singleTSub(X, σ)
      else
         X = singleSSub(X, σ)
      end
   end
   X
end

"""
Distribute substitutions over a vector of values. This calls recursively the function
`apply_subs`.
"""
function distribute_substitute(as :: Union{Vector, Tuple}, σ :: Substitutions)
   map(a->distribute_substitute(a, σ), as)
end
function distribute_substitute(a :: Any, σ :: Substitutions)
   apply_subs(a, σ)
end

"""
Pretty printing of a list of substitutions.
"""
function printSub(σ :: Substitutions)
   for (x, ξ) in σ
      println("$x := $ξ")
   end
end

