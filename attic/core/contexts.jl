



############################################################################################
### TypeOps

"""
    add_TypeOp((S,T,C), op :: DMTypeOp)

Add `op` to the constraints `C`, also creating the necessary type and sensitivity variables.
Return the new context, the `DMType` of the result of the operation, and its signature.
"""
function add_TypeOp((S,T,C) :: Tuple{SVarCtx,TVarCtx,Constraints}, op :: DMTypeOp) :: Tuple{Tuple{SVarCtx,TVarCtx,Constraints}, DMType, Vector{Sensitivity}}

    function name_prefix(τ::DMType)
        name = @match τ begin
            DMInt() => Symbol("int_")
            DMReal() => Symbol("real_")
            TVar(s) => Symbol(s, "_");
            Constant(t,η) => Symbol(t, "_const_");
            _ => Symbol("_")
        end;
        return name
    end

    @match op begin
        Unary(kind, τ) => let
            (S , svar) = addNewName(S, name_prefix(τ))
            (T , tvar) = addNewName(T, Symbol("res_", typeof(kind)))
            C2 = [isTypeOpResult([symbols(svar)], TVar(tvar), Unary(kind, τ))]
            if kind isa DMOpCeil
                C2 = [C2 ; isNumeric(τ)]
            end
            C = vcat(C, C2)

            (S, T, C), TVar(tvar), [symbols(svar)]
        end;
        Binary(kind, τ1, τ2) => let
            (S , svar1) = addNewName(S, name_prefix(τ1))
            (S , svar2) = addNewName(S, name_prefix(τ2))
            (T , tvar) = addNewName(T, Symbol("res_", typeof(kind)))
            C2 = [
                  isTypeOpResult([symbols(svar1), symbols(svar2)], TVar(tvar), Binary(kind, τ1, τ2)),
                  isNumeric(τ1),
                  isNumeric(τ2)
                 ]
            C = vcat(C, C2)

            # for subtraction of constants, make sure the result is non-negative
            # TODO figure out how to handle non-negative numbers
            #@match (kind, τ1, τ2) begin
            #    (DMOpSub(), Constant(_, η1), Constant(_, η2)) => let
            #        C = [C; isLessOrEqual(η2, η1)]
            #    end;
            #    _ => nothing
            #end

            (S, T, C), TVar(tvar), [symbols(svar1), symbols(svar2)]
        end;
    end
end

############################################################################################
### Context Operations

"""
    merge_contexts(combine::Function, S, T, C, Σ1, Σ2)

Make a new context that has all variables of both input contexts. Unify types if the
contexts disagree on the type of a variable. Apply the `combine` function on the annotations
of the variables present in both contexts.
"""
function merge_contexts(combine::Function, S::SVarCtx, T::TVarCtx, C::Constraints, Σ1::A, Σ2::A) :: Full{A} where {A<:Context}
    Σ = deepcopy(Σ1)
    for (v, (s, τ, int)) in Σ2
        if haskey(Σ1, v)
            @assert Σ1[v][3] == int "Trying to unify variables with different interestingness?"
            println("combining $s and $(Σ1[v][1])")
            sa = s isa Sensitivity ? simplify_sensitivity(combine(s, Σ1[v][1])) : simplify_sensitivity.(combine(s, Σ1[v][1]))
            # if the contexts disagree on the type of v, unify.
            if haskey(Σ, v)
                τ, Cu = unify_nosubs(Σ1[v][2], τ)
                C = [C; Cu]
            end
            Σ[v] = (sa, τ, int)
        else
            Σ[v] = (s, τ, int)
        end
    end
    (S, T, C, Σ)
end

"""
    merge_contexts(combine::Function, S, T, C, Σs::Array)

Make a new context that has all variables of all input contexts. Unify types if the
contexts disagree on the type of a variable. Apply the `combine` function on the annotations
of the variables present in multiple contexts.
"""
function merge_contexts(combine::Function, S::SVarCtx, T::TVarCtx, C::Constraints, Σs::Array{A}) where {A<:Context}
    foldl((Σ1,Σ2) -> merge_contexts(combine,S,T,C,Σ1,Σ2), Σs)
end

"Add all `Σs`, unifying types of variables where the contexts disagree of the type."
add(S::SVarCtx, T::TVarCtx, C::Constraints, Σs::A...) where {A<:SCtx} = merge_contexts(+, S, T, C, [Σs...])
add(S::SVarCtx, T::TVarCtx, C::Constraints, Σs::A...) where {A<:PCtx} = merge_contexts((p,q)->p.+q, S, T, C, [Σs...])

add(S::SVarCtx, T::TVarCtx, C::Constraints, Σs...) = error("trying to add contexts of different types!")

"Scale all sensitivities in `Σ` by `r`."
scale(r::STerm, Σ::SCtx) = SCtx(v => (r*s, t, i) for (v,(s,t,i)) in Σ)

maxannotation(a1::Privacy, a2::Privacy) = (max(a1[1],a2[1]), max(a1[2],a2[2]))
maxannotation(a1::Sensitivity, a2::Sensitivity) = max(a1, a2)


"Combine `Σs` using the maximum of annotations, unifying types of variables where the contexts disagree of the type."
upperbound(S::SVarCtx, T::TVarCtx, C::Constraints, Σs::A...) where {A<:Context} = merge_contexts(maxannotation, S, T, C, [Σs...])

zeroa(T::Type) = T <: Sensitivity ? 0 : (0,0)
truncate(s1::A1, s2::A2) where {A1<:Annotation,A2<:Annotation} = isequal(s1, zeroa(A1)) ? zeroa(A2) : s2

# this is denoted ⌉c⌈^s in the paper
# if applied eg to SCtx and a Privacy, this changes colour of the context!
truncate(c::Context, p::Privacy) = PCtx(v => (truncate(p1, p), t, i) for (v,(p1,t,i)) in c)
truncate(c::Context, s::Sensitivity) = SCtx(v => (truncate(s1, s), t, i) for (v,(s1,t,i)) in c)

# this is denoted ⌊c⌋_{vars} in the paper
restrict(c::C, vars::Vector{Symbol}) where {C<:Context} = C(v => c[v] for v in vars)
complement(c::C, vars::Vector{Symbol}) where {C<:Context} = C(v => c[v] for v in setdiff(keys(c), vars))

# this is denoted ⌉⌊c⌋⌈^p_{vars} in the paper
restrict_truncate(c::Context, vars::Vector{Symbol}, p::Privacy) = truncate(restrict(c, vars), p)