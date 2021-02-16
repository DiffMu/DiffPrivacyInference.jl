
include("unification.jl")
include("substitutions.jl")



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
            C2 = [
                  isTypeOpResult([symbols(svar)], TVar(tvar), Unary(kind, τ)),
                  isNumeric(τ)
                 ]
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
            @match (kind, τ1, τ2) begin
                (DMOpSub(), Constant(_, η1), Constant(_, η2)) => let
                    C = [C; isLessOrEqual(η2, η1)]
                end;
                _ => nothing
            end

            (S, T, C), TVar(tvar), [symbols(svar1), symbols(svar2)]
        end;
        Ternary(_, τ_n, τ_c, τ_b) => let
            # extract return type
            #TODO unify with capture type(s)?
            τ_ret = @match τ_b begin
                Arr(_, τ) => τ
                _ => error("loop body type $τ_b must be an arrow")
            end

            # create variables for context coefficients
            (S, s_n) = addNewName(S, name_prefix(τ_n))
            (S, s_c) = addNewName(S, name_prefix(τ_c))
            (S, s_b) = addNewName(S, :loop_ret_)

            # add a constraint so we can later decide whether it's a loop or an sloop
            C = [C;
                 isTypeOpResult([symbols(s_n), symbols(s_c), symbols(s_b)], TVar(τ_ret), Ternary(DMOpLoop(), τ_n, τ_c, τ_b));
                 isNumeric(τ_n)]

            (S, T, C), τ_ret, [symbols(s_n), symbols(s_c), symbols(s_b)]
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
    for (v, (s, τ)) in Σ2
        if haskey(Σ1, v)
            sa = simplify(combine(s, Σ1[v][1]))
            # if the contexts disagree on the type of v, unify.
            if haskey(Σ, v)
                τ, Cu = unify_nosubs(Σ1[v][2], τ)
                C = [C; Cu]
            end
            Σ[v] = (sa, τ)
        else
            Σ[v] = (s, τ)
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


maxannotation(a1::Privacy, a2::Privacy) = (max(a1[1],a2[1]), max(a1[2],a2[2]))
maxannotation(a1::Sensitivity, a2::Sensitivity) = max(a1, a2)


"Combine `Σs` using the maximum of annotations, unifying types of variables where the contexts disagree of the type."
upperbound(S::SVarCtx, T::TVarCtx, C::Constraints, Σs::A...) where {A<:Context} = merge_contexts(maxannotation, S, T, C, [Σs...])


"Add all `Σs`, unifying types of variables where the contexts disagree of the type."
add(S::SVarCtx, T::TVarCtx, C::Constraints, Σs::A...) where {A<:Context} = merge_contexts(+, S, T, C, [Σs...])


"Scale all sensitivities in `Σ` by `r`."
scale(r::Number, Σ::SensitivityContext) = SensitivityContext(v => (simplify(r*s), t) for (v,(s,t)) in Σ)
"Scale all sensitivities in `Σ` by `r`."
scale(r::STerm, Σ::SensitivityContext) = SensitivityContext(v => (r*s, t) for (v,(s,t)) in Σ)
"Scale all sensitivities in `Σ` by `r`."
scale(r::STerm, (S,T,C,Σ)::Full{SensitivityContext}) = (S, T, C, scale(r, Σ))


"Return new context with the given entries removed."
remove(c::Context, vars::Array{Symbol}) = Dict(e for e in c if !(e[1] in vars))
