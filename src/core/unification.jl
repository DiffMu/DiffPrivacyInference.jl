
include("../core/definitions.jl")
include("../utils/logging.jl")


############################################################################################
### Sensitivity unification

EvaluatedNumber = Union{Int, Real}


"A special struct that [try_destructure_sensitivity](@ref) will return upon encountering the ∞ symbol."
struct Infty
end


"If `s` is a single symbol, infinity, or a number, return that. If not, return nothing."
function try_destructure_sensitivity(s :: Sensitivity) :: Union{Nothing, Symbol, EvaluatedNumber, Infty}
   syms = free_symbols(s)
   @match syms begin
      [] => let
         if s isa EvaluatedNumber
            s
         else
            error("INTERNAL ERROR: Encountered an (evaluated) sensitivity of type " ++ typeof(n) ++ " while trying to destructure.")
         end
      end;
      [x] => let
         x_name = Symbol(string(x))
         if isequal(s, ∞)
            Infty() # we need to distinguish this special symbol from the others so we don't make substitutions like ∞ = 7
         elseif isequal(s, symbols(x_name))
            x_name
         else
            nothing
         end
      end;
      _ => nothing
   end
end

#TODO do this properly
function unify_Sensitivity_nosubs(s1 :: Sensitivity, s2 :: Sensitivity) :: Tuple{Sensitivity, Constraints}
    s, Cs, subs = unify_Sensitivity(s1,s2)
    Cs = [Cs; substitutions_to_constraints(subs)]
    s, Cs
end

"Unify `s1` and `s2` by attempting to destructure or adding an equality constraint upon failure."
function unify_Sensitivity(s1 :: Sensitivity, s2 :: Sensitivity) :: Tuple{Sensitivity, Constraints, Substitutions}

   # handle the case where both sides are the same
   if isequal(s1, s2)
       (s1, [], [])
   else
      ds1 , ds2 = (try_destructure_sensitivity(s1), try_destructure_sensitivity(s2))

      # println("Destructuring s1 & s2:")
      # println("$ds1    &    $ds2")

      @match (ds1, ds2) begin
         (::EvaluatedNumber, ::EvaluatedNumber) => if ds1 == ds2
             (ds1, [], [])
         else
             throw(ConstraintViolation("impossible constraint: $ds1 = $ds2"))
         end
         (::Infty, ::Infty) => (ds1, [], [])
         (x :: Symbol, _) => (s2, [], [(x, s2)])
         (_, y :: Symbol) => (s1, [], [(y, s1)])
         (_ , _) => (s1, [isEqual(s1, s2)], [])
      end
   end
end

############################################################################################
### utils

"Convert substitutions to `isEqual` or `isEqualType` constraints."
function substitutions_to_constraints(σs :: Substitutions) :: Constraints
    c = Constraints()
    for σ in σs
        if σ isa TSSub
            var, value = σ
            push!(c, isEqualType(TVar(var), value))
        elseif σ isa SSSub
            var, value = σ
            push!(c, isEqual(symbols(var), value))
        else
            error("INTERNAL ERROR: Unexpected substitution type.")
        end
    end
    c
end

############################################################################################
### Type unification

#TODO build this right in
function unify_nosubs(τ :: DMType, ρ :: DMType) :: Tuple{DMType, Constraints}
    τ, C, σ = unify_DMType(τ, ρ)
    C = [C; substitutions_to_constraints(σ)]
    τ, C
end



"""
    unify_DMType(τ :: DMType, ρ :: DMType)

Unify the types `τ` and `ρ`, returning the new type as well as all constraints added
and substitutions made in the process.
"""
function unify_DMType(τ :: DMType, ρ :: DMType) :: Tuple{DMType, Constraints, Substitutions}
    printdebug(Log_UnificationPhases(), "== Entering Unification: unifying: $τ ≈ $ρ")

    function simpleReturn(τr, C, σs)
        printdebug(Log_UnificationPhases(), "unification resulted in substs: $σs")
        printdebug(Log_UnificationPhases(), "unification resulted in constr: $C")
        printdebug(Log_UnificationPhases(), "== Exiting Unification.")
        τr, C, σs
    end
    @match (τ, ρ) begin
        (DMInt(), DMInt()) => simpleReturn(DMInt(), [], [])
        (DMReal(), DMReal()) => simpleReturn(DMReal(), [], [])
        #(Idx(η1), Idx(η2)) => (Idx(min(η1, η2)), Idx(min(η1, η2)), [], []) #TODO index with number or constant?
        (Constant(X, c), Constant(Y, d)) =>
            let
                (T, co1, σ1) = unify_DMType(X,Y)
                (s, co2, σ2) = unify_Sensitivity(c, d)    #WARNING: Bugs possible here, we do not apply σ1 to c and d. This should in our case not be neccessary, but seems wrong.
                simpleReturn(Constant(T, s), [co1; co2], [σ1; σ2])
            end;
        (DMVec(l1, X1), DMVec(l2, X2)) => let
            (T, co1, σ1) = unify_DMType(X1, X2)
            (l, co2, σ2) = unify_Sensitivity(l1, l2)    #WARNING: same again.
            simpleReturn(DMVec(l, T), [co1; co2], [σ1; σ2])
        end
        (DMTup(X1s), DMTup(X2s)) => let
            σ, co = [], []
            τs = []
            Xs = collect(zip(X1s, X2s))
            for i in 1:length(X1s)
                (X1, X2) = Xs[i]

                # unify element types
                (T, cot, σt) = unify_DMType(X1, X2)
                push!(τs, T)
                Xs, τs, co = distribute_substitute((Xs,τs,co), σt)
                σ = vcat(σ, σt)
                co = vcat(co, cot)
            end
            simpleReturn(DMTup(τs), co, σ)
        end
            #=
        (A, ForAll((Δ, C), B)) => begin
            A, B, C2, σs2 = unify_DMType(A,B)
            println("Unifying $τ ≈ $ρ")
            println("=== Raw:")
            println("    Type 1: $A")
            println("    Type 2: $B")
            println("    Constraints: $C2")
            println("    Substitutions: $σs2")

            (Δ, σs_global, σs_local, C_global, C_local) = splitByNames_reorientSubstitutions(Δ, σs2, C2)

            # We have to apply the new local substitutions to our existing constraints
            C = apply_subs(C, σs_local)
            B = apply_subs(B, σs_local)

            # NOTE: the order of A and B matters here
            Res = ForAll((Δ, [C ; C_local]), B)

            # println("Unifying $τ ≈ $ρ\nResult: $Res\nConstraints: $C_global\nGlobal Substs: $σs_global\nlocal (forgotten) substs: $σs_local\n")
            println("=== Diffed:")
            println("    Type: $Res")
            println("    Constraints: $C_global")
            println("    Global Substs: $σs_global")
            println("    local (forgotten) substs: $σs_local\n")

            Res, Res , C_global, σs_global
            # A, ForAll((Δ, [C ; C_local]), B) , C_global, σs_global
        end
        (ForAll((Δ, C),B), A) => begin
            A, B, C2, σs2 = unify_DMType(A,B)
            println("Unifying $τ ≈ $ρ")
            println("=== Raw:")
            println("    Type 1: $B")
            println("    Type 2: $A")
            println("    Constraints: $C2")
            println("    Substitutions: $σs2")

            (Δ, σs_global, σs_local, C_global, C_local) = splitByNames_reorientSubstitutions(Δ, σs2, C2)

            # We have to apply the new local substitutions to our existing constraints
            C = apply_subs(C, σs_local)
            B = apply_subs(B, σs_local)

            # NOTE: the order of A and B matters here
            Res = ForAll((Δ, [C ; C_local]), B)

            println("=== Diffed:")
            println("    Type: $Res")
            println("    Constraints: $C_global")
            println("    Global Substs: $σs_global")
            println("    local (forgotten) substs: $σs_local\n")

            Res, Res , C_global, σs_global
        end
        =#
        #=
        (DMTrtProduct(X1s), DMTrtProduct(X2s)) => let
        σ, co = [], []
        for ((η1, X1), (η2, X2)) in zip(X1s, X2s)
        # unify element types
        _, _, cot1, σt1 = unify_Sensitivity(η1, η2)
        X1, X2, X1s, X2s, co = distribute_substitute((X1, X2, X1s, X2s, co), σt1)

        (X1, X2, cot2, σt2) = unify_DMType(X1, X2)
        X1s, X2s, co = distribute_substitute((X1s,X2s,co), σt2)
        σ = [σ; σt1; σt2]
        co = [co; cot1; cot2]
        end
        (DMTrtProduct(X1s), DMTrtProduct(X2s), co, σ)
        end
        =#
        (Arr(X1s,Y1), Arr(X2s,Y2)) =>
        let
            if length(X1s) != length(X2s)
                throw(ConstraintViolation("trying to unify arrows with different no. of arguments:\n   $τ\nand\n   $ρ"))
            end
            σ = Substitutions()
            co = []
            Xs = DMType[]
            S = Sensitivity[]
            for i in 1:length(X1s)
                # unify argument types
                X1, X2 = X1s[i][2], X2s[i][2]
                (X, cot, σt) = unify_DMType(X1, X2)
                X1s, X2s = distribute_substitute((X1s,X2s), σt)
                push!(Xs, X)
                σ = vcat(σ, σt)
                co = vcat(co, cot)

                # unify argument sensitivities
                s1, s2 = X1s[i][1], X2s[i][1]
                (s, cos, σs) = unify_Sensitivity(s1, s2)
                X1s, X2s = distribute_substitute((X1s,X2s), σs)
                push!(S, s)
                σ = vcat(σ, σs)
                co = vcat(co, cos)
            end

            # unify result type
            Y1, Y2 = distribute_substitute((Y1, Y2), σ)
            (Y, cor, σr) = unify_DMType(Y1, Y2)
            σ = vcat(σ, σr)
            co = vcat(co, cor)

            Xs, S, co = distribute_substitute((Xs, S, co), σ)

            simpleReturn((Arr(collect(zip(S, Xs)), Y)), co, σ)
        end;
        (TVar(t1), TVar(t2)) && if t1 == t2 end => simpleReturn(TVar(t1), [], [])
        (TVar(n1), Y)                           => simpleReturn(Y, [], [(n1, Y)])
        (X, TVar(n2))                           => simpleReturn(X, [], [(n2, X)])
        (_ , _) => throw(ConstraintViolation("could not unify the types $τ and $ρ."))
    end
end
