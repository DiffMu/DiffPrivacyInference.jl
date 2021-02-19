


############################################################################################
### supremum surface
function getSupremumOf((S,T,C,Σ)::Full{A}, τ1 :: DMType, τ2 :: DMType) :: Tuple{Full{A},DMType} where {A}
    T, ρ = addNewName(T, Symbol("sup_"))
    ρ = TVar(ρ)
    C = [C ; [isSupremumOf(τ1, τ2, ρ)]]
    (S,T,C,Σ), ρ
end

############################################################################################
### supremum (deferred) evaluation

#TODO: Add a function which evaluates arrows in isSupremumOf-constraints
#      (similar to the isSubtypeOf variant)
function try_eval_isSupremumOf_nosubs(τ1 :: DMType, τ2 :: DMType, ρ :: DMType) :: Union{Nothing,Constraints}
    sup = try_eval_isSupremumOf_noarr(τ1, τ2) #TODO: We should resolve arrows first... Currently not implemented
    if sup isa Nothing
        nothing
    else
        _, C = unify_nosubs(ρ, sup)
        C
    end
end


function try_eval_isSupremumOf_noarr(orig1 :: DMType, orig2 :: DMType) :: Union{Nothing,DMType}
    τ1s = Vector{DMType}()
    push!(τ1s, orig1)
    τ2s = Vector{DMType}()
    push!(τ2s, orig2)
    try_eval_isSupremumOf_noarr(orig1, orig2, Vector{DMType}(), Vector{DMType}(), τ1s, τ2s)
end

function try_eval_isSupremumOf_noarr(orig1 :: DMType, orig2 :: DMType, old1s :: Vector{DMType}, old2s :: Vector{DMType}, τ1s :: Vector{DMType}, τ2s :: Vector{DMType}) :: Union{Nothing,DMType}
    old1s_next = copy(old1s)
    append!(old1s_next, τ1s)
    old2s_next = copy(old2s)
    append!(old2s_next, τ2s)

    common = intersect(old1s_next, old2s_next)
    # println("# Searching for supremum: ($orig1, $orig2) ($old1s, $old2s) ($τ1s, $τ2s)")
    @match common begin
        [] =>
        let
            if τ1s == [] && τ2s == []
                throw(ConstraintViolation("The types $τ1 and $τ2 do not have a common supertype!"))
            end
            τ1s_next = Vector{DMType}()
            for τ1 in τ1s
                supers = try_get_direct_supertypes(τ1)
                if supers == nothing # This means that supers could not be determined yet
                    return nothing
                else
                    append!(τ1s_next, supers)
                end
            end

            τ2s_next = Vector{DMType}()
            for τ2 in τ2s
                supers = try_get_direct_supertypes(τ2)
                if supers == nothing # This means that supers could not be determined yet
                    return nothing
                else
                    append!(τ2s_next, supers)
                end
            end

            try_eval_isSupremumOf_noarr(orig1, orig2, old1s_next, old2s_next, τ1s_next, τ2s_next)

        end
        [ρ] =>
        let
            # println("#####################\n# Found sup($orig1, $orig2) = $ρ")
            ρ
        end
        many => throw(ConstraintViolation("Could not find unique supremum of $orig1 and $orig2.\n Solutions are: $many"))
    end
end


############################################################################################
### subtyping constraint simplification

"""
    eval_arr(Φ :: Full{A}, τ1 :: DMType, τ2 :: DMType)

Attempt to simplify a subtyping constraint τ1 ⊑ τ2, potentially adding new variables and
constraints to the context. Return nothing if there is not enough information to simplify,
and throw an error if the constraint is violated.
"""
function try_eval_isSubtypeOf((S,T,C,Σ) :: Full{A}, τ1 :: DMType, τ2 :: DMType) :: Union{Nothing, Full{A}} where {A}
    @match (τ1, τ2) begin
        (τ1, τ2) && if isequal(τ1, τ2) end => return (S,T,C,Σ)
        (Arr(αs, ρ), Arr(βs, ρ2)) => let
            # we add constraints
            # βi ⊑ αi and ρ ⊑ ρ2
            # and hence
            # Arr(αs, ρ) ⊑ Arr(βs, ρ2)
            newCs = [isSubtypeOf(β[2], α[2]) for (α, β) in zip(αs, βs)]
            push!(newCs, isSubtypeOf(ρ, ρ2))

            newCs = [newCs; [isEqual(β[1], α[1]) for  (α, β) in zip(αs, βs)]]

            return (S,T,union(C, newCs),Σ)
        end;
        (TVar(_), Arr(αs, ρ)) => let
            # τ1 must be an Arr too, so we invent variables ds, βs and ρ2 and say τ1 = Arr(βs, ρ2)
            # we also add constraints
            # αi ⊑ βi and ρ2 ⊑ ρ
            # and hence
            # Arr(βs, ρ2) ⊑ Arr(αs, ρ)
            newCs = Constraints()
            βs = []
            for (s, α) in αs
                T, β = addNewName(T, Symbol("sub_atype_"))
                β = TVar(β)
                push!(βs, (s, β))
                push!(newCs, isSubtypeOf(α, β))
            end

            T, ρ2 = addNewName(T, Symbol("sub_rtype_"))
            ρ2 = TVar(ρ2)
            push!(newCs, isSubtypeOf(ρ2, ρ))

            _, uCs = unify_nosubs(τ1, Arr(βs, ρ2))

            (S,T,union(C, newCs, uCs), Σ)
        end;
        (Arr(αs, ρ), TVar(_)) => let
            # τ2 must be an Arr too, so we invent variables ds, βs and ρ2 and say τ2 = Arr(βs, ρ2)
            # we also add constraints
            # βi ⊑ αi and ρ ⊑ ρ2
            # and hence
            # Arr(αs, ρ) ⊑ Arr(βs, ρ2)
            newCs = Constraints()
            βs = []
            for (s, α) in αs
                T, β = addNewName(T, Symbol("sub_atype_"))
                β = TVar(β)
                push!(βs, (s, β))
                push!(newCs, isSubtypeOf(β,α))
            end

            T, ρ2 = addNewName(T, Symbol("sub_rtype_"))
            ρ2 = TVar(ρ2)
            push!(newCs, isSubtypeOf(ρ, ρ2))

            _, uCs = unify_nosubs(τ2, Arr(βs, ρ2))

            (S,T,union(C, newCs, uCs), Σ)
        end;
        (Arr(_,_), _) => throw(ConstraintViolation("Invalid subtyping constraint $τ1 ⊑ $τ2; second argument must be an Arrow."))
        (_, Arr(_,_)) => throw(ConstraintViolation("Invalid subtyping constraint $τ1 ⊑ $τ2; first argument must be an Arrow."))
        (TVar(_), _) => return nothing
        (_, TVar(_)) => let
            # this kind of constraint can only appear from subtyping constraints made during apllication typechecking.
            # the right-hand side is a type var A is only used as the argument type of the applied function in that
            # specific single application, hence there can be no other subtype constraints B < A and we can safely
            # unify the two.
            _, newC  = unify_nosubs(τ1, τ2)
            return (S,T,union(C,newC),Σ)
        end
        _ => let
            # traverse the subtype relation graph upwards from τ1, to see if we come across τ2.
            supers = try_get_direct_supertypes(τ1)
            if isnothing(supers)
                # we don't know the supertypes, so we cannot say anything about if τ1 ⊑ τ2
                return nothing
            else
                # see if one of the supertypes of τ1 is a subtype of τ2
                maybe = false # to remember whether we found a super that may be a subtype of τ2 but we don't know.
                for σ in supers
                    try
                        res = try_eval_isSubtypeOf((S,T,C,Σ), σ, τ2) # this might throw
                        if isnothing(res)
                            maybe = true
                        else
                            return res
                        end
                    catch err
                        if !(err isa ConstraintViolation)
                            rethrow(err)
                        end
                    end
                end
                # if τ1 has no supertypes (root of the tree) or none of the supers is a subtype of τ2,
                # τ1 can't be a subtype of τ2 either
                maybe ? nothing : throw(ConstraintViolation("Expected $τ1 to be a subtype of $τ2, but it is not."))
            end
        end;
    end
end

#=

# Use this, when τ1 and τ2 do not contain arrows
struct Res_IsNotSubtype end
struct Res_CouldNotGetSupers end

function check_isSubtypeOf_noarr((S,T,C,Σ) :: Full{A}, τ1 :: DMType, τ2 :: DMType) :: Union{Res_IsNotSubtype, Res_CouldNotGetSupers, Full{A}} where {A}
     try
         _, newC  = unify_nosubs(τ1, τ2)
         return (S,T,union(C,newC),Σ)
     catch # if unification is not possible, try if any of τ1s supertypes is a subtype of τ2
         supers = try_get_direct_supertypes(τ1)
         if supers == nothing
             return Res_CouldNotGetSupers()
         else
             for σ in supers
                 res = check_isSubtypeOf_noarr((S,T,C,Σ), σ, τ2)
                 if (res isa Res_IsNotSubtype) || (res isa Res_CouldNotGetSupers)
                     continue
                 else
                     return res
                 end
             end
             return Res_IsNotSubtype()
         end
     end
 end
=#

############################################################################################
### Definition of the subtyping relation

"Get the list of direct supertypes of `τ`, or return nothing if `τ` has type variables."
function try_get_direct_supertypes(τ :: DMType) :: Union{Nothing,Vector{DMType}}
    @match τ begin
        Constant(DMInt(), η)   => [Constant(DMReal(), η), DMInt()]
        Constant(DMReal(), η)  => [DMReal()]
        Constant(TVar(_), _)   => nothing
        Constant(τ, _)         => error("A constant of type $τ is invalid.")

        DMInt()                => [DMReal()]
        DMReal()               => []

        Arr(_, _)           => error("Unreachable location reached. Tried to get direct super types of an arrow type.")

        _                      => nothing
    end
end
