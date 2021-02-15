include("../core/contexts.jl")
include("../typechecking/subtyping.jl")


############################################################################################
### Utils

"An error to throw upon finding a constraint that is violated."
struct ConstraintViolation <: Exception
   msg::String
end


"If `τ` is numeric, return `()`. If it's unclear, return nothing. If it's not numeric, error."
function check_numeric(τ::DMType) :: Union{Nothing,Tuple{}}
   @match τ begin
      TVar(_) => nothing
      DMInt() => ()
      DMReal() => ()
      #Idx(_) => ()
      Constant(τ2, a) => check_numeric(τ2)
      _ => throw(ConstraintViolation("Expected $τ to be a numeric type."));
   end
end


function set_or_unify(a :: SymbolOrSens, b :: Sensitivity) :: Tuple{Constraints, Substitutions}
      if a isa Symbol
         ([], [(a, b)])
      else
         (_, co, σ) = unify_Sensitivity(a, b)
         (co, σ)
      end
end


function set_or_unify(a :: SymbolOrType, b :: DMType) :: Tuple{Constraints, Substitutions}
      if a isa Symbol
         ([], [(a, b)])
      else
         (_, co, σ) = unify_DMType(a, b)
         (co, σ)
      end
end


"""
    try_apply_with_extra(f, Φ, args, constructor)

Apply `f(Φ, τ)` to all types `τ` in `args`, updating `Φ`. If `f` does nothing on all `τ`,
return nothing. Else return the updated `Φ` and the new type `constructor(τs)`.

# Arguments
- `f::Function`: some map `C x DMType -> Union{Nothing, (C, DMType)}`.
- `Φ::C where C`: something to get updated by `f`, e.g. a `SensitivityContext`.
- `args::Union{Tuple, Vector}`: list of things to apply `f` to.
- `constructor::Function`: the constructor to apply to the resulting list.
"""
function try_apply_with_extra(f, Φ::C, args::Union{Tuple, Vector}, constructor) :: Union{Nothing, Tuple{C, A} where A} where {C}
    newargs = []
    something = false
    for τ in args
        # we have to match here every possible argument type of a DMType.
        res = @match τ begin
            ::DMType => let
                f(Φ, τ)
            end;
            ::Union{Constr, DMTypeOp} => let
                # mxu will hate me for this :D
                τconstructor = typeof(τ) # the constructor of τ
                τargs = map(fld->getfield(τ,fld), fieldnames(τconstructor)) # the arguments of τ
                try_apply_with_extra(f,Φ,τargs,τconstructor)
            end
            ::Tuple => let
                try_apply_with_extra(f,Φ,τ,tuple)
            end;
            ::Vector => let
                try_apply_with_extra(f,Φ,τ,(v...)->[v...])
            end;
            ::SymbolOrSens => nothing;
            ::DMTypeOps_Unary => nothing;
            ::DMTypeOps_Binary => nothing;
            ::DMTypeOps_Ternary => nothing;
            _ => error("unexpected thing $τ in $constructor($args)"); #TODO think this through
        end
        if !isnothing(res)
            (Φ, τ) = res
            something = true
        end
        push!(newargs, τ)
    end
    if something
        println("trying to construct $constructor with args $newargs")
        return (Φ, constructor(newargs...))
    else
        return nothing
    end
end


############################################################################################
### Resolving Types

#TODO this does not really need Σ, as it's never modified. rewrite of simplify_constraints pending
#function try_resolve_choice((S,T,C)::Tuple{NameCtx, NameCtx, Constraints}, τ::DMChoice) :: Union{Nothing, Tuple{Tuple{NameCtx, NameCtx, Constraints}, DMType}}
"""
    try_resolve_choice((S,T,C,Σ), τ::DMChoice)

Attempt to reduce `τ` by trying to simplify the constraints of each choice and discarding
it if they turn out to be unsatisfiable. Return nothing if no reduction was possible, and
the new context and the reduced `τ` if it was.
"""
function try_resolve_choice((S,T,C,Σ)::Full{SensitivityContext}, τ::DMChoice) :: Union{Nothing, Tuple{Full{SCtx}, DMType}}
    @match τ begin
        DMChoice([])              => error("$τ has no valid choice.");
        DMChoice([(flag, c, Cc)]) => return ((S,T,union(C,Cc,[isEqual(flag, 1)]),Σ), c);
        DMChoice(choices) => let
            # see if we can remove choices because their constraints are not satisfiable
            newchoices = DMSingleChoice[]
            for (flag, c, Cc) in choices
                try
                    # try to simplify all constraints of this choice
                    (nS,nT,Cc,_), newc = simplify_constraints((S,T,Cc,Σ), c) # we can throw Σ away because it never gets changed
                    # TODO constraint evaluation can create new Svars and Tvars if there is a constraint τ ⊑ Arr(...)
                    # TODO right now, we would have to add these only to the choice, not the global S and T, which is messy.
                    # TODO we forbid it for now, as ForAll will relieve us of this
                    @assert issubset(nS.names, S.names) && issubset(nT.names, T.names) "choice constraint evaluation yielded other svars/tvars\n $(setdiff(nS.names, S.names))\n $(setdiff(nT.names,T.names))"

                    # if there was no violated constraint, try to resolve the c
                    # it is sufficient to only input Cc here and not C, as all substitutions from the outer constraints were done in Cc too
                    res = try_resolve_type((S,T,Cc,Σ), newc)
                    if !isnothing(res)
                        (_,_,Cc,_), newc = res
                    end

                    # add the refined (or original, if no refinement happened) choice
                    push!(newchoices, (flag, newc, Cc))
                catch err
                    # upon constraint violation, the choice does not get added to newchoices.
                    C = [C; isEqual(flag, 0)] # choice discarded, set flag to 0.
                    if !(err isa ConstraintViolation)
                        rethrow(err)
                    end
                end
            end
            if newchoices != choices
                @match newchoices begin
                    []              => error("$τ has no valid choice.");
                    [(flag, c, Cc)] => return ((S,T,union(C, Cc,[isEqual(flag, 1)]), Σ), c);
                    _               => return let
                        println("new choices: $newchoices, type $(typeof(newchoices))")
                        ((S,T,C,Σ), DMChoice(newchoices))
                    end;
                end
            else
                return nothing
            end
        end;
    end;
end


"Try to resolve all `DMChoice` and `ForAll` types in `τ`, recursively."
function try_resolve_type(STCΣ::Full{SCtx}, τ::DMType) :: Union{Nothing, Tuple{Full{SCtx}, DMType}}
    # TODO do we have to deal with captures here?
    @match τ begin
        ::DMChoice => try_resolve_choice(STCΣ, τ);
        ::ForAll => error("resolving ForAlls not implemented."); # TODO
        _ => let
            # mxu will hate me for this :D
            τctor = typeof(τ) # the constructor of τ
            τargs = map(f->getfield(τ,f), fieldnames(τctor)) # the fields of τ
            # recursively resolve all types in all fields of τ
            try_apply_with_extra(try_resolve_type,STCΣ,τargs,τctor)
        end;
    end
end


"Try to resolve all types appearing in the constraints in `C`."
function try_resolve_constraints(STCΣ::Full{SCtx}) :: Union{Nothing, Full{SCtx}}
    _,_,C,_ = STCΣ
    res = try_apply_with_extra(try_resolve_type, (STCΣ), C, (v...)->[(v...)])
    if isnothing(res)
        return nothing
    else
        (S,T,C,Σ), _ = res
        return (S,T,C,Σ)
    end
end


"Try to resolve all types in `Σ`."
function try_resolve_sigma((S,T,C,Σ)::Full{SCtx}) :: Union{Nothing, Full{SCtx}}
    for (x,(s,τ)) in Σ
        res = try_resolve_type((S,T,C,Σ), τ)
        if !isnothing(res)
            (S,T,C,Σ), newτ = res
            Σ[x] = (s,newτ)
            return try_resolve_sigma((S,T,C,Σ))
        end
    end
    return nothing
end


############################################################################################
### Constraint Evaluation

"""
    try_simplify_Constr((S,T,AllCs,Σ), c)

Try if `c` can be simplifyd. If it cannot, return nothing. If it can, remove `c` from
`AllCs`, add any new constraints made during evaluation to `AllCs`, and return the new
context and the substitutions made during evaluation.
"""
function try_simplify_Constr((S,T,AllCs,Σ) :: Full{SCtx}, c :: Constr) :: Union{Nothing, Tuple{Full{SCtx},Substitutions}}

    # This means the constraint was successfully discharged
    # and no new constraints or substitutions apply
    function return_discharge()
        C = copy(AllCs)
        filter!(x -> x != c, C)
        (S,T,C,Σ),[]
    end

    # This means something other that simple discharging happened.
    function return_simple(newCs :: Constraints, σs :: Substitutions)
        C = vcat(AllCs,newCs)
        filter!(x -> x != c, C)
        apply_subs((S,T,C,Σ),σs), σs
    end

    @match c begin
        isEqual(s1,s2) => let
            res = try_unify_Sensitivity(s1,s2)
            if res isa Nothing
                nothing
            else
                (_, σ) = res
                return_simple([], σ)
            end
        end;
        isLessOrEqual(s1, s2) => let
            n1 , n2 = (try_destructure_Sensitivity(s1), try_destructure_Sensitivity(s2))

            @match (n1, n2) begin
                (::EvaluatedNumber, ::EvaluatedNumber) => n1 <= n2 ? return_discharge() : throw(ConstraintViolation("exprected $n1 <= $n2"))
                (_ , _) => nothing
            end
        end
        isNumeric(a) => let
            if check_numeric(a) isa Nothing
                nothing
            else
                return_discharge()
            end
        end;
        isNotConstant(a) => @match a begin
            Constant(_, _) => throw(ConstraintViolation("Expected $a not to be a singleton type."))
            TVar(_) => nothing
            _ => return_discharge()
        end;
        isTypeOpResult(sv, τ, op) => let
            otherCs = copy(AllCs)
            filter!(x -> x != c, otherCs)
            res = signature((S,T,otherCs,Σ), op)
            if res isa Nothing
                return nothing
            else
                (vs, vt, (S,T,co,Σ)) = res
                @assert length(vs) == length(sv) "operator argument number mismatch"

                σ = Substitutions()

                for (s, v) in zip([sv; τ], [vs; vt])
                    (co1, σ1) = set_or_unify(apply_subs(s, σ), apply_subs(v, σ))
                    σ = vcat(σ, σ1)
                    co = vcat(co, co1)
                end

                apply_subs((S,T,co,Σ),σ), σ
            end;
        end;
        isSubtypeOf(τ1, τ2) =>
        let
            otherCs = copy(AllCs)
            filter!(x -> x != c, otherCs)
            try_eval_isSubtypeOf((S,T,otherCs,Σ), τ1, τ2)
        end;
        isSupremumOf(τ1, τ2, ρ) =>
        let
            otherCs = copy(AllCs)
            filter!(x -> x != c, otherCs)
            try_eval_isSupremumOf((S,T,otherCs,Σ), τ1, τ2, ρ)
        end;
        isEqualType(t1, t2) => begin
            otherCs = copy(AllCs)
            filter!(x -> x != c, otherCs)
            FF, _, σ = unify_DMType((S,T,otherCs,Σ), t1, t2)
            FF , σ
        end
    end
end


"""
    simplify_constraints((S,T,C,Σ), τ)

Evaluate all constraints in `C` that can be simplified, also trying to resolve choices and
foralls. Carry out all substitutions on `τ` and return the new context and `τ`.
"""
function simplify_constraints(STCΣ::Full{SensitivityContext}, τ::DMType) :: Tuple{Full{SCtx}, DMType}

    # try if Σ contains any types that can be resolved (i.e. choices with nonsatisfiable constraints).
    res = try_resolve_sigma(STCΣ)
    if !isnothing(res)
        #@assert issubset(res[3],STCΣ[3]) "resolve yielded new constraint!\n $(setdiff(res[3],STCΣ[3]))"
        newcs = setdiff(res[3],STCΣ[3])
        @assert all([c isa isEqual for c in newcs])  "resolve yielded invalid new constraint!\n $newcs"
        STCΣ = res
    end

    # try if C contains any types that can be resolved.
    res = try_resolve_constraints(STCΣ)
    if !isnothing(res)
        #@assert issubset(res[3],STCΣ[3]) "resolve yielded new constraint!\n $(setdiff(res[3],STCΣ[3]))"
        newcs = setdiff(res[3],STCΣ[3])
        @assert all([c isa isEqual for c in newcs])  "resolve yielded invalid new constraint!\n $newcs"
        STCΣ = res
    end

    # try if τ contains any types that can be resolved.
    res = try_resolve_type(STCΣ, τ)
    if !isnothing(res)
        #@assert issubset(res[1][3],STCΣ[3]) "resolve yielded new constraint(s)!\n $(setdiff(res[1][3],STCΣ[3]))"
        newcs = setdiff(res[1][3],STCΣ[3])
        @assert all([c isa isEqual for c in newcs])  "resolve yielded invalid new constraint!\n $newcs"
        STCΣ, τ = res
    end

    # try to simplify all constraints in C. if any of them can be simplifyd, call simplify_constraints recursively.
    (S,T,C,Σ) = STCΣ
    for constr in C
        # try to simplify constr
        STCΣσ = try_simplify_Constr((S,T,C,Σ), constr)
        if !isnothing(STCΣσ)
            STCΣ, σ = STCΣσ
            τ = apply_subs(τ, σ)
            println("###simplified $constr, got subs $σ\n\n")
            println("    recursing with:\n$STCΣ\n    and type: $τ\n")
            # recursive call
            return simplify_constraints(STCΣ, τ)
        end
    end
    println("#### simplify done:\n$STCΣ\n    and type: $τ\n")
    return ((S, T, unique(C), Σ), τ)
end

