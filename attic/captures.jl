include("../core/definitions.jl")
include("../core/operations.jl")
include("../core/unification.jl")
include("../utils/logging.jl")

# functions can use variables from outer scope that are not yet defined at function definition time, eg
#   function scope()
#      g(x) = x+y
#      y = 10
#      g(1)
#   end
# type of g before line 2 will be [y::Y](x::X) => X+Y, y is a "capture"
# upon application in line 3, all captures have to be defined, else julia will error.
# this function removes captured variables that are in Γ from τ_lam, treating them like additional function arguments
# and performing necessary context operations.
# type of g after applying this function would be [](x::X) => X+Y
function resolve_captures((S, T, C, Γ)::Full{TypeContext}, τ_lam::DMType, Σ::SCtx) :: Tuple{Full{SCtx}, DMType, Substitutions}

    if isempty(Γ)
        return (S,T,C,Σ), τ_lam, Substitutions()
    end

    printdebug(Log_ResolveCaptures(), "== Entering resolve ($τ_lam)")
    printdebug(Log_ResolveCaptures(), "svars:   $S")
    printdebug(Log_ResolveCaptures(), "tvars:   $T")
    printdebug(Log_ResolveCaptures(), "constraints:   $C")
    printdebug(Log_ResolveCaptures(), "context:   $Γ")
    printdebug(Log_ResolveCaptures(), "--")

    function return_logged(Σ_res, τ_res, σs_res)
        printdebug(Log_ResolveCaptures(), "--")
        printdebug(Log_ResolveCaptures(), "resolve result is:")
        printdebug(Log_ResolveCaptures(), "type:   $τ_res")
        printdebug(Log_ResolveCaptures(), "substs: $σs_res")
        printdebug(Log_ResolveCaptures(), "== Exiting resolve ($τ_lam)")
        Σ_res, τ_res, σs_res
    end

    σ = []

    @match τ_lam begin
        DMChoice(choices) => let
            newchoices = DMSingleChoice[]
            for (b, τ_choice, con) in choices
                τ_choice, con = @match τ_choice begin
                    Arr(caps, as, r) => let
                        # all choices get their resolve done with the same input contexts
                        (_,_,con,_), τ_choice, σ_r = resolve_captures((S,T,con,Γ), τ_choice, Σ)
                        # substitutions are recorded as constraints in the choice.
                        con = [con; substitionsToConstraints(σ_r)]
                        (τ_choice, con)
                    end
                    _ => error("invalid type $τ_choice in choice.")
                end
                newchoices = [newchoices; (b, τ_choice , con)]
            end
            return_logged((S,T,C,Σ), DMChoice(newchoices), σ)
        end;

        Arr(caps, as, r) => let

            σ = Substitutions()

            newcaps = Tuple{Symbol, Sensitivity, DMType}[]
            for i in 1:length(caps)
                (c, s, τ_cap) = caps[i]

                # resolve the capture type
                (S,T,C,Σ), τ_cap, σ_res  = resolve_captures((S,T,C,Γ), τ_cap, Σ)
                Γ,s,caps = distribute_substitute((Γ,s,caps), σ_res)
                σ = [σ; σ_res]

                if(haskey(Γ, c)) # c can be resolved
                    # we treat the capture like a var(c) term that's a normal function argument
                    Σ_var = SCtx(c => (1, Γ[c]))
                    τ_var = Γ[c]

                    # of course captures can capture things as well
                    (S,T,C,Σ_var), τ_var, σ_res  = resolve_captures((S,T,C,Γ), τ_var, Σ_var)
                    Γ,Σ,s,caps = distribute_substitute((Γ,Σ,s,caps), σ_res)
                    σ = [σ; σ_res]

                    # the type of the var(c) term must be what is requested in the function signature
                    (S,T,C,Σ), (Γ,Σ_var,s,caps), τ_cap, _, σ_u = unify_DMType_withExtra((S,T,C,Σ), (Γ,Σ_var,s,caps), τ_cap, τ_var)
                    σ = [σ; σ_u]

                    # compute the result context (like in normal application rule)
                    (S,T,C,Σ), σ_add = add(S,T,C,Σ, scale(s, Σ_var))
                    Γ,Σ,s,τ_cap,caps = distribute_substitute((Γ,Σ,s,τ_cap,caps), σ_add)
                    σ = [σ ; σ_add]
                else
                    # keep captures that cannot be resolved.
                    newcaps = [newcaps ; (c, s, τ_cap)]
                end
            end

            as,r,newcaps = distribute_substitute((as,r,newcaps), σ)

            newas = Tuple{Sensitivity, DMType}[]
            for i in 1:length(as)
                (s, τa) = as[i]

                # resolve all captures in the function arguments as well.
                (S,T,C,Σ), newa, σ_a = resolve_captures((S,T,C,Γ), τa, Σ)
                Γ,r,newcaps,as,newas = distribute_substitute((Γ,r,newcaps,as,newas), σ_a)
                newas = [newas; (s, newa)]
                σ = [σ; σ_a]
            end

            # also in the result type
            (S,T,C,Σ), newr, σ_r = resolve_captures((S,T,C,Γ), r, Σ)
            newcaps,newas = distribute_substitute((newcaps,newas), σ_r)
            σ = [σ; σ_r]

            # finally, our newly resolved function type!
            return_logged((S,T,C,Σ), Arr(newcaps, newas, newr), σ)
        end;

        # things that are not functions cannot capture.
        _ => return_logged((S,T,C,Σ), τ_lam, σ)
    end
end

