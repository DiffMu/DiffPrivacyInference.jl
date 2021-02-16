
include("../typechecking/monadic_simplify.jl")

"""
simplify_constraints_lose_generality() :: TC

Simplify as many constraints as possible, then assume all free type variables involved in
DMTypeOps are non-constant and simplify again.

This worsens the sensitivity, as non-constant types yield larger sensitivity penalty. It
is hence legal to do, but should only be done if no other simplification is possible for best results.
"""
function simplify_constraints_lose_generality() :: TC

    # try to simplify a less general version of the first constraint in Ci by assuming all free
    # type variables involved are nonconstant (this makes sensitivity worse).
    # in case that was possible, recurse lose_generality with the new state.
    # else pop the constraint and recurse try_simplify_constraints with the next one in Ci.
    function try_simplify_constraints(Ci::Constraints) :: TC
        if isempty(Ci)
            mreturn(TC, nothing)
        else
            @match Ci[1] begin
                isTypeOpResult(sv, τres, op) => let #TODO clean this up

                    function mconstr(S,T,C,Σ) :: MType{Union{Nothing, Tuple{}}}
                        otherCs = filter!(x -> !isequal(x, Ci[1]), deepcopy(C))
                        res = signature((S,T,otherCs,Σ), op, true) # pass the flag for making typevars nonconst
                        if res isa Nothing
                            try_simplify_constraints(Ci[2:end]) # nothing happened, try the next constraint.
                        else
                            (vs, vt, (S,T,co,_)) = res
                            @assert length(vs) == length(sv) "operator argument number mismatch"

                            co = [co; unify_nosubs(τres, vt)[2]]
                            co = [co; map(x->unify_Sensitivity_nosubs(x...)[2], zip(sv, vs))...]

                            return ((S,T,co,Σ), ())
                        end
                    end

                    @mdo TC begin
                        M <- TC(mconstr)
                        _ <- simplify_constraints_lose_generality()
                        return ()
                    end
                end;
                _ => try_simplify_constraints(Ci[2:end]) # nothing happened, try the next constraint.
            end
        end
    end

    @mdo TC begin
        _ <- msimplify_constraints() # simplify once without changing things
        Cs <- extract_Cs()
        _ <- try_simplify_constraints(Cs) # lose generality and recurse
        return ()
    end

end

