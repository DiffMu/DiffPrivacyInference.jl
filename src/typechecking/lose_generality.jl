
include("../typechecking/monadic_simplify.jl")


"Make types involved in underspecified operations non-constant to enable simplification."
# this is permitted as ops on non-consts have worse sensitivity.
function make_typeOp_nonconst(constr :: Constr) :: TC
    # get non-constant type of τ
    function relax_numeric_type(τ :: DMType) :: DMType
        @match τ begin
            Constant(τ1, _) => relax_numeric_type(τ1)
            X => X
        end
    end

    # if c is in C already, return nothing
    function add_c_ifnew(c::Constr) :: TC
        function mconstr(S,T,C) :: MType{Union{Nothing, Tuple{}}}
            if c in C
                return (S,T,C,SCtx()), nothing
            else
                return (S,T,[C; c],SCtx()), ()
            end
        end
        TC(mconstr)
    end

    @match constr begin
        isTypeOpResult(_, _, (Binary(_, τ1, τ2))) => @match (τ1, τ2) begin
            (TVar(x), Y) => add_c_ifnew(isEqualType(x, relax_numeric_type(Y)))
            (X, TVar(y)) => add_c_ifnew(isEqualType(y, relax_numeric_type(X)))
            (_, _) => mreturn(TC, nothing)
        end;
        _ => mreturn(TC, nothing)
    end
end

"""
    simplify_constraints_lose_generality((S,T,C,Γ)::Full{SensitivityContext}, τ::DMType)

Assume all free type variables are non-constant and convert constant types involved in
underspecified operations to their non-constant equivalent. Then evaluate the constraints
in `C`, updating `τ`.

This worsens the sensitivity, as non-constant types yield larger sensitivity penalty. It's
hence legal, but should only be done after attempting to simplify without assumptions for
best results.
"""
function simplify_constraints_lose_generality() :: TC

    # add isNonConstant constraints for all typevars
    make_all_nonconstant() = TC((S,T,C) -> ((S,T,union(C,[isNotConstant(TVar(t)) for t in T.names]) ,SCtx()), ()))

    # find an underspecified typeOp constraint, make all types involved nonconst, then recurse.
    function recurse_lose_generality(Ci::Constraints) :: TC
        if isempty(Ci)
            mreturn(TC, ())
        else
            @mdo TC begin
                lg <- make_typeOp_nonconst(Ci[1])
                r <- (isnothing(lg) ? recurse_lose_generality(Ci[2:end]) : simplify_constraints_lose_generality())
                return ()
            end
        end
    end

    @mdo TC begin
        _ <- make_all_nonconstant()
        _ <- msimplify_constraints()
        Cs <- extract_Cs()
        _ <- recurse_lose_generality(Cs)
        return ()
    end

end

