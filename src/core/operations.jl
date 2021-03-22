
############################################################################################
### Constancy Check

"Check whether `τ` contains any non-constant types."
function check_not_constant(τ :: DMType, tvars_nonconst::Bool) :: Bool
   @match τ begin
      DMInt() => true
      DMReal() => true
      #Idx(_) => true
      Constant(_, _) => false
      DMTup(Ts) => any(map(T->check_not_constant(T, tvars_nonconst), Ts))
      Arr(_, _) => true
      ArrStar(_, _) => true
      TVar(t) => tvars_nonconst
      DMMatrix => true
   end
end


############################################################################################
### Signatures


"""
    signature(STCΣ :: Full{A}, top::DMTypeOp)

Return the sensitivity signature of `top`, if it is clear yet.

If the types of `top` are not yet sufficiently specified to determine the signature, return
`nothing`. Else, return the signature as specified in the Duet paper, as well as the return
type of the operation and the new context with new constraints in case the op required any.
"""
function signature(STCΣ :: Full{A}, top::DMTypeOp, tvars_nonconst = false) :: Union{Nothing, Tuple{Array{Sensitivity}, DMType, Full{A}}} where A

    # ensure all types are non-constant
    cINC(Xs::DMType...) = all(X -> check_not_constant(X, tvars_nonconst), Xs)

    # if the types are equal most operations result in that same type, if they are not most default to real.
    comT(X, Y) = (X==Y ? X : DMReal())

    # resWithSup(η₁, η₂, X, Y, C) = (X == Y ? (η₁, η₂, X, X, C) : (η₁, η₂, X, Y, [C ; isSupremumOf(X,Y,result_type)]))

    # get the supremum of τ1 and τ2, without simplifying constraints.
    function supremum(τ1 :: DMType, τ2 :: DMType) :: DMType
        (STCΣ, τres) = getSupremumOf(STCΣ, τ1, τ2)
        τres
    end

    # add the new constraints and return the signature
    function return_with_new_constraints(sensitivities, ty, newCs)
        S, T, C, Σ = STCΣ
        (sensitivities, ty, (S, T, [C ; newCs], Σ))
    end


    # check if we know for sure that τ is numeric
    function is_numeric(τ::DMType) :: Bool
        @match τ begin
            DMInt() => true
            DMReal() => true
            Constant(τ2, _) => is_numeric(τ2)
            TVar => isNumeric(τ) in STCΣ[3]
            _ => false
        end
    end

    @match top begin
        Unary(op, τ) => let
            (v, vt, co0) = @match (op, τ) begin
                (DMOpCeil(), Constant(X, η))                   => (0, Constant(DMInt(), ceil(η)), []);
                (DMOpCeil(), X)            && if cINC(X) end => (1, DMInt(), []);
                (DMOpCeil(), TVar(_))                          => return nothing;

                (DMOpGauss(), DMMatrix(L2, _, dims, X)) && if is_numeric(X) end => (1, DMMatrix(L∞, U, dims, DMReal()), []);
                (DMOpGauss(), X)            && if is_numeric(X) end => (1, DMReal(), []);
                (DMOpGauss(), TVar(_))                          => return nothing;

                _ => error("No unary operation $op available on operand of type $τ.");
            end;
            return return_with_new_constraints([v], vt, co0)
        end;
        Binary(op, τ1, τ2) => let
            (v1, v2, vt, co0) = @match (op, τ1, τ2) begin
                (DMOpAdd(), Constant(X, η1), Constant(Y, η2))  => (0, 0, Constant(supremum(X,Y), η1 + η2), []);
                (DMOpAdd(), X, Y)                              && if cINC(X,Y) end => (1, 1, supremum(X,Y), []);
                (DMOpAdd(), Constant(X, η1), Y)                && if cINC(Y) end => (0, 1, supremum(X,Y), []);
                (DMOpAdd(), X, Constant(Y, η2))                && if cINC(X) end => (1, 0, supremum(X,Y), []);
                (DMOpAdd(), Constant(TVar(_), _), Y)           => return nothing;
                (DMOpAdd(), X, Constant(TVar(_), _))           => return nothing;
                (DMOpAdd(), TVar(_), Y)                        => return nothing;
                (DMOpAdd(), X, TVar(_))                        => return nothing;

                (DMOpMul(), Constant(X, η1), Constant(Y, η2))  => (0, 0, Constant(supremum(X,Y), η1 * η2), []);
                (DMOpMul(), X, Y)                              && if cINC(X,Y) end => (∞, ∞, supremum(X,Y), []);
                (DMOpMul(), Constant(X, η1), Y)                && if cINC(Y) end => (0, η1, supremum(X,Y), []);
                (DMOpMul(), X, Constant(Y, η2))                && if cINC(X) end => (η2, 0, supremum(X,Y), []);
                (DMOpMul(), Constant(TVar(_), _), Y)           => return nothing;
                (DMOpMul(), X, Constant(TVar(_), _))           => return nothing;
                (DMOpMul(), TVar(_), Y)                        => return nothing;
                (DMOpMul(), X, TVar(_))                        => return nothing;

                (DMOpEq(), Constant(X, η1), Constant(Y, η2))  => (0, 0, DMInt(), []);
                (DMOpEq(), X, Y)                               && if cINC(X,Y) end => (1, 1, DMInt(), []);
                (DMOpEq(), Constant(X, η1), Y)                 && if cINC(Y) end => (0, 1, DMInt(), []);
                (DMOpEq(), X, Constant(Y, η2))                 && if cINC(X) end => (1, 0, DMInt(), []);
                (DMOpEq(), Constant(TVar(_), _), Y)            => return nothing;
                (DMOpEq(), X, Constant(TVar(_), _))            => return nothing;
                (DMOpEq(), TVar(_), Y)                         => return nothing;
                (DMOpEq(), X, TVar(_))                         => return nothing;

                # TODO figure out how to handle negative numbers.
                (DMOpSub(), Constant(X, η1), Constant(Y, η2))  => (0, 0, Constant(comT(X,Y), η1 - η2), []); # [isLessOrEqual(η2, η1)]);
                (DMOpSub(), X, Y)                              && if cINC(X,Y) end => (1, 1, comT(X,Y), []);
                (DMOpSub(), Constant(_, _), Y)                 => return nothing;
                (DMOpSub(), X, Constant(_, _))                 => return nothing;
                (DMOpSub(), TVar(_), Y)                        => return nothing;
                (DMOpSub(), X, TVar(_))                        => return nothing;

                (DMOpDiv(), Constant(X, η1), Constant(Y, η2))  => (0, 0, Constant(DMReal(), η1 / η2), []);
                (DMOpDiv(), X, Y)                              && if cINC(X,Y) end => (∞, ∞, DMReal(), []);
                (DMOpDiv(), Constant(X, η1), Y)                && if cINC(Y) end => (0, ∞, DMReal(), []);
                (DMOpDiv(), X, Constant(Y, η2))                && if cINC(X) end => (1/η2, 0, DMReal(), []);
                (DMOpDiv(), Constant(TVar(_), _), Y)           => return nothing;
                (DMOpDiv(), X, Constant(TVar(_), _))           => return nothing;
                (DMOpDiv(), TVar(_), Y)                        => return nothing;
                (DMOpDiv(), X, TVar(_))                        => return nothing;

                (DMOpMod(), Constant(X, η1), Constant(Y, η2))  => (η2, η1, Constant(comT(X,Y), η1 % η2), []);
                (DMOpMod(), X, Y)                              && if cINC(X,Y) end => (∞, ∞, comT(X,Y), []);
                (DMOpMod(), X, Constant(Y, η2))                && if cINC(X) end => (η2, 0, comT(X,Y), []);
                #(DMOpMod(), Idx(η1), Idx(η2))                 => (η1, η2, Idx(min(η1, η2)), []);
                (DMOpMod(), Constant(TVar(_), _), Y)           => return nothing;
                (DMOpMod(), X, Constant(TVar(_), _))           => return nothing;
                (DMOpMod(), TVar(_), Y)                        => return nothing;
                (DMOpMod(), X, TVar(_))                        => return nothing;

                (op, τ1, τ2) => error("No binary operation $op available on operands of types $τ1 and $τ2.");
            end;
            return return_with_new_constraints([v1, v2], vt, co0)
        end;
        Ternary(op, τ1, τ2, τ3) => let
            (v1, v2, v3, vt, co0) = @match (op, τ1, τ2, τ3) begin
                (DMOpLoop(), Constant(DMInt(), η), X, Arr(xs, Y)) => let
                    s = xs[2][1]
                    (0, s^η, η, X, [])
                 end
                 (DMOpLoop(), DMInt(), X, Arr(xs, Y))             => let
                     s = xs[2][1]
                     (1, 1, ∞, X, [isLessOrEqual(s, 1)])
                end
                (DMOpLoop(), TVar(_), X, TVar(_))                 => return nothing;
                (DMOpLoop(), TVar(_), X, Arr(_, _))               => return nothing;
                (DMOpLoop(), DMInt(), X, TVar(_))                 => return nothing;
                (DMOpLoop(), Constant(TVar(_), _), X, TVar(_))    => return nothing;
                (DMOpLoop(), Constant(TVar(_), _), X, Arr(_, _))  => return nothing;
                (DMOpLoop(), X, _, Z)                             => error("loop index type $X and body type $Z are illegal.");

                (op, _, _, _)                                     => error("ternary operation $op unknown.")
            end
            return ([v1, v2, v3], vt, co0)
        end;
    end
end
