include("../core/contexts.jl")
include("../core/DMIR.jl")
include("../typechecking/subtyping.jl")
include("../utils/logging.jl")

using MLStyle


check_sens(t::DMTerm) = check_sens((emptySVarCtx(),emptyTVarCtx(),emptyConstraints(),TypeContext()), t)


# input: type and sensitivity variables and constraints on them under which to check
# output: contexts and inferred type, plus all type/sensitivity variable substitutions made in the process.
function check_sens((S,T,C,Γ)::Full{TypeContext}, t::DMTerm) :: Tuple{Full{SensitivityContext}, DMType, Substitutions}
    @match t begin
        sng(n) =>
        let
            Σ = SCtx(i => (0, α) for (i, α) in Γ)
            # maybe n actually is a constant
            τ = @match n begin
                ::Int => DMInt()
                ::Real => DMReal()
                _ => let
                    T, t = addNewName(T, Symbol("$n", "_"))
                    TVar(t)
                end;
            end
            (S,T,C,Σ), Constant(τ, n), Substitutions()
        end;
        var(x,τ) =>
        if haskey(Γ,x)
            Σ = SCtx(i => ((i==x ? 1 : 0), α) for (i, α) in Γ)
            (S,T,C,Σ), Σ[x][2], Substitutions()
        else
            error("Variable $x not in scope!")
        end;
        op(f, args) => let
            σ = Substitutions()
            τs = DMType[]
            Σs = []

            # check the branches
            for arg in args
                (S,T,C,Σ1), τ1, σ1 = check_sens((S,T,C,Γ), arg)
                Γ = apply_subs(Γ, σ1)
                Σs = [Σs; Σ1]
                τs = [τs; τ1]
                σ = [σ; σ1]
            end
            # in case the a branch substituted things that appear in the results of the others:
            # substitute!
            Γ, Σs, τs = distribute_substitute((Γ, Σs, τs), σ)

            # add contraint
            op = getDMOp(f)(τs)
            (S,T,C), τ, sv = add_TypeOp((S,T,C), op)
            # println("Adding op constraint: got $s1 and $s2.")

            # compute result contexts
            (S,T,C,Σ), σa = add(S,T,C, map(x -> scale(x...), zip(sv, Σs))...)

            (S,T,C,Σ), τ, [σ; σa]
        end;
        phi(c,tr,fs) => let

            # check the condition and branches
            (S,T,C,Σ1), _, σ = check_sens((S,T,C,Γ), c)
            Γ = apply_subs(Γ, σ)

            (S,T,C,Σ2), τ2, σ2 = check_sens((S,T,C,Γ), tr)
            Γ = apply_subs(Γ, σ2)
            # in case the return type is a constant number, make it non-constant
            # because it would be weird if both branches are forced to return the same constant
            # TODO composite types are still unified in the usual way. proper subtyping?

            (S,T,C,Σ3), τ3, σ3 = check_sens((S,T,C,Γ), fs)

            # apply substitutions done in later checking to everything
            Σ1, Σ2, τ2 = distribute_substitute((apply_subs(Σ1, σ2), Σ2, τ2), σ3)

            # unify the return types of the branches
            (S,T,C,Σ1), (Σ2, Σ3), τ, σ_sub = getSupremumOf_withExtra((S,T,C,Σ1), (Σ2, Σ3), τ2, τ3)

            # compute the result context
            (S,T,C,Σ), σ_add = add(S,T,C,scale(∞, Σ1), Σ2, Σ3)

            # in case that changed τ, substitute
            τ = apply_subs(τ, σ_add)

            return (S,T,C,Σ), τ, [σ; σ2; σ3; σ_sub; σ_add]
        end;
        ret(e) => error("no return in sensitive mode");
        lam(xτs, e) => let
            Σ = Γ

            #println("LAM checking $xτs=>$e\n")
            # add type and sensitivity variables for all arguments
            function makeType((x, τ1))
                τ1, S, T, C = create_DMType(τ1, S, T, C)
                Σ = merge(Σ, TypeContext(x => τ1))
                (x, τ1)
            end
            xτs = map(makeType, xτs)

            # check the term
            (S,T,C,Σ), τ_e, σ = check_sens((S,T,C,Σ), e)
            Γ = apply_subs(Γ, σ)

            # calculate the resulting type by looking into the current context
            # NOTE: we have to read out the sensitivity and type of the argument from the context
            # given back to us, in case the type was unified further when checking.
            resτ = Arr([], [Σ[x[1]] for x in xτs], τ_e)

            # remove argument variables from the context.
            for (x, _) in xτs
                if haskey(Γ, x)
                    # NOTE: This means we have shadowed a pre-existing x with a new one in this lambda
                    Σ = merge(Σ, SCtx(x => (0, Γ[x])))
                else
                    Σ = remove(Σ, [x])
                end
            end

            (S,T,C,Σ), resτ, σ
        end;
        lam_star(xξs, e) => error("not implemented!")
        apply(f, args) => let

            # check the lambda
            (S,T,C,Σ), τ_lam, σ = check_sens((S,T,C,Γ), f)
            Γ = apply_subs(Γ, σ)

            # resolve the arguments
            τs = []
            for arg in args
                # create new variables for argument sensitivity
                S, s = addNewName(S, Symbol("sens_"))
                s = symbols(s)

                # check the argument
                (S,T,C,Σ_arg), τ_arg, σ_arg = check_sens((S,T,C,Γ), arg)
                #println("arg $arg checked:\nSigma_arg: ",Σ_arg,"\nargtype: ",τ_arg,"\nT: $T\nsubs: $σ_arg\n\n")
                # apply substitutions to everything encountered so far
                (Γ, Σ, τ_lam, s) = distribute_substitute((Γ, Σ, τ_lam, s), σ_arg)
                σ = [σ ; σ_arg]

                # compute the result context
                (S,T,C,Σ), σ_add = add(S,T,C,Σ, scale(s, Σ_arg))
                (Γ, τ_lam, s) = distribute_substitute((Γ, τ_lam, s), σ_arg)
                σ = [σ ; σ_add]

                #println("APPLY: substituted:\n",Σ,"\n",τ_lam,"\n$T\n$Γ\n")
                τs = [τs; (s, τ_arg)]
            end

            # and one variable for the return type
            T, τ_ret = addNewName(T, Symbol("arr_"))
            τ_ret = TVar(τ_ret)

            # unify the lambda's type with the arrow type appropriate for the given arguments
            # captures are empty, as application is only allowed for lambdas for wich all captures can
            # be resolved at application time.
            # (S,T,C,Σ), Arr_res, _, σ_arr = unify_DMType((S,T,C,Σ), τ_lam, Arr(τs, τ_ret))
            #TODO eval suptype right away to avoid stupid constraint foo
            (S,T,C,Σ), Arr_res, _, σ_arr = checkSubtypeOf((S,T,C,Σ), Arr([], τs, τ_ret), τ_lam)
            σ = [σ ; σ_arr]

            τ_ret = @match Arr_res begin
                Arr(_, _, τ_ret) => τ_ret;
                _ => error("INTERNAL ERROR: Unification of an arrow type destroyed the arrow.")
            end

            (S,T,C,Σ), τ_ret, σ
        end;
        abstr(t) => begin
            STCΣ , τ , σs = check_sens((S,T,C,Γ), t)
            STCΣ, σs, Δ = diff(STCΣ, σs, (S,T))
            STCΣ, ForAll(Δ, τ), σs
        end
        iter(f, s, l)        => error("typechecking of iter should be done inside loop.") #TODO this is kinda weird
        loop(it, cs, b)      => let

            # compute number of iteration steps
            f, s, l = @match it begin
                iter(f, s, l) => (f, s, l)
                _ => error("first argument of loop must be an iter term")
            end;

            niter = op(ceil, [op(/, [op(-, [l, op(-, [f, sng(1)])]), s])])

            # check the niter term
            (S,T,C,Σ_n), τ_n, σ = check_sens((S,T,C,Γ), niter)
            Γ = apply_subs(Γ, σ)

            # check the body
            (S,T,C,Σ_b), τ_b, σ_b = check_sens((S,T,C,Γ), b)
            (Γ, Σ_n, τ_n) = distribute_substitute((Γ, Σ_n, τ_n), σ_b)
            σ = [σ; σ_b]

            # grab capture input and return type of th ebody
            τ_bin, τ_bret = @match τ_b begin
                Arr(_, [_, (_, τ_bin)], τ_bret) => (τ_bin, τ_bret)
            end

            # ensure body input and output are the same type
            (S,T,C,Σ_b), (Σ_n, τ_n, τ_b), τ_bret, σ_ub = unify_DMType_withExtra((S,T,C,Σ_b), (Σ_n, τ_n, τ_b), τ_bret, τ_bin)
            σ = [σ; σ_ub]

            # check captures
            (S,T,C,Σ_c), τ_c, σ_c = check_sens((S,T,C,Γ), cs)
            (Γ, Σ_n, τ_n, Σ_b, τ_b) = distribute_substitute((Γ, Σ_n, τ_n, Σ_b, τ_b), σ_c)
            σ = [σ; σ_c]

            # ensure capture type and body in-/output are the same type
            (S,T,C,Σ_c), (Σ_n, τ_n, Σ_b, τ_b), τ_c, σ_uc = unify_DMType_withExtra((S,T,C,Σ_c), (Σ_n, τ_n, Σ_b, τ_b), τ_bret, τ_c)
            σ = [σ; σ_uc]

            # create sens vars and constraints so we can later decide if it's loop or sloop
            (S,T,C), τ_ret, sv = add_TypeOp((S,T,C), Ternary(DMOpLoop(), τ_n, τ_c, τ_b))

            # compute result context
            (S,T,C,Σ), σ_add = add(S,T,C,scale(sv[1], Σ_n), scale(sv[2], Σ_c), scale(sv[3], Σ_b))
            τ_ret = apply_subs(τ_ret, σ_add) # in case something in τ_ret was substituted by the addition
            σ = [σ; σ_add]

            (S,T,C,Σ), τ_ret, σ
        end;
        #=
        trttup(ts) =>
        let
            σ = Substitutions()
            ηs = Sensitivity[]
            τs = DMType[]
            Σs = []

            # check the elements
            for t in ts
                (S,T,C,Σ1), τ1, σ1 = check_sens((S,T,C,Γ), t)
                Γ = apply_subs(Γ, σ1)
                S, η1 = addNewName(S, Symbol("trttup_sens_"))
                η1 = symbols(η1)
                ηs = [ηs; η1]
                Σ1 = scale(η1, Σ1)
                Σs = [Σs; Σ1]
                τs = [τs; τ1]
                σ = [σ; σ1]
            end
            # in case a branch substituted things that appear in the results of the others:
            # substitute!
            Γ, Σs, τs = distribute_substitute((Γ, Σs, τs), σ)

            # compute result context
            (S,T,C,Σ), σa = add(S,T,C, Σs...)

            ητs = collect(zip(ηs, τs))
            (S,T,C,Σ), DMTrtProduct(ητs), [σ; σa]

        end;
        trtlet(xs, tu, b) => let
            # check the body
            (S,T,C,Σ_b), τ_b, σ_b = check_sens((S,T,C,Γ), lam(xs, b))
            Γ = apply_subs(Γ, σ_b)

            # check the tuple
            (S,T,C,Σ_t), τ_t, σ_t = check_sens((S,T,C,Γ), tu)
            (Σ_b, τ_b) = distribute_substitute((Σ_b, τ_b), σ_t)

            # grab the types the variables have in the body, as well es the return type
            ητs, τ_ret = @match τ_b begin
                Arr(ητs, τ_ret) => (ητs, τ_ret)
            end

            # make sure the type of tup is the correct tuple type for the body variables
            # This takes care of the sensitivity-var unification for tuple tranparency as well!
            (S,T,C,Σ_t), (Σ_b, τ_b), _, _, σ_u = unify_DMType_withExtra((S,T,C,Σ_t), (Σ_b, τ_b), τ_t, DMTrtProduct(ητs))

            # compute the maximum sensitivity among the arguments, also grab the return type
            # s, τ = @match τ_b begin
            #     Arr(τs, τ_ret) => (max(map(first, τs)...), τ_ret);
            # end

            # compute result sensitivity. No scaling is needed, since it was already done when creating the tuple.
            (S,T,C,Σ), σ_add = add(S,T,C, Σ_t, Σ_b)
            τ_ret = apply_subs(τ_ret, σ_add)

            (S,T,C,Σ), τ_ret, [σ_b; σ_t; σ_u; σ_add]
        end;
        =#
        tup(ts) => let
            σ = Substitutions()
            τs = DMType[]
            Σs = []

            # check the elements
            for t in ts
                (S,T,C,Σ1), τ1, σ1 = check_sens((S,T,C,Γ), t)
                Γ = apply_subs(Γ, σ1)
                Σs = [Σs; Σ1]
                τs = [τs; τ1]
                σ = [σ; σ1]
            end
            # in case a branch substituted things that appear in the results of the others:
            # substitute!
            Γ, Σs, τs = distribute_substitute((Γ, Σs, τs), σ)

            # compute result context
            (S,T,C,Σ), σa = add(S,T,C, Σs...)

            (S,T,C,Σ), DMTup(τs), [σ; σa]
        end;
        tlet(xs, tu, b) => let
            # check the body
            (S,T,C,Σ_b), τ_b, σ_b = check_sens((S,T,C,Γ), lam(xs, b))
            Γ = apply_subs(Γ, σ_b)

            # check the tuple
            (S,T,C,Σ_t), τ_t, σ_t = check_sens((S,T,C,Γ), tu)
            (Σ_b, τ_b) = distribute_substitute((Σ_b, τ_b), σ_t)

            # grab the types the variables have in the body
            τs = @match τ_b begin
                Arr(_, τs, τ_ret) => map(last, τs);
            end

            # make sure the type of tup is the correct tuple type for the body variables
            (S,T,C,Σ_t), (Σ_b, τ_b), _, σ_u = unify_DMType_withExtra((S,T,C,Σ_t), (Σ_b, τ_b), τ_t, DMTup(τs))

            # compute the maximum sensitivity among the arguments, also grab the return type
            # NOTE: this differs from the paper, we allow different sensitivities for the variables
            # that the tuple is assigned to so we use maximum of the sensitivities.
            s, τ = @match τ_b begin
                Arr(_, τs, τ_ret) => (length(τs) > 1 ? max(map(first, τs)...) : first(τs[1]), τ_ret);
            end

            # compute result sensitivity
            (S,T,C,Σ), σ_add = add(S,T,C, scale(s, Σ_t), Σ_b)
            τ = apply_subs(τ, σ_add)

            # remove variables from the context again.
            for (v, _) in xs
                if haskey(Γ, v)
                    # NOTE: This means we have shadowed a pre-existing x with a new one in this let
                    Σ = merge(Σ, SCtx(x => (0, Γ[v])))
                else
                    Σ = remove(Σ, [v])
                end
            end

            (S,T,C,Σ), τ, [σ_b; σ_t; σ_u; σ_add]
        end;
        slet(v, t, b) => let
            check_sens((S,T,C,Γ), apply(lam([v], b), [t]))
            #=
            printdebug(Log_TypecheckPhases(), "== Entering SLET ($v)")
            printdebug(Log_TypecheckPhases(), "SLET typechecking body: $b")
            # check the body
            (S,T,C,Σ_b), τ_b, σ_b = check_sens((S,T,C,Γ), lam([v], b))
            Γ = apply_subs(Γ, σ_b)
            printdebug(Log_TypecheckPhases(), "SLET got body type: $τ_b")
            printdebug(Log_SubstitutionDetails(), "SLET typechecking body got substs: $σ_b")

            # check the assignee
            (S,T,C,Σ_t), τ_t, σ_t = check_sens((S,T,C,Γ), t)
            (Γ, Σ_b, τ_b) = distribute_substitute((Γ, Σ_b, τ_b), σ_t)

            printdebug(Log_TypecheckPhases(), "SLET got assignee type: $τ_t")

            # resolve captures of the body type. this has to eliminate all captures
            (S,T,C,Σ_b), τ_b, σ_r = resolve_captures((S,T,C,merge(Γ, TypeContext([(first(v),τ_t)]))), τ_b, Σ_b)
            Γ, Σ_t, τ_t = distribute_substitute((Γ,Σ_t, τ_t), σ_r)
            printdebug(Log_SubstitutionDetails(), "SLET resolving captures of body got substs: $σ_r")

            # grab the types the variable has in the body
            τv = @match τ_b begin
                Arr([], τv, _) => last(τv[1]);
                Arr(_, _, _) => error("not all captures of $τ_b could be resolved in slet body")
            end

            printdebug(Log_TypecheckPhases(), "SLET unifying $τ_t   with    $τv   in     $τ_b")

            # make sure the type of v is the correct type for the body variable
            (S,T,C,Σ_t), (Γ, Σ_b, τ_b), _, _, σ_u = unify_DMType_withExtra((S,T,C,Σ_t), (Γ, Σ_b, τ_b), τ_t, τv)
            printdebug(Log_SubstitutionDetails(), "SLET unification got substs: $σ_u")

            # compute the sensitivity of the argument, also grab the return type
            s, τ = @match τ_b begin
                Arr(_, τv, τ_ret) => (first(τv[1]), τ_ret);
            end

            printdebug(Log_TypecheckPhases(), "SLET before distributing substitute.")
            # compute result context
            (S,T,C,Σ), σ_add = add(S,T,C, scale(s, Σ_t), Σ_b)
            Γ, τ = distribute_substitute((Γ, τ), σ_add)

            # remove variable from the context again.
            if haskey(Γ, first(v))
                #n NOTE: This means we have shadowed a pre-existing v with a new one in this let
                Σ = merge(Σ, SCtx(first(v) => (0, Γ[v[1]])))
            else
                Σ = remove(Σ, [v[1]])
            end

            σ_res = [σ_b; σ_t; σ_r; σ_u; σ_add]
            printdebug(Log_SubstitutionDetails(), "Returning substs: $σ_res")
            printdebug(Log_TypecheckPhases(), "== Exiting SLET ($v)")

            (S,T,C,Σ), τ, σ_res
=#
        end;
        vect(vs) => let
            l = length(vs)

            # check the elements
            (S,T,C,Σ1), τ1, σ1 = check_sens((S,T,C,Γ), vs[1])
            Σ1 = scale(l, Σ1)

            for t in vs[2:end]
                # check element
                (S,T,C,Σ), τ, σ_c = check_sens((S,T,C,Γ), t)
                (Γ, Σ1, τ1) = distribute_substitute((Γ, Σ1, τ1), σ_c)

                # make all element types equal
                (S,T,C,Σ), (Γ, Σ1), τ1, σ_u = unify_DMType_withExtra((S,T,C,Σ), (Γ, Σ1), τ, τ1)

                # compute result context
                (S,T,C,Σ1), σ_a = add(S,T,C, Σ1, scale(l, Σ))
                (Γ, τ1) = distribute_substitute((Γ, τ1), σ_a)

                σ1 = [σ1; σ_c; σ_u; σ_a]
            end

            (S,T,C,Σ1), DMVec(length(vs), τ1), σ1
        end;
        flet(fname, fterm, body) => let
            # functions from outer scope are not allowed to capture inside fname's scope:
            # g(x) = x+y
            # fname(y) = g(2)
            # fname(1)        --> error: y not defined.
            # we take them out of the scope for checking the function term, they get a TVar type in Σ2.
            # we keep them when checking the body so their potential captures can be resolved there.
            # then when we add Σ2 and Σ3 the Tvar and resolved Arr get unified TODO delete caps
            #Γnocaps = filter((τ) -> !(τ[2] isa Union{Arr, DMChoice}), Γ)

            # check sensitivity and get type of newly declared function
            (S2, T2, C2, Σ2) , τ_function, σ_function = check_sens((S,T,C,Γ), fterm)
            Γ2 = apply_subs(Γ, σ_function)

            # add function choice to context
            Γ2, choice_index = insert_choice(Γ2, fname, τ_function)

            # typecheck body in this context
            (S3, T3, C3, Σ3) , τ_body , σ_body = check_sens((S2,T2,C2,Γ2), body)
            Σ2 = apply_subs(Σ2, σ_body)

            # remove the choice again from the contexts
            Σ3 = delete_choice(Σ3, fname, choice_index)

            # the final sensitivity is the sum of the functions' and the bodys'
            (S,T,C,Σ), σ_add = add(S3,T3,C3, Σ2, Σ3)

            # combine all substitutions
            σ = [σ_function ; σ_body ; σ_add]

            # remove variable from the context again.
            if haskey(Γ, fname)
                # NOTE: This means we have shadowed a pre-existing x with a new one in this let
                Σ = merge(Σ, SCtx(fname => (0, Γ[fname])))
            else
                Σ = remove(Σ, [fname])
            end

            # return
            (S,T,C,Σ) , τ_body , σ

        end
        vcreate(s, l) => let
            # check the length term
            (S,T,C,Σ_s), τ_s, σ_s = check_sens((S,T,C,Γ), s)
            Γ = apply_subs(Γ, σ_s)

            # make it equal to some singleton number
            (S, svar) = addNewName(S, Symbol("veclen_"))
            svar = symbols(svar)
            (S,T,C,Σ_s), (Γ, svar), τ_s, σ_u = unify_DMType_withExtra((S,T,C,Σ_s), (Γ, svar), τ_s, Constant(DMInt(), svar))

            # check the generating function
            (S,T,C,Σ_l), τ_l, σ_l = check_sens((S,T,C,Γ), l)

            # apply substitution to everything encountered so far
            (Σ_s, τ_s, svar) = distribute_substitute((Σ_s, τ_s, svar), σ_l)

            # compute result context
            (S,T,C,Σ), σ_add = add(S,T,C,scale(0, Σ_s), scale(svar, Σ_l))

            # substitute in vector element type and length term
            (τ_l, svar) = distribute_substitute((τ_l, svar), σ_add)

            # extract element type
            τ = @match τ_l begin
                Arr(_, _, τ) => τ
                _ => error("vector argument $l is not a function")
            end

            (S,T,C,Σ), DMVec(svar, τ), [σ_s; σ_l; σ_add]
        end;
        index(v, i) => let
            # check the vector
            (S,T,C,Σ_v), τ_v, σ_v = check_sens((S,T,C,Γ), v)
            Γ = apply_subs(Γ, σ_v)

            # make it equal to some vector
            S, len = addNewName(S, Symbol("veclen_"))
            T, τ = addNewName(T, Symbol("vecelem_"))
            len = symbols(len)
            τ = TVar(τ)
            (S,T,C,Σ_v), Γ, τ_v, σ_vv = unify_DMType_withExtra((S,T,C,Σ_v), Γ, τ_v, DMVec(len, τ))

            # check the index term
            (S,T,C,Σ_i), τ_i, σ_i = check_sens((S,T,C,Γ), i)

            # enforce it's a number
            C = [C; isNumeric(τ_i)]

            # apply substitution to everything encountered so far
            (Σ_v, τ) = distribute_substitute((Σ_v, τ), σ_i)

            # TODO make the index term be of the appropriate Index type
            #(S,T,C,Σ_i), (Σ_v, τ), _, τ_i, σ_u = unify_DMType_withExtra((S,T,C,Σ_i), (Σ_v, τ), τ_i, Idx(s))

            # compute result context
            (S,T,C,Σ), σ_add = add(S,T,C, Σ_v, scale(0, Σ_i))

            # substitute in vector type
            τ = apply_subs(τ, σ_add)

            #(S,T,C,Σ), τ, [σ_v; σ_i; σ_u; σ_add]
            (S,T,C,Σ), τ, [σ_v; σ_vv; σ_i; σ_add]
        end;
        len(v)                => error("not implemented!")
        dphi(_)               => error("not implemented!")
    end
end

