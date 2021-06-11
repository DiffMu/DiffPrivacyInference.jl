"""
check_term(t::DMTerm, scope = Dict{Symbol, Vector{DMTerm}}()) :: TC

Typecheck the input `DMTerm` and return the resulting computation as a `TC` monad. The
result will have a lot of unresolved constraints.
"""
check_term(t::DMTerm) = mcheck_sens(t, Dict{Symbol, Vector{DMTerm}}(), false)

# scope maps variable names to the stack of terms that were assigned to that variable. it
# gets updated during the recursive traversal of t, pushing a term to the stack whenever
# a variable gets assigned. this is analogous to the julia interpreter's traversal of the
# corresponding julia expression and serves to keep track of the current state of a variable
# at the point in execution where it is actually used as a function argument.
# expect_priv flags whether we expect the term to be a privacy/"red" term.
function mcheck_sens(t::DMTerm, scope :: Dict{Symbol, Vector{DMTerm}}, expect_priv::Bool) :: TC#{DMType}

    println("chekcing $t, expecting p $expect_priv\n")
    result = @match (t, expect_priv) begin

        ############################################## these terms can only be sensitivity terms.

        (sng(n), false) => let
            # maybe n actually is a constant. get n's type
            function make_type(T)
                T, τ = @match n begin
                    ::Int => (T, DMInt())
                    ::Real => (T, DMReal())
                    _ => add_new_type(T, Symbol(n))
                end;
                T, Constant(τ, n)
            end
            add_type(make_type)
        end;

        (arg(x, dτ, i), false) => let # a special term for function argument variables. those get sensitivity 1, all other variables are var terms
            @mdo TC begin
                τ <- mcreate_DMType(dτ)
                τ <- set_var(x, 1, τ, i) # set sensitivity = 1, type = τ for x and interestingness to i.
                return τ
            end
        end;

        (op(opf, args), false) => let
            # handle a single argument. τ and s are the typevar and sensitivity scalar
            # belonging to this arg, as assigned to by the typeOp.
            function check_op_arg((arg, τ, s)::Tuple{DMTerm, DMType, Sensitivity}) :: TC
                @mdo TC begin
                    τ_arg <- mcheck_sens(arg, scope, false) # check operand
                    _ <- mscale(s) # scale context
                    n <- unify(τ_arg, τ) # unify with type from the typeOp
                    return n
                end
            end

            @mdo TC begin
                (τ_res, τs, vs) <- add_op(opf) # add typeop
                _ <- msum(map(check_op_arg, zip(args,τs,vs))) # check operands seperately and sum result contexts
                return τ_res
            end
        end;

        (mcreate(n, m, xs, body), false) => let

            function setdim(v::DMTerm, s) :: TC
                @mdo TC begin
                    t <- mcheck_sens(v, scope, false)
                    _ <- unify(t, Constant(DMInt(),s))
                    _ <- mscale(0)
                    return s
                end
            end

            function setarg(x::Symbol) :: TC
                @mdo TC begin
                    t <- lookup_var_type(x)
                    _ <- (isnothing(t) ? mreturn(()) : subtype_of(t, DMInt()))
                    return ()
                end
            end

            # add the index variables to the scope. TODO this is weird, use lam isntead?
            scope[xs[1]] = [arg(xs[1],Int)]
            scope[xs[2]] = [arg(xs[2],Int)]

            @mdo TC begin
                (nv, mv) <- mapM(x->add_svar(), (n,m))
                tbody <- mcheck_sens(body, scope, false)
                _ <- mscale(nv*mv)
                _ <- msum(mreturn(tbody), setdim(n, nv), setdim(m, mv))
                _ <- mapM(setarg, xs)
                norm <- add_nvar()
                return DMMatrix(norm, U, (nv, mv), tbody)
            end
        end;


        (lam(xτs, body), false) => let

            scope = deepcopy(scope)

            for (x,τ) in xτs
                # put a special term to mark x as a function argument. those get special tratment
                # because we're interested in their sensitivity
                scope[x] = [arg(x,τ)]
            end

            @mdo TC begin
                τr <- mcheck_sens(body, scope, false) # check body to obtain lambda return type
                xrτs <- get_arglist(xτs) # argument variable types and sensitivities inferred from body
                return Arr(xrτs, τr)
            end
        end;

        (lam_star(xτs, body), false) => let

            scope = deepcopy(scope)

            for ((x,τ),i) in xτs
                # put a special term to mark x as a function argument. those get special tratment
                # because we're interested in their sensitivity
                scope[x] = [arg(x,τ,i)]
            end

            # check body in privacy mode.
            @mdo TC begin
                τr <- mcheck_sens(body, scope, true) # check body to obtain lambda return type.
                xrτs <- get_arglist(map(first,xτs)) # argument variable types and sensitivities inferred from body
                _ <- mtruncate(∞)
                return ArrStar(xrτs, τr)
            end
        end;

        (chce(Cs), false) => let # a special term for storing choices, can only appear during typechecking (not from parsing)
            if length(Cs) == 1
                mcheck_sens(first(values(Cs)), scope, false)
            else

                # check a single choice, return pair (signature => (flag variable, choice type))
                function check_choice((sign,choice)::Tuple{Vector{<:DataType}, DMTerm}) :: TC#{Pair{Sensitivity,DMType}}
                    @mdo TC begin
                        τ_choice <- mcheck_sens(choice, scope, false)
                        flag <- add_svar("chce_flag_") # add a flag variable to set to 0 or 1 depending on if this choice was picked
                        _ <- mscale(flag)
                        return sign => (flag, τ_choice)
                    end
                end

                # check all choices, collect result in a isChoice constraint.
                @mdo TC begin
                    sτs <- msum(map(check_choice, zip(keys(Cs), values(Cs)))) # check every choice seperately and sum with flags
                    τ <- add_type(T -> add_new_type(T, :chce)) # create a typevar for the choice type
                    _ <- add_Cs(Constraints([isChoice(τ, Dict(sτs))])) # add the constraint
                    return τ
                end
            end
        end;

        (var(x,dτ), false) => let
            if haskey(scope, x)
                scope = deepcopy(scope)

                # get the term that corresponds to this variable from the scope dict
                vt = @match scope[x] begin
                    [t] => let
                        delete!(scope, x)
                        t
                    end;
                    ts => pop!(scope[x]) # x was overwritten at some point; we take the most recent term.
                end

                @mdo TC begin
                    τ <- mcheck_sens(vt, scope, false) # check the term
                    dτd <- mcreate_DMType(dτ) # get user annotation DMType
                    _ <- (dτ == Any ? mreturn(nothing) : subtype_of(τ, dτd)) # inferred type must be a subtype of the user annotation
                    return τ
                end

            else
                throw(NotInScope("Variable $x not in scope!"))
            end
        end;

        (tlet(xs, tu, body), false) => let
            if !allunique(map(first, xs))
                error("tuple assignment to the same variable mutliple times is forbidden in $t")
            end

            newscope = deepcopy(scope)

            # generate unique variable names for the tuple entry to put into the arg term
            # we use arg because we need to infer their sensitivity in the body to make the right scale
            xnames = []
            for (x, xτ) in xs
                @assert xτ == Any "Type annotations on variables not yet supported."
                xname = gensym("tup_arg_")
                push!(xnames, xname)
                newscope[x] = [arg(xname,Any)]
            end

            # check t, scale with s
            function check_tup(t::DMTerm, s::Sensitivity) :: TC
                @mdo TC begin
                    τ <- mcheck_sens(t, scope, false)
                    _ <- mscale(s)
                    return τ
                end
            end

            @mdo TC begin
                # check body with the scope that contains the tuple entries
                τb <- mcheck_sens(body, newscope, false)

                # lookup the inferred types and sensitivities of tuple entries and delete them from Σ
                sτs <- mapM(remove_var, xnames)
                τs = map(x->x[2], sτs)
                s = isempty(τs) ? 0 : maximum(map(first, sτs)) # we allow more than two entries that can have different sensitivity, hence max
                _ = println("checked body $body\ngot $sτs on $xnames\n so s is $s\n")

                # sum tuple context scaled with s and body context
                (_, τtu) <- msum(mreturn(τb), check_tup(tu, s))

                # set tuple type
                _ <- unify(τtu, DMTup(τs))

                return τb
            end
        end

        (tup(ts), false) => let
            @mdo TC begin
                # just check each entry and sum
                τs <- msum(map(a -> mcheck_sens(a, scope, false), ts))
                return DMTup(τs)
            end
        end

        (loop(it, cs, xs, b), false) => let

            # compute number of iteration steps
            niter = @match it begin
                iter(f, s, l) => op(:ceil, [op(:/, [op(:-, [l, op(:-, [f, sng(1)])]), s])])
                _ => error("first argument of loop must be an iter term")
            end;

            miter = @mdo TC begin
                τ <- mcheck_sens(niter, scope, false)
                s <- add_svar("n_iter_")
                _ <- mscale(s)
                return (τ, s)
            end

            mcaps = @mdo TC begin
                τ <- mcheck_sens(cs, scope, false)
                s <- add_svar("caps_")
                _ <- mscale(s)
                _ = println("checked caps:\n")
                _ <- mprint()
                return (τ, s)
            end

            newscope = deepcopy(scope)
            # we use arg because we need to infer their sensitivity in the body to make the right scale
            for x in xs
                newscope[x] = [arg(x,Any)]
            end

            mbody = @mdo TC begin
                τ <- mcheck_sens(b, newscope, false)
                s <- add_svar("lbody_")
                vs <- mapM(remove_var, xs)
                _ <- mscale(s)
                return (τ, s, vs)
            end

            @mdo TC begin
                # check number of iterations, captures, and body term.
                ((τ_iter, s_iter), (τ_caps, s_caps), (τ_b, s_b, vs)) <- msum(miter, mcaps, mbody)
                ((_,τ_biter), (s, τ_bcaps)) = vs # sensitivities and types of body iput iteration index and captures

                _ <- add_Cs([isSubtypeOf(τ_iter, τ_biter), # number of iterations must match typer equested by body
                             isSubtypeOf(τ_caps, τ_bcaps), # capture type must match type requested by body
                             isSubtypeOf(τ_b, τ_bcaps), # body output type must match body capture input type
                             isLoopResult((s_iter, s_caps, s_b), s, τ_iter)]) # compute the right scalars once we know if τ_iter is const or not.

                return τ_b
            end
        end;


        (apply(f, args), false) => let
            # check a single argument, append the resulting (Sensitivity, DMType) tuple to sτs
            function check_sarg(arg::DMTerm) :: TC
                @mdo TC begin
                    τ_res <- mcheck_sens(arg, scope, false) # check the argument term
                    s <- add_svar("farg_s_") # add a new svar for this argument's sensitivity
                    _ <- mscale(s) # scale the context with it
                    return (s, τ_res)
                end
            end

            @mdo TC begin
                (sτs_args, τ_lam) <- msum(msum(map(check_sarg, args)), mcheck_sens(f, scope, false)) # check function and args seperately
                τ_ret <- add_type(T -> add_new_type(T, :ret)) # create a tvar for the return type
                a <- subtype_of(τ_lam, Arr(sτs_args,τ_ret)) # add the right subtype constraint
                return τ_ret
            end
        end;

        (dmclip(norm, body), false) => let
            @mdo TC begin
                bt <- mcheck_sens(body, scope, false)
                l <- add_nvar()
                c_in <- add_cvar()
                (rows, cols) <- mapM(x->add_svar(), collect((nothing for _ in 1:2)))
                _ <- unify(bt, DMMatrix(l, c_in, (rows, cols), DMData()))
                return DMMatrix(l, norm, (rows, cols), DMData())
            end
        end

        (slet((v, dτ), t, b), false) => let

            # TODO this requires saving the annotation in the dict.
            @assert dτ == Any "Type annotations on variables not yet supported."

            # we're very lazy, only adding the new term for v to its scope entry
            scope = deepcopy(scope)
            present = haskey(scope,v)
            present ? push!(scope[v], t) : scope[v] = [t]

            return mcheck_sens(b, scope, expect_priv) # check body, this will put the seinsitivity it has in the arguments in the monad context.
        end;

        ############################################## these can be privacy _or_ sensitivity terms


        (slet((v, dτ), t, b), true) => let # this is the bind rule, actually.

            # TODO this requires saving the annotation in the dict.
            @assert dτ == Any "Type annotations on variables not yet supported."

            # add an arg term for v, we don't really care for it's sensitivity bu it can be used as a sensitivity term. 
            newscope = deepcopy(scope)
            newscope[v] = [arg(v,Any)]

            mbody = @mdo TC begin
                τ_b <- mcheck_sens(b, newscope, true)
                _ <- remove_var(v)
                return τ_b
            end

            @mdo TC begin
                (τ_b, _) <- msum(mbody, mcheck_sens(t, scope, true))
                return τ_b
            end
        end;
#=
        (flet(f, s, l, b), _) => let

            scope = deepcopy(scope)

            present = haskey(scope,f)

            if present
                choice = @match scope[f] begin
                    [chce(Cs)] => Cs;
                    _ => "error invalid term for choice $f: $(scope[f])"
                end
                choice[s] = l # add choice entry with the term l for this signature s
            else
                scope[f] = [chce(Dict(s => l))] # make a new scope entry for f with only one choice
            end

            @mdo TC begin
                result <- mcheck_sens(b, scope, expect_priv) # check the body
                _ <- (present ? mreturn(result) : remove_var(f)) # remove f from the return context #TODO really?
                return result
            end
        end;
=#
        (phi(c,tr,fs), _) => let
            @mdo TC begin
                τ_c <- mcheck_sens(c, scope, false) # check condition. must be a sensitivity term
                (_, τ_tr, τ_fs) <- msum(mscale(∞), mcheck_sens(tr,scope,expect_priv), mcheck_sens(fs,scope,expect_priv)) # check both branches and sum
                τ_ret <- msupremum(τ_tr, τ_fs) # branches return type must be the same, or at least the non-constant version
                return τ_ret
            end
        end;

        #################################################### these can only be privacy terms

        (ret(rt), true) => let
            @mdo TC begin
                τ <- mcheck_sens(rt, scope, false)
                _ <- mtruncate((∞,∞))
                return τ
            end
        end;

        (gauss(ps, f), false) => let

            # this is different from the paper. we assume gauss takes a sensitivity function with required sensitivity
            # and returns a privacy function with requested privacy. the privacy is in all arguments of the input function,
            # which gives a way to choose wht x1...xn from the paper.

            (r, ϵ, δ) = ps

            # check tt and set it to be a subtype of some Const Real.
            function set_type_sng(tt::DMTerm) :: TC
                @mdo TC begin
                    τ <- mcheck_sens(tt, scope, false)
                    v <- add_svar("gauss_param_")
                    τ <- subtype_of(τ, Constant(DMReal(), v))
                    return v
                end
            end

            @mdo TC begin
                τ_f <- mcheck_sens(f, scope, false)
                xs, ts, τ_fret = @match τ_f begin
                    Arr(xts, τ_fret) => (map(first, xts), map(last, xts), τ_fret)
                end
                τ_gauss <- add_type(T -> add_new_type(T, :gauss_res_))

                _ <- add_Cs(Constr[isGaussResult(τ_gauss, τ_fret)]) # we decide later if it's gauss or matrix gauss
                (rv, ϵv, δv) <- mapM(set_type_sng, (r,ϵ,δ)) # all parameters have to be const real
                _ <- add_Cs(Constr[isLessOrEqual(s, rv) for s in xs]) # all sensitivities of f have to be bounded by rv
                return ArrStar([((ϵv,δv), t) for t in ts], τ_gauss)
            end
        end;

        (loop(it, cs, vs, b), true) => let

            # compute number of iteration steps
            niter = @match it begin
                iter(f, s, l) => op(:ceil, [op(:/, [op(:-, [l, op(:-, [f, sng(1)])]), s])])
                _ => error("first argument of loop must be an iter term")
            end;

            # check #iterations term
            miter = @mdo TC begin
                τ <- mcheck_sens(niter, scope, false)
                _ <- mtruncate((0,0))
                return τ
            end

            # check capture variable term
            mcap = @mdo TC begin
                τ <- mcheck_sens(cs, scope, false)
                _ <- mtruncate((∞,∞))
                return τ
            end

            # add the iteration and capture variables to the scope
            # their inferred privacy does not really matter, they just have to be there. 
            newscope = deepcopy(scope)
            for x in vs
                newscope[x] = [arg(x,Any)]
            end

            # given a list of interesting variables and their annotations, as well as the number of iterations,
            # compute the composite privacy and set it in the context.
            function set_interesting((xs,ps,τs)::Tuple{Vector{Symbol}, Vector, Vector{DMType}}, n::Sensitivity) :: TC
                @mdo TC begin
                    # compute maximal privacy value in the xs of interest
                    ϵ = maximum([first(p) for p in ps])
                    δ = maximum([last(p) for p in ps])

                    δn <- add_svar("comp_del_") # we can choose this!

                    # compute the new privacy for the xs according to the advanced composition theorem
                    newp = (2*ϵ*sqrt(2*n*log(1/δn)), δn+n*δ)

                    # set the xs' privacy accordingly
                    _ <- mapM(((x,τ),) -> set_var(x,newp,τ), collect(zip(xs,τs)))
                    return ()
                end
            end

            mbody = @mdo TC begin
                # check the body, lookup the privacies of the xs and truncate to ∞
                τ_b <- mcheck_sens(b, newscope, true)
                _ <- mapM(remove_var, vs) #TODO do something?
                (xs, ps, τs) <- get_interesting() # get all variables & their annotations that have an "interesting" tag
                _ <- mtruncate((∞,∞))
                n <- add_svar("n_iter_") # a variable for the number of iterations
                _ <- (isempty(xs) ? mreturn(nothing) : set_interesting((xs, ps, τs), n))
                return (τ_b, n) # return body return type an n as we we'll need it later
            end

            @mdo TC begin

                # check number of iterations, captures and body term, then sum.
                (τ_iter,τ_caps,(τ_b,n)) <- msum(miter, mcap, mbody)

                _ <- unify(τ_iter, Constant(DMInt(), n)) # number of iterations must be constant n

                _ <- add_Cs(Constr[isSubtypeOf(τ_b, τ_caps)]) # set correct body type

                return τ_caps
            end
        end;


        (apply(f, args), true) => let

            # execute all monads in args seperately with the same input Σ, only passing on S,T,C
            # then sum the resulting contexts and return execution results as a vector
            # function takes τ and Σ
            function mconstr(S,T,C,Σ) :: MType{Tuple{DMType, Vector}}
                (S,T,C,Σ1), τ_lam = mcheck_sens(f, scope, false).func(S,T,C,deepcopy(Σ))
                τs = []
                Σ1 = truncate(Σ1, (∞,∞))
                for arg in args
                    # TODO func should not be modifying Σ, but deepcopy just in case...
                    (S,T,C,Σ2), τ = check_parg(arg).func(S,T,C,deepcopy(Σ))
                    τs = push!(τs, τ)
                    (S,T,C,Σ1) = add(S,T,C,Σ1,Σ2)
                end
                return (S,T,C,Σ1), (τ_lam, τs)
            end

            # check a single argument, append the resulting (Sensitivity, DMType) tuple to sτs
            function check_parg(arg::DMTerm) :: TC
                @mdo TC begin
                    τ_res <- mcheck_sens(arg, scope, false) # check the argument term
                    ϵ <- add_svar("papply_eps_") # add a new svars for this argument's privacy
                    δ <- add_svar("papply_del_")
                    _ <- mtruncate((ϵ,δ)) # truncate the context with it
                    return ((ϵ, δ), τ_res)
                end
            end

            @mdo TC begin
                (τ_lam, aτs) <- TC(mconstr) # check the function
                τ_ret <- add_type(T -> add_new_type(T, :ret)) # create a tvar for the return type
                a <- subtype_of(τ_lam, ArrStar(aτs, τ_ret)) # add the right subtype constraint
                return τ_ret
            end
        end;

        (_, true) => mcheck_sens(ret(t), scope, true) # if a priv term was expected but a sens term given, just ret it.

        _ => error("could not check $t, expected a privacy term $expect_priv")

    end

    result

end
