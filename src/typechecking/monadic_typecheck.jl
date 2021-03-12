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

        (arg(x, dτ), false) => let # a special term for function argument variables. those get sensitivity 1, all other variables are var terms
            @mdo TC begin
                τ <- mcreate_DMType(dτ)
                τ <- set_var(x, 1, τ) # set sensitivity = 1 and type = τ for x
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
                (τ_res, τs, vs) <- add_op(opf, length(args)) # add typeop
                _ <- msum(map(check_op_arg, zip(args,τs,vs))) # check operands seperately and sum result contexts
                return τ_res
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

            for (x,τ) in xτs
                # put a special term to mark x as a function argument. those get special tratment
                # because we're interested in their sensitivity
                scope[x] = [arg(x,τ)]
            end

            # check body in privacy mode.
            @mdo TC begin
                τr <- mcheck_sens(body, scope, true) # check body to obtain lambda return type.
                xrτs <- get_arglist(xτs) # argument variable types and sensitivities inferred from body
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
                        flag <- add_svar() # add a flag variable to set to 0 or 1 depending on if this choice was picked
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

        (apply(f, args), false) => let
            # check a single argument, append the resulting (Sensitivity, DMType) tuple to sτs
            function check_sarg(arg::DMTerm) :: TC
                @mdo TC begin
                    τ_res <- mcheck_sens(arg, scope, false) # check the argument term
                    _  = println("checking arg $arg , got $τ_res.")
                    s <- add_svar() # add a new svar for this argument's sensitivity
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

        ############################################## these can be privacy _or_ sensitivity terms

        (slet((v, dτ), t, b), _) => let

            # TODO this requires saving the annotation in the dict.
            @assert dτ == Any "Type annotations on variables not yet supported."

            # we're very lazy, only adding the new term for v to its scope entry
            scope = deepcopy(scope)
            present = haskey(scope,v)
            present ? push!(scope[v], t) : scope[v] = [t]

            return mcheck_sens(b, scope, expect_priv) # check body, this will put the seinsitivity it has in the arguments in the monad context.
        end;

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
                    ϵ <- add_svar() # add a new svars for this argument's privacy
                    δ <- add_svar()
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
