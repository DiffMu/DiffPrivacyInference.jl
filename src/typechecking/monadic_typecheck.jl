"""
   check_term(t::DMTerm, scope = Dict{Symbol, Vector{DMTerm}}()) :: TC

Typecheck the input `DMTerm` and return the resulting computation as a `TC` monad. The
result will have a lot of unresolved constraints.
"""
check_term(t::DMTerm) = mcheck_sens(t, Dict{Symbol, Vector{DMTerm}}())

# scope maps variable names to the stack of terms that were assigned to that variable. it
# gets updated during the recursive traversal of t, pushing a term to the stack whenever
# a variable gets assigned. this is analogous to the julia interpreter's traversal of the
# corresponding julia expression and serves to keep track of the current state of a variable
# at the point in execution where it is actually used as a function argument.
function mcheck_sens(t::DMTerm, scope :: Dict{Symbol, Vector{DMTerm}}) :: TC#{DMType}

    result = @match t begin
        sng(n) => let
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

        lam(xτs, body) => let
            scope = deepcopy(scope)

            for (x,τ) in xτs
                # put a special term to memorize the type signature
                scope[x] = [arg(τ)]
            end

            @mdo TC begin
                τr <- mcheck_sens(body, scope) # check body to obtain lambda return type
                xrτs <- get_arglist(xτs) # argument variable types and sensitivities inferred from body
                return Arr(xrτs, τr)
            end

        end

        flet(f, s, l, b) => let

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
                result <- mcheck_sens(b, scope) # check the body
                _ <- (present ? mreturn(result) : remove_var(f)) # remove f from the return context #TODO really?
                return result
            end
        end;

        chce(Cs) => let # a special term for storing choices, can only appear during typechecking (not from parsing)
            if length(Cs) == 1
                mcheck_sens(first(values(Cs)), scope)
            else

                # check a single choice, return pair (signature => (flag variable, choice type))
                function check_choice((sign,choice)::Tuple{Vector{<:DataType}, DMTerm}) :: TC#{Pair{Sensitivity,DMType}}
                    @mdo TC begin
                        τ_choice <- mcheck_sens(choice, scope)
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

        slet((v, dτ), t, b) => let

            # we're very lazy, only adding the new term for v to its scope entry
            scope = deepcopy(scope)
            present = haskey(scope,v)
            present ? push!(scope[v], t) : scope[v] = [t]

            result = @mdo TC begin
                τ <- mcheck_sens(b, scope) # check body
                τv <- lookup_var_type(v) # get inferred type of v (τv = nothing if it was not used in the body)
                dτd <- mcreate_DMType(dτ)
                _ <- ((isnothing(τv) || dτ == Any) ? mreturn(nothing) : subtype_of(τv, aτ)) # inferred type of v must be subtype of user annotation.
                _ <- (present ? mreturn(nothing) : remove_var(v)) #TODO really??
                return τ
            end

            # last step in the mdo:
            # remove v from the return context
            # if it was present we need to keep it in the scope:
            # v = y
            # v = v+v
            # v
            # should be 2-sensitive in v.
        end;

        var(x,dτ) => let
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
                    τ <- mcheck_sens(vt, scope) # check the term
                    τ <- set_var(x, 1, τ) # set sensitivity = 1 and type = τ for x
                    dτd <- mcreate_DMType(dτ) # get user annotation DMType
                    _ <- (dτ == Any ? mreturn(nothing) : subtype_of(τ, dτd)) # inferred type must be a subtype of the user annotation
                    return τ
                end

            else
                error("Variable $x not in scope!")
            end
        end;

        arg(dτ) => let # a special term recording user-given function argument types (τ :: DataType)
            mcreate_DMType(dτ)
        end;

        op(opf, args) => let
            # handle a single argument. τ and s are the typevar and sensitivity scalar
            # belonging to this arg, as assigned to by the typeOp.
            function check_op_arg((arg, τ, s)::Tuple{DMTerm, DMType, Sensitivity}) :: TC
                @mdo TC begin
                    τ_arg <- mcheck_sens(arg, scope) # check operand
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

        apply(f, args) => let

            # check a single argument, append the resulting (Sensitivity, DMType) tuple to sτs
            function check_arg(arg::DMTerm) :: TC
                @mdo TC begin
                    τ_res <- mcheck_sens(arg, scope) # check the argument term
                    s <- add_svar() # add a new svar for this argument's sensitivity
                    _ <- mscale(s) # scale the context with it
                    return (s, τ_res)
                end
            end

            @mdo TC begin
                (sτs_args, τ_lam) <- msum(msum(map(check_arg, args)), mcheck_sens(f, scope)) # check function and args seperately
                τ_ret <- add_type(T -> add_new_type(T, :ret)) # create a tvar for the return type
                a <- subtype_of(τ_lam, Arr(sτs_args,τ_ret)) # add the right subtype constraint
                return τ_ret
            end
        end;

        _ => error("something unsupported: $t")

    end

    result

end
