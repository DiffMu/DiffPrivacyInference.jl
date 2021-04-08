
"""
file_to_dmterm(file::AbstractString)

Parse the file named `file` into a DMTerm. Includes are resolved and parsed as well.
All functions in the file will become nested `flet` terms, normal assignments are parsed
into `slet` terms. If the last statement of the file is a function definition or assignment,
the term will \"return\" that last variable."""
function file_to_dmterm(file::AbstractString) :: DMTerm
    ast = Meta.parseall(read(file, String), filename = file)
    println("read file $file")
    # error upon modification of nonlocal variables
    sanitize(ast.args, ast.args[1])
    println("sanitizing complete.")
    exprs_to_dmterm(ast.args, ast.args[1])
end


"Parse a string into a DMTerm."
function string_to_dmterm(code::String, ln=LineNumberNode(1, "none")) :: DMTerm
    println("starting parsing.")
    ast = Meta.parse("begin $code end")
    # error upon modification of nonlocal variables
    sanitize([ast], ln)
    println("sanitizing complete.")
    exprs_to_dmterm([ast], ln)
end

# we forbid number types finer than Integer and Real as function signatures, so we can
# decide on dispatch without having to carry the exact julia type.
function type_allowed(t::DataType)
    if t in [Integer, Real, Number, Any]
        return true
    elseif t <: Array
        return type_allowed(t.parameters[1])
    elseif t <: Tuple
        return all(map(type_allowed, t.parameters))
    else
        return false
    end
end


"""
exprs_to_dmterm(exs, ln::LineNumberNode, scope = ([],[],[], false))

Parse a block (a `Vector`) of expressions into a DMTerm. The vector can contain `Expr`s,
`Symbol`s, `LineNumberNode`s and `Number`s. `ln` is the current line and file.
`scope` is:
- `F`: Names of the functions in whose bodys the `exs` live.
- `A`: Names of argument variables of the innermost function -- these can be modified/assigned to.
- `C`: Names of variables captured from outside the innermost function -- these cannot be assigned to.
- `L`: `bool` variable indicating whether the parsed expressions are inside a loop body, as different rules apply there.
"""
# TODO maybe we don't need C anymore because we do sanitationz
function exprs_to_dmterm(exs, ln, scope = ([],[],[], false)) :: DMTerm

    #TODO this is just dispatch really, but the compiler does not terminate if i write it
    # with thwo mutually recursive functions. maybe another instance of https://github.com/JuliaLang/julia/issues/31572 ?
    @match exs begin
        ::Number => sng(exs)
        ::Symbol => var(exs, Any)


        # an array of Exprs and LineNumberNodes, like encountered as the body of a block.
        ::AbstractArray => let
            @assert !isempty(exs) "empty expression list?"

            (F, A, C, L) = scope

            ex = exs[1]
            tail = exs[2:end]


            if ex isa LineNumberNode
                return exprs_to_dmterm(tail, ex, scope)

            elseif ex isa Expr
                ex_head = ex.head

                #TODO again, using @match here makes the compiler go on forever.
                if ex_head == :function
                    head, body = ex.args
                    constr = lam
                    name = head.args[1]
                    if L && head in C
                        error("overwriting an existing function in a loop is not allowed in $ex, $(ln.file) line $(ln.line)")
                    elseif !(name isa Symbol)
                        if head.head == :(::)
                            annotation = head.args[2]
                            # check for privacy lambda annotation
                            if annotation.head == :call && annotation.args[1] == :Priv
                                constr = lam_star
                                head = head.args[1]
                                name = head.args[1]
                            else
                                error("function return type annotation not supported yet in $ex, $(ln.file) line $(ln.line).")
                            end
                        else
                            error("function return type annotation not supported yet in $ex, $(ln.file) line $(ln.line).")
                        end
                    elseif is_builtin_op(name)
                        error("overwriting builtin function $name in $ex, $(ln.file) line $(ln.line) is not permitted.")
                    end
                    vs = Symbol[]
                    ts = DataType[]
                    for a in head.args[2:end]
                        if a isa Symbol
                            push!(vs, a)
                            push!(ts, Any)
                        elseif a isa Expr && a.head == :(::)
                            s, T = a.args
                            Tt = eval(T)
                            if !type_allowed(Tt)
                                error("dispatch on number types finer than Real and Integer is not allowed! Argument $s has type $Tt in definition of function $head, $(ln.file) line $(ln.line)")
                            end
                            push!(vs, s)
                            push!(ts, Tt)
                        else
                            ln = body.args[1]
                            error("keyword/vararg/optional arguments not yet supported in function definition $head, $(ln.file) line $(ln.line)")
                        end
                    end
                    tailex = isempty(tail) ? var(name, Any) : exprs_to_dmterm(tail, ln, scope)
                    newscope = ([[name]; F], vs, union(C, setdiff(A, vs), [head]), L)
                    return flet(name, ts, constr(collect(zip(vs, ts)), exprs_to_dmterm(body, ln, newscope)), tailex)

                elseif ex_head == :(=)
                    ase, asd = ex.args
                    if ase isa Expr && ase.head == :call
                        f = ase.args
                        return exprs_to_dmterm([[Expr(:function, ase, asd)]; tail], ln, scope)
                    elseif ase isa Symbol
                        if ase in C
                            error("illegal modification of variable $ase from an outer scope in $ex, $(ln.file) line $(ln.line)")
                        elseif is_builtin_op(ase)
                            error("overwriting builtin function $ase in $ex, $(ln.file) line $(ln.line) is not permitted.")
                        end
                        v = (ase, Any)
                        newscope = (F, [[ase]; A], C, L)
                        return slet(v, exprs_to_dmterm(asd, ln, newscope), isempty(tail) ? var(v...) : exprs_to_dmterm(tail, ln, newscope))
                    elseif ase isa Expr && ase.head == :(::)
                        s, T = ase.args
                        if s in C
                            error("illegal modification of variable $ase from an outer scope in $ex, $(ln.file) line $(ln.line)")
                        elseif !(s isa Symbol) #TODO PRiv
                            error("type assignment not yet supported for $s in  $ex, $(ln.file) line $(ln.line)")
                        elseif is_builtin_op(s)
                            error("overwriting builtin function $s in $ex, $(ln.file) line $(ln.line) is not permitted.")
                        end
                        v = (s, eval(T))
                        newscope = (F, [[s]; A], C, L)
                        return slet(v, exprs_to_dmterm(asd, ln, newscope), isempty(tail) ? var(v...) : exprs_to_dmterm(tail ,ln, newscope))
                    else
                        error("unsupported assignment in $ex, $(ln.file) line $(ln.line)")
                    end

                elseif ex_head == :(+=)
                    ase, asd = ex.args
                    return exprs_to_dmterm([[:($ase = $ase + $asd)]; tail], ln, scope)
                elseif ex_head == :(-=)
                    ase, asd = ex.args
                    return exprs_to_dmterm([[:($ase = $ase - $asd)]; tail], ln, scope)
                elseif ex_head == :(*=)
                    ase, asd = ex.args
                    return exprs_to_dmterm([[:($ase = $ase * $asd)]; tail], ln, scope)
                elseif ex_head == :(/=)
                    ase, asd = ex.args
                    return exprs_to_dmterm([[:($ase = $ase / $asd)]; tail], ln, scope)

                elseif ex_head == :if
                    if length(ex.args) == 2
                        cond, ife = ex.args
                        @assert cond isa Symbol || cond isa Number || cond.head == :call "unsupported if condition $cond in $ex, $(ln.file) line $(ln.line)."
                        return phi(exprs_to_dmterm(cond, ln, scope), exprs_to_dmterm([[ife]; tail], ln, scope), exprs_to_dmterm(tail, ln, scope))

                    elseif length(ex.args) == 3
                        cond, ife, ele = ex.args
                        @assert cond isa Symbol || cond isa Number || cond.head == :call "unsupported if condition $cond in $ex, $(ln.file) line $(ln.line)."
                        return phi(exprs_to_dmterm(cond, ln, scope), exprs_to_dmterm([[ife]; tail], ln, scope), exprs_to_dmterm([[ele]; tail], ln, scope))
                    end

                elseif ex_head == :elseif
                    if length(ex.args) == 2
                        cond, ife = ex.args
                        @assert cond.head == :block && length(cond.args) == 2 "it seems elseif conditions can be various..."
                        @assert cond isa Symbol || cond isa Number || cond.args[2].head == :call "unsupported if condition $cond in $ex, $(ln.file) line $(ln.line)."
                        phi(exprs_to_dmterm(cond.args[2], cond.args[1], scope),
                            exprs_to_dmterm([[ife]; tail], ln, scope),
                            exprs_to_dmterm(tail, ln, scope))
                    elseif length(ex.args) == 3
                        cond, ife, ele = ex.args
                        @assert cond.head == :block && length(cond.args) == 2 "it seems elseif conditions can be various..."
                        @assert cond isa Symbol || cond isa Number || cond.args[2].head == :call "unsupported if condition $cond in $ex, $(ln.file) line $(ln.line)."
                        phi(exprs_to_dmterm(cond.args[2], cond.args[1], scope),
                            exprs_to_dmterm([[ife]; tail], ln, scope),
                            exprs_to_dmterm([[ele]; tail], ln, scope))
                    end

                # a special tuple exclusively for loop returns
                elseif ex_head == :dtuple
                    tup(map(e -> exprs_to_dmterm(e, ln, scope), ex.args))


                elseif ex_head == :for
                    it, body = ex.args
                    # unpack one-liner multi-iteration
                    if it.head == :block
                        loops = body
                        for its in it.args
                            loops = Expr(:for, its, loops)
                        end
                        return exprs_to_dmterm([[loops]; tail], ln, scope)
                    end

                    # extract the iterator
                    if it isa Expr && it.head == :(=)
                        i, r = it.args
                        @assert i isa Symbol "expected symbol $i"
                        if r isa Expr && r.head == :call
                            @assert r.args[1] == :(:) "expected colon in iterator $it"
                            if length(r.args) == 3
                                b, e = r.args[2:3]
                                lit = iter(exprs_to_dmterm(b, ln, scope), sng(1), exprs_to_dmterm(e, ln, scope))
                            elseif length(r.args) == 4
                                b, s, e = r.args[2:4]
                                lit = iter(exprs_to_dmterm(b, ln, scope), exprs_to_dmterm(s, ln, scope), exprs_to_dmterm(e, ln, scope))

                            elseif r isa Symbol
                                lit = var(r, Any)
                            else
                                error("unsupported iterator $r in $(ln.file) line $(ln.line)")
                            end
                        end
                    else
                        error("unsupported iteration over $it in $(ln.file) line $(ln.line)")
                    end

                    # a placeholder for the capture tuple, as we don't know yet what is going to be inside it
                    capst = gensym()
                    # make the body explicitly return the captures
                    if body.head == :block
                        push!(body.args, Expr(:dtuple, capst))
                    else
                        body = Expr(:block, body, Expr(:dtuple, capst))
                    end

                    # parse loop body
                    # capture iteration variable as it cannot be modified #TODO protect vector elements?
                    lbody = exprs_to_dmterm(body, ln, (F, A, C ∪ [i], true))

                    # TODO this is pretty expensive. maybe make the parser return the assignees of the current block?
                    function collect_assignments(t::DMTerm)
                        @match t begin
                            slet(x,a,b) => union([first(x)], collect_assignments(a), collect_assignments(b))
                            tlet(xs,a,b) => union(map(first, xs), collect_assignments(a), collect_assignments(b))
                            _ => let
                                targs = map(fld->getfield(t,fld), fieldnames(typeof(t)))
                                union(map(collect_assignments, targs))
                            end
                        end
                    end
                    collect_assignments(t) = []

                    # collect all variables that are arguments or internal variables of the innermost
                    # function *and* assigned to in the loop body. these are explicitly captured.
                    # don't mind functions, inside loops it's forbidden to assign them anyways
                    caps = filter(s->s isa Symbol && s != i, intersect(A, collect_assignments(lbody)))

                    newcaptup = tup(map(e -> exprs_to_dmterm(e, ln, scope), caps)) # make a tup from the captures
                    # replace the capture term in the loop body dmterm by the new tup TODO this is messy
                    lbody = typeof(lbody)(map(fld->getfield(lbody,fld), fieldnames(typeof(lbody))[1:end-1])...,newcaptup)

                    # body lambda maps captures  to body
                    cname = gensym("caps")
                    captasgmts = [(c, Any) for c in caps]
                    llam = lam([(i, Int), (cname, Any)], tlet(captasgmts, var(cname, Any), lbody))

                    lloop = loop(lit, tup(map(v->var(v...), captasgmts)), llam)

                    return tlet(captasgmts, lloop, exprs_to_dmterm(tail, ln, scope))

                    #=
                    if iter isa Expr && iter.head == :vect
                        #TODO this comes at high cost! vector refs are expensive :(
                        vsym = gensym()
                        isym = gensym()
                        push!(nexs, :($vsym = $iter))
                        pushfirst!(body.args, :($i = $vsym[$isym]))
                        i = isym
                        iter = :(1:length($vsym))
                    end
                    =#

                elseif ex_head == :call
                    f = ex.args[1]
                    args = ex.args[2:end]
                    if f == :include
                        if length(args) != 1
                            error("include with mapexpr not supported: $ex in $(ln.file) line $(ln.line)")
                        end
                        inast = Meta.parseall(read(args[1], String), filename = args[1])
                        return exprs_to_dmterm([inast.args; tail], inast.args[1], scope)
                    elseif isempty(tail)
                        if f in F
                            error("recursive call of $f in in $(ln.file) line $(ln.line)")
                        end
                        exprs_to_dmterm(ex, ln, scope)
                    else
                        error("calls without assignments are forbidden. are you trying to mutate something? $ex in $(ln.file) line $(ln.line)")
                    end

                elseif ex_head == :block
                    args = ex.args
                    if args[1] isa LineNumberNode
                        exprs_to_dmterm([args[2:end]; tail], args[1], scope)
                    else
                        exprs_to_dmterm([args; tail], ln, scope)
                    end

                elseif ex_head == :return
                    arg = ex.args[1]
                    if L
                        error("use of return is forbidden inside loops in $ex, $(ln.file) line $(ln.line)")
                    end
                    exprs_to_dmterm(arg, ln, scope)

                else
                    error("unsupported expression type $ex_head in $ex, $(ln.file) line $(ln.line)")
                end
            else
                isempty(tail) ? exprs_to_dmterm(ex, ln, scope) : error("something unsupported: $ex in $(ln.file) line $(ln.line)")
            end
        end;

        # single expressions, as encountered only at the end of an expression block.
        ::Expr => let
            ex = exs
            @assert ln isa LineNumberNode "expected a LineNumerNode $ln"
            (F, A, C, L) = scope

            if ex.head == :block
                args = ex.args
                if args[1] isa LineNumberNode
                    return exprs_to_dmterm(args[2:end], args[1], scope)
                else
                    return exprs_to_dmterm(args, ln, scope)
                end

            elseif ex.head == :call
                eargs = ex.args
                callee = eargs[1]
                args = eargs[2:end]
                if callee == :gaussian_mechanism
                    ats = map(a->exprs_to_dmterm(a, ln, scope), args)
                    @assert length(ats) == 4 "wrong number of arguments for gauss: $ex in $(ln.file) line $(ln.line)"
                    return gauss((ats[1:3]...,), ats[4])
                elseif callee isa Symbol && is_builtin_op(callee)
                    if length(args) == 1
                        return  op(callee, [exprs_to_dmterm(args[1], ln, scope)])
                    else
                        if callee == :(==) && length(args) != 2
                            error("invalid number of arguments for == in $(ln.file) line $(ln.line)")
                        end
                        # reduce nests multi-arg ops like x+x+x -> op(+, op(+, x, x), x)
                        return reduce((x,y)->op(callee, [x,y]), map(a->exprs_to_dmterm(a, ln, scope), args))
                    end
                elseif callee in F
                    error("recursive call of $callee in $(ln.file) line $(ln.line)")
                else
                    return apply(exprs_to_dmterm(callee, ln, scope), map(a->exprs_to_dmterm(a, ln, scope), args)) #TODO DMDFunc type?
                end

            elseif ex.head == :(->)
                argt, body = ex.args
                as = argt isa Expr && argt.head == :tuple ? argt.args : [argt]
                vs = Symbol[]
                ts = DataType[]
                for a in as
                    if a isa Symbol
                        push!(vs, a)
                        push!(ts, Any)
                    elseif a isa Expr && a.head == :(::)
                        s, T = a.args
                        Tt = eval(T)
                        if !type_allowed(Tt)
                            error("dispatch on number types finer than Real and Integer is not allowed! Argument $s has type $Tt in definition of anonymous function at $(ln.file) line $(ln.line)")
                        end
                        push!(vs, s)
                        push!(ts, Tt)
                    else
                        ln = body.args[1]
                        error("keyword/vararg/optional arguments not yet supported in lambda definition $head, $(ln.file) line $(ln.line)")
                    end
                end
                newscope = (F, vs, union(C, setdiff(A, vs)), L)
                @assert body.head == :block
                return lam(collect(zip(vs, ts)), exprs_to_dmterm(body.args[2:end], body.args[1], newscope))
            else
                error("something unsupported: $ex with head $(ex.head), $(ln.file) line $(ln.line)")
            end

            #=
            @match ex begin
                Expr(:vect, args...) => let
                    vect(map(e -> exprs_to_dmterm(e, ln, scope), args))
                end;

                Expr(:ref, v, i) => let
                    if i isa Symbol || i isa Number
                        index(exprs_to_dmterm(v, ln, scope), exprs_to_dmterm(i, ln, scope))
                    else
                        error("unsupported reference $ex in $(ln.file) line $(ln.line)")
                    end
                end;
            end
            =#

        end;
        _ => error("invalid input type, expected Expr, Number, Symbol, or Array of those, but got $(typeof(exs))")
    end
end
