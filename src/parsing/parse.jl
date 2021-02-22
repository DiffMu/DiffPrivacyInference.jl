
"""
    file_to_dmterm(file::AbstractString)

Parse the file named `file` into a DMTerm. Includes are resolved and parsed as well.
All functions in the file will become nested `flet` terms, normal assignments are parsed
into `slet` terms. If the last statement of the file is a function definition or assignment,
the term will \"return\" that last variable."""
function file_to_dmterm(file::AbstractString) :: DMTerm
    ast = Compat.parseall(read(file, String), filename = file)
    println("read file $file")
    # error upon modification of nonlocal variables
    sanitize(ast.args, ast.args[1])
    exprs_to_dmterm(ast.args, ast.args[1])
end


"Parse a string into a DMTerm."
function string_to_dmterm(code::String, ln=LineNumberNode(1, "none")) :: DMTerm
    ast = Meta.parse("begin $code end")
    # error upon modification of nonlocal variables
    sanitize([ast], ln)
    exprs_to_dmterm([ast], ln)
end

# we forbid number types finer than Integer and Real as function signatures, so we can
# decide on dispatch without having to carry the exact julia type.
function type_allowed(t::DataType)
    if t in [Integer, Real, Number, Any]
        return true
    elseif t<: Vector
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
function exprs_to_dmterm(exs::AbstractArray, ln::LineNumberNode, scope = ([],[],[], false)) :: DMTerm

    @assert !isempty(exs) "empty expression list?"

    (F, A, C, L) = scope

    ex = exs[1]
    tail = exs[2:end]

    @match ex begin

        ::LineNumberNode => exprs_to_dmterm(tail, ex, scope)

        Expr(:function, head, body) => let
            if L && head in C
                error("overwriting an existing function in a loop is not allowed in $ex, $(ln.file) line $(ln.line)")
            end
            name = head.args[1]
            if !(name isa Symbol)
                error("function return type annotation not supported yet in $ex, $(ln.file) line $(ln.line).")
            elseif is_builtin_op(name)
                error("overwriting builtin function $name in $ex, $(ln.file) line $(ln.line) is not permitted.")
            end
            vs = Symbol[]
            ts = DataType[]
            for a in head.args[2:end]
                (v, t) = @match a begin
                    ::Symbol => (a, Any)
                    Expr(:(::), s, T) => let
                        Tt = eval(T)
                        if !type_allowed(Tt)
                            error("dispatch on number types finer than Real and Integer is not allowed! Argument $s has type $Tt in definition of function $head, $(ln.file) line $(ln.line)")
                        end
                        (s, Tt)
                    end
                    _ => let
                        ln = body.args[1]
                        error("keyword/vararg/optional arguments not yet supported in function definition $head, $(ln.file) line $(ln.line)")
                    end
                end;
                push!(vs, v)
                push!(ts, t)
            end
            tailex = isempty(tail) ? var(name, Any) : exprs_to_dmterm(tail, ln, scope)
            newscope = ([[name]; F], vs, union(C, setdiff(A, vs), [head]), L)
            return flet(name, ts, lam(collect(zip(vs, ts)), expr_to_dmterm(body, ln, newscope)), tailex)
        end;

        Expr(:(=), ase, asd) => let
            @match ase begin
                Expr(:call, f...) => exprs_to_dmterm([[Expr(:function, ase, asd)]; tail], ln, scope)
                ::Symbol => let
                    if ase in C
                        error("illegal modification of variable $ase from an outer scope in $ex, $(ln.file) line $(ln.line)")
                    elseif is_builtin_op(ase)
                        error("overwriting builtin function $ase in $ex, $(ln.file) line $(ln.line) is not permitted.")
                    end
                    v = (ase, Any)
                    newscope = (F, [[ase]; A], C, L)
                    slet(v, expr_to_dmterm(asd, ln, newscope), isempty(tail) ? var(v...) : exprs_to_dmterm(tail, ln, newscope))
                end;
                Expr(:(::), s, T) => let
                    if s in C
                        error("illegal modification of variable $ase from an outer scope in $ex, $(ln.file) line $(ln.line)")
                    elseif !(s isa Symbol)
                        error("type assignment not yet supported for $s in  $ex, $(ln.file) line $(ln.line)")
                    elseif is_builtin_op(s)
                        error("overwriting builtin function $s in $ex, $(ln.file) line $(ln.line) is not permitted.")
                    end
                    v = (s, eval(T))
                    newscope = (F, [[s]; A], C, L)
                    slet(v, expr_to_dmterm(asd, ln, newscope), isempty(tail) ? var(v...) : exprs_to_dmterm(tail ,ln, newscope))
                end;
                _ => error("unsupported assignment in $ex, $(ln.file) line $(ln.line)")
            end;
        end;

        Expr(:(+=), ase, asd) => exprs_to_dmterm([[:($ase = $ase + $asd)]; tail], ln, scope)
        Expr(:(-=), ase, asd) => exprs_to_dmterm([[:($ase = $ase - $asd)]; tail], ln, scope)
        Expr(:(*=), ase, asd) => exprs_to_dmterm([[:($ase = $ase * $asd)]; tail], ln, scope)
        Expr(:(/=), ase, asd) => exprs_to_dmterm([[:($ase = $ase / $asd)]; tail], ln, scope)

        Expr(:if, cond, ife) => let
            phi(expr_to_dmterm(cond, ln, scope), exprs_to_dmterm([[ife]; tail], ln, scope), exprs_to_dmterm(tail, ln, scope))
        end
        Expr(:if, cond, ife, ele) => let
            phi(expr_to_dmterm(cond, ln, scope), exprs_to_dmterm([[ife]; tail], ln, scope), exprs_to_dmterm([[ele]; tail], ln, scope))
        end;
        Expr(:elseif, cond, ife) => let
            @assert cond.head == :block && length(cond.args) == 2 "it seems elseif conditions can be various..."
            phi(expr_to_dmterm(cond.args[2], cond.args[1], scope),
                exprs_to_dmterm([[ife]; tail], ln, scope),
                exprs_to_dmterm(tail, ln, scope))
        end;
        Expr(:elseif, cond, ife, ele) => let
            @assert cond.head == :block && length(cond.args) == 2 "it seems elseif conditions can be various..."
            phi(expr_to_dmterm(cond.args[2], cond.args[1], scope),
                exprs_to_dmterm([[ife]; tail], ln, scope),
                exprs_to_dmterm([[ele]; tail], ln, scope))
        end;

        # a special tuple exclusively for loop returns
        Expr(:dtuple, args...) => let
            tup(map(e -> expr_to_dmterm(e, ln, scope), args))
        end;

        Expr(:for, it, body) => let

            # unpack one-liner multi-iteration
            if it.head == :block
                loops = body
                for its in it.args
                    loops = Expr(:for, its, loops)
                end
                return exprs_to_dmterm([[loops]; tail], ln, scope)
            end

            # extract the iterator
            i, lit = @match it begin
                Expr(:(=), i::Symbol, r) => let
                    @match r begin
                        Expr(:call, :(:), b, e) => (i, iter(expr_to_dmterm(b, ln, scope), sng(1), expr_to_dmterm(e, ln, scope)))
                        Expr(:call, :(:), b, s, e) => (i, iter(expr_to_dmterm(b, ln, scope), expr_to_dmterm(s, ln, scope), expr_to_dmterm(e, ln, scope)))
                        ::Symbol => (i, var(r, Any))
                        _ => error("unsupported iterator $r in $(ln.file) line $(ln.line)")
                    end
                end
                _ => error("unsupported iteration over $it in $(ln.file) line $(ln.line)")
            end

            # don't mind functions, inside loops it's forbidden to assign them anyways
            caps = filter(s->s isa Symbol && s != i, A)

            # make the body explicitly return the captures
            if body.head == :block
                push!(body.args, Expr(:dtuple, caps...))
            else
                body = Expr(:block, body, Expr(:dtuple, caps...))
            end

            # parse loop body
            # capture iteration variable as it cannot be modified #TODO protect vector elements?
            lbody = expr_to_dmterm(body, ln, (F, A, C ∪ [i], true))

            # body lambda maps captures  to body
            cname = gensym("caps")
            captasgmts = [(c, Any) for c in caps]
            llam = lam([(i, DMDInt()), (cname, Any)], tlet(captasgmts, var(cname, Any), lbody))

            lloop = loop(lit, tup(map(v->var(v...), captasgmts)), llam)

            return tlet(captasgmts, lloop, exprs_to_dmterm(tail, ln, scope))

            #=
            # TODO
            # remove captures that are not assigned to in the body
            # caps = caps ∩ assd

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
        end;

        Expr(:call, f, args...) => let
            if f == :include
                if length(args) != 1
                    error("include with mapexpr not supported: $ex in $(ln.file) line $(ln.line)")
                end
                inast = Compat.parseall(read(args[1], String), filename = args[1])
                return exprs_to_dmterm([inast.args; tail], inast.args[1], scope)
            elseif isempty(tail)
                if f in F
                    error("recursive call of $f in in $(ln.file) line $(ln.line)")
                end
                expr_to_dmterm(ex, ln, scope)
            else
                error("calls without assignments are forbidden. are you trying to mutate something? $ex in $(ln.file) line $(ln.line)")
            end
        end;

        Expr(:block, args...) => let
            if args[1] isa LineNumberNode
                exprs_to_dmterm([args[2:end]; tail], args[1], scope)
            else
                exprs_to_dmterm([args; tail], ln, scope)
            end
        end;

        Expr(:return, arg) => let
            if L
                error("use of return is forbidden inside loops in $ex, $(ln.file) line $(ln.line)")
            end
            expr_to_dmterm(arg, ln, scope)
        end;

        _ => isempty(tail) ? expr_to_dmterm(ex, ln, scope) : error("something unsupported: $ex in $(ln.file) line $(ln.line)")
    end
end


expr_to_dmterm(ex::Number, ln::LineNumberNode, (F, A, C, L)) :: DMTerm = sng(ex)
expr_to_dmterm(ex::Symbol, ln::LineNumberNode, (F, A, C, L)) :: DMTerm = var(ex, Any)

"""
    expr_to_dmterm(ex::Union{Number, Symbol, Expr}, ln::LineNumberNode, scope = ([],[],[], false))

Parse single expression into a DMTerm. Only expressions that are allowed to be the last
expression of a block are allowed here. `ln` is the current line and file.
`scope` is:
  - `F`: Names of the functions in whose bodys the `exs` live.
  - `A`: Names of argument variables of the innermost function -- these can be modified/assigned to.
  - `C`: Names of variables captured from outside the innermost function -- these cannot be assigned to.
  - `L`: `bool` variable indicating whether the parsed expressions are inside a loop body, as different rules apply there.
"""
function expr_to_dmterm(ex::Expr, ln::LineNumberNode, (F, A, C, L)) :: DMTerm

    scope = (F, A, C, L)

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
        if callee isa Symbol && is_builtin_op(callee)
            if length(args) == 1
                return op(callee, [expr_to_dmterm(args[1], ln, scope)])
            else
                # reduce nests multi-arg ops like x+x+x -> op(+, op(+, x, x), x)
                return reduce((x,y)->op(callee, [x,y]), map(a->expr_to_dmterm(a, ln, scope), args))
            end
        elseif callee in F
            error("recursive call of $callee in $(ln.file) line $(ln.line)")
        else
            return apply(expr_to_dmterm(callee, ln, scope), map(a->expr_to_dmterm(a, ln, scope), args)) #TODO DMDFunc type?
        end

    elseif ex.head == :(->)
        argt, body = ex.args
        as = argt isa Expr && argt.head == :tuple ? argt.args : [argt]
        vs = Symbol[]
        ts = DataType[]
        for a in as
            (v, t) = @match a begin
                ::Symbol => (a, Any)
                Expr(:(::), s, T) => let
                    Tt = eval(T)
                    if !type_allowed(Tt)
                        error("dispatch on number types finer than Real and Integer is not allowed! Argument $s has type $Tt in definition of anonymous function at $(ln.file) line $(ln.line)")
                    end
                    (s, eval(T))
                end
                _ => let
                    ln = body.args[1]
                    error("keyword/vararg/optional arguments not yet supported in lambda definition $head, $(ln.file) line $(ln.line)")
                end
            end;
            push!(vs, v)
            push!(ts, t)
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
            vect(map(e -> expr_to_dmterm(e, ln, scope), args))
        end;

        Expr(:ref, v, i) => let
            if i isa Symbol || i isa Number
                index(expr_to_dmterm(v, ln, scope), expr_to_dmterm(i, ln, scope))
            else
                error("unsupported reference $ex in $(ln.file) line $(ln.line)")
            end
        end;
    end
    =#
end

