

####################################################################
# julia interface

builtin_ops = Dict(
                   :ceil => (1, τs -> Unary(DMOpCeil(), τs...)),
                   :+ => (2, τs -> Binary(DMOpAdd(), τs...)),
                   :- => (2, τs -> Binary(DMOpSub(), τs...)),
                   :* => (2, τs -> Binary(DMOpMul(), τs...)),
                   :/ => (2, τs -> Binary(DMOpDiv(), τs...)),
                   :% => (2, τs -> Binary(DMOpMod(), τs...)),
                   :rem => (2, τs -> Binary(DMOpMod(), τs...)),
                   :(==) => (2, τs -> Binary(DMOpEq(), τs...)),
                  )

builtin_mutations = Dict(
                         :gaussian_mechanism! => gauss,
                         :clip! => dmclip,
                         :subtract_gradient! => dmsubgrad
                        )

is_builtin_op(f::Symbol) = haskey(builtin_ops,f)
is_builtin_mutation(f::Symbol) = haskey(builtin_mutations,f)
is_builtin(f::Symbol) = is_builtin_op(f) || is_builtin_mutation(f)

"Get a map from some argument `DMType`s to the `DMTypeOp` corresponding to the input julia function."
getDMOp(f::Symbol) = is_builtin_op(f) ? builtin_ops[f] : error("Unsupported builtin op $f.")


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
    # println("starting parsing.")
    ast = Meta.parse("begin $code end")
    # error upon modification of nonlocal variables
    sanitize([ast], ln)
    # println("sanitizing complete.")
    exprs_to_dmterm([ast], ln)
end

# we forbid number types finer than Integer and Real as function signatures, so we can
# decide on dispatch without having to carry the exact julia type.
function type_allowed(t::Type)
    if t in [Integer, Real, Number, Any]
        return true
    elseif t == Matrix
        return true
    elseif t <: Matrix
        return type_allowed(t.parameters[1])
    elseif t <: Tuple
        return all(map(type_allowed, t.parameters))
     elseif t in [DMParams, DMGrads]
        return true
    else
        return false
    end
end

# extract the variable names, type signature and interestingness annotation from
# the expression head.
function build_signature(args, ln :: LineNumberNode, name = :anonymous)
   vs = Symbol[]
   ts = Type[]
   is = Bool[]
   for a in args
      if a isa Symbol
         push!(vs, a)
         push!(ts, Any)
         push!(is, true)
      elseif a isa Expr && a.head == :(::)
         s, T = a.args
         if T isa Expr && T.head == :call && T.args[1] == :NoData
            interesting = false
         else
            interesting = true
         end
         is = [is; interesting]
         Tt = eval(T)
         if !type_allowed(Tt)
            error("dispatch on number types finer than Real and Integer is not allowed!
                  Argument $s has type $Tt in definition of function $name($args), $(ln.file) line $(ln.line)")
         end
         push!(vs, s)
         push!(ts, Tt)
      else
         error("keyword/vararg/optional arguments not yet supported in function definition $name($args), $(ln.file) line $(ln.line)")
      end
   end
   return (vs, ts, is)
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
                if length(tail) == 1
                   return exprs_to_dmterm(tail[1], ex, scope)
                else
                   return exprs_to_dmterm(tail, ex, scope)
                end

            elseif ex isa Expr
                ex_head = ex.head

                #TODO again, using @match here makes the compiler go on forever.
                if ex_head == :function
                    head, body = ex.args
                    name = head.args[1]
                    constr = lam
                    if L && head in C
                        error("overwriting an existing function in a loop is not allowed in $ex, $(ln.file) line $(ln.line)")
                    elseif !(name isa Symbol)
                        if head.head == :(::)
                            annotation = head.args[2]
                            # check for privacy lambda annotation
                            if annotation isa Expr && annotation.head == :call && annotation.args[1] == :Priv
                                head = head.args[1]
                                name = head.args[1]
                                constr = lam_star
                            else
                                error("function return type annotation not supported yet in $ex, $(ln.file) line $(ln.line).")
                            end
                        else
                            error("function return type annotation not supported yet in $ex, $(ln.file) line $(ln.line).")
                        end
                    elseif is_builtin(name)
                        error("overwriting builtin function $name in $ex, $(ln.file) line $(ln.line) is not permitted.")
                    end

                    (vs, ts, is) = build_signature(head.args[2:end], body.args[1], name)

                    tailex = isempty(tail) ? var(name, Any) : exprs_to_dmterm(tail, ln, scope)
                    newscope = ([[name]; F], vs, union(C, setdiff(A, vs), [head]), L)
                    argvec = (constr == lam_star) ? collect(zip(zip(vs, ts), is)) : collect(zip(vs, ts))
                    return flet(name, constr(argvec, exprs_to_dmterm(body, ln, newscope)), tailex)

                elseif ex_head == :(=)
                    ase, asd = ex.args
                    # first case is one-line function assignments like "f(x) = 10", second is that with annotation
                    # like "f(x) :: Function = 10"
                    if ase isa Expr && (ase.head == :call || (ase.head == :(::) && ase.args[1].head == :call))
                        f = ase.args
                        return exprs_to_dmterm([[Expr(:function, ase, asd)]; tail], ln, scope)
                    elseif ase isa Symbol
                        if ase in C
                            error("illegal modification of variable $ase from an outer scope in $ex, $(ln.file) line $(ln.line)")
                        elseif is_builtin(ase)
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
                        elseif is_builtin(s)
                            error("overwriting builtin function $s in $ex, $(ln.file) line $(ln.line) is not permitted.")
                        end
                        v = (s, eval(T))
                        newscope = (F, [[s]; A], C, L)
                        return slet(v, exprs_to_dmterm(asd, ln, newscope), isempty(tail) ? var(v...) : exprs_to_dmterm(tail ,ln, newscope))
                    elseif ase isa Expr && ase.head == :tuple
                        function handle_elem(exm::Expr)
                           println("got expr $exm")
                           if exm.head == :(::)
                              s, T = exm.args
                           println("calling with $s, $T")
                              handle_elem(s,T)
                           else
                              error("unsupported assignment in $ex, $(ln.file) line $(ln.line)")
                           end
                        end
                        function handle_elem(elem::Symbol, T=(:Any))
                           if elem in C
                               error("illegal modification of variable $ase from an outer scope in $ex, $(ln.file) line $(ln.line)")
                           elseif is_builtin(elem)
                               error("overwriting builtin function $ase in $ex, $(ln.file) line $(ln.line) is not permitted.")
                           end
                           return (elem, eval(T))
                        end
                        println("args: $(ase.args)")
                        names = map(handle_elem, ase.args)
                        newscope = (F, [map(first, names); A], C, L)
                        return tlet(names, exprs_to_dmterm(asd, ln, newscope), isempty(tail) ? var(v...) : exprs_to_dmterm(tail ,ln, newscope))
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
                                be, ee = map(e -> exprs_to_dmterm(e, ln, scope), r.args[2:3])
                                lnit = op(:ceil, [op(:-, [ee, op(:-, [be, sng(1)])])])
                                lit = iter(be, sng(1), ee)
                            elseif length(r.args) == 4
                                be, se, ee = map(e -> exprs_to_dmterm(e, ln, scope), r.args[2:4])
                                lnit = op(:ceil, [op(:/, [op(:-, [ee, op(:-, [be, sng(1)])]), se])])
                                lit = iter(be, se, ee)
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

                    if length(caps) == 1
                        cap = caps[1]
                        # TODO we're actually parsing this twice that's not acceptable really
                        body = Expr(:block, body.args[1:end-1]..., cap)
                        lbody = exprs_to_dmterm(body, ln, (F, A, C ∪ [i], true))

                        # body lambda maps captures  to body
                        cname = gensym("caps")
                        llam = slet((cap, Any), var(cname, Any), lbody)

                        lloop = loop(lit, lnit, var(cap, Any), (i, cname), llam)

                        return slet((cap, Any), lloop, exprs_to_dmterm(tail, ln, scope))
                    else

                        # TODO we're actually parsing this twice that's not acceptable really
                        body = Expr(:block, body.args[1:end-1]..., Expr(:dtuple, caps...))
                        lbody = exprs_to_dmterm(body, ln, (F, A, C ∪ [i], true))

                        # body lambda maps captures  to body
                        cname = gensym("caps")
                        captasgmts = [(c, Any) for c in caps]
                        llam = tlet(captasgmts, var(cname, Any), lbody)

                        lloop = loop(lit, lnit, tup(map(v->var(v...), captasgmts)), (i, cname), llam)

                        return tlet(captasgmts, lloop, exprs_to_dmterm(tail, ln, scope))
                    end
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
                        return exprs_to_dmterm(ex, ln, scope)
                    elseif is_builtin_mutation(f)
                        ctor = builtin_mutations[f]
                        return mut_slet(ctor(exprs_to_dmterm(args[1], ln, scope), exprs_to_dmterm(args[2], ln, scope)),exprs_to_dmterm(tail, ln, scope))
                    elseif string(f)[end] == '!'
                        return mut_slet(var(f, Any), exprs_to_dmterm(tail, ln, scope))
                    else
                        error("non-mutating calls without assignments are forbidden. are you trying to mutate something? $ex in $(ln.file) line $(ln.line)")
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

            elseif ex.head == :tuple
                tup(map(e -> exprs_to_dmterm(e, ln, scope), ex.args))

            elseif ex.head == :call
                eargs = ex.args
                callee = eargs[1]
                args = eargs[2:end]
                if callee == :gaussian_mechanism
                    ats = map(a->exprs_to_dmterm(a, ln, scope), args)
                    @assert length(ats) == 4 "wrong number of arguments for gauss: $ex in $(ln.file) line $(ln.line)"
                    return gauss((ats[1:3]...,), ats[4])
                elseif callee == :zeros
                    ats = map(a->exprs_to_dmterm(a, ln, scope), args)
                    @assert length(ats) == 2 "wrong number of arguments for zeros: $ex in $(ln.file) line $(ln.line)"
                    return mcreate(ats..., (gensym(), gensym()), sng(0))
                elseif callee == :ones
                    ats = map(a->exprs_to_dmterm(a, ln, scope), args)
                    @assert length(ats) == 2 "wrong number of arguments for ones: $ex in $(ln.file) line $(ln.line)"
                    return mcreate(ats..., (gensym(), gensym()), sng(1))
                elseif callee == :randn
                    ats = map(a->exprs_to_dmterm(a, ln, scope), args)
                    if length(ats) == 0
                       return rnd(Float64)
                    elseif length(ats) == 1
                       rname = gensym()
                       return return slet((rname, Any), rnd(Real), mcreate(sng(1), ats[1], (gensym(), gensym()), var(rname, Any)))
                    elseif length(ats) == 2
                       rname = gensym()
                       return slet((rname, Any), rnd(Real), mcreate(ats..., (gensym(), gensym()), var(rname, Any)))
                    else
                        error("wrong number of arguments for randn: $ex in $(ln.file) line $(ln.line)")
                    end
                elseif callee == :transpose
                    @assert length(args) == 1 "wrong number of arguments for transpose: $ex in $(ln.file) line $(ln.line)"
                    return dmtranspose(exprs_to_dmterm(args[1], ln, scope))
                elseif is_builtin_mutation(callee)
                        ctor = builtin_mutations[callee]
                        return ctor(exprs_to_dmterm(args[1], ln, scope), exprs_to_dmterm(args[2], ln, scope))
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
                    callee_term = exprs_to_dmterm(callee, ln, scope)
                    return apply(callee_term, map(a->exprs_to_dmterm(a, ln, scope), args)) #TODO DMDFunc type?
                end

            elseif ex.head == :(->)
                argt, body = ex.args
                as = argt isa Expr && argt.head == :tuple ? argt.args : [argt]
                (vs, ts, _) = build_signature(as, body.args[1])
                newscope = (F, vs, union(C, setdiff(A, vs)), L)
                @assert body.head == :block
                return chce((ts, lam(collect(zip(vs, ts)), exprs_to_dmterm(body.args[2:end], body.args[1], newscope))))

            elseif ex.head == :ref
                    if length(ex.args) == 3
                        (m, i, j) = ex.args
                           if i isa Symbol || i isa Number
                              return index(exprs_to_dmterm(m, ln, scope), exprs_to_dmterm(i, ln, scope), exprs_to_dmterm(j, ln, scope))
                           else
                              error("unsupported reference $ex in $(ln.file) line $(ln.line)")
                           end
                    else
                        error("unsupported reference $ex in $(ln.file) line $(ln.line)")
                    end

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
