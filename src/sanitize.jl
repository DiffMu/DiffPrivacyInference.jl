# make Expr matchable
@as_record Expr
@as_record LineNumberNode

"""
    sanitize_file(file::AbstractString)

Enforce the following hygiene rules on the whole `file` as well as all `includes`:

It is not allowed to
 - modify anything from an outer scope within the body of a function (like `f(x) = (y = 10)` if `y` is defined somewhere).
 - make assignments within the top-level scope of the body of an assignment (like `x = (y = 20)`).
 - use `+=` and friends on things that are not yet defined.

It returns two `Dict`s mapping variables to line numbers of:
 - the variables that are assigned to in any "inner scopes", that is within function bodies inside this block.
 - the variables this block assigns to.
"""
function sanitize_file(file::AbstractString)
    ast = Meta.parseall(read(file, String), filename = file)
    println("read file $file")
    sanitize(ast.args, ast.args[1])
end


"Enforce the hygiene rules on a single expression."
function sanitize(ex, ln::LineNumberNode, F, current = Dict()) :: Tuple{Dict, Dict}
    sanitize([ex], ln, F, current)
end


function merge_blocks(b1, b2) :: Expr
   (e1, e2) = @match (b1, b2) begin
      (Expr(:block, e1...), Expr(:block, e2...))  => (e1,e2)
      (Expr(:block, e1...), e2)  => (e1,e2)
      (e1, Expr(:block, e2...))  => (e1,e2)
      (e1, e2) => (e1,e2)
   end
   return Expr(:block, [e1; e2]...)
end

rearrange(::Nothing) = nothing
rearrange(exin::Symbol) :: Symbol = exin
rearrange(exin::LineNumberNode) :: LineNumberNode = exin
rearrange(exin::QuoteNode) = rearrange(exin.value)
rearrange(exin::Number) :: Number = exin
function rearrange(exin::Expr) :: Expr
   @match exin begin
      Expr(:block, exs...) => let
         ex = exs[1]
         tail = length(exs)==2 ? exs[2] : Expr(:block,exs[2:end]...)
         @match ex begin
            Expr(:call, :include, args) => let
               if length(args) != 1
                  error("include with mapexpr not supported: $ex")
               end
               inast = Meta.parseall(read(args[1], String), filename = args[1])
               return rearrange(merge_blocks(inast, tail))
            end
            Expr(:if, cond, ifb, elseb) => let
               rtail = rearrange(tail)
               rifb = rearrange(merge_blocks(ifb, rtail))
               relseb = rearrange(merge_blocks(elseb, rtail))
               return Expr(:if, rearrange(cond), rifb, relseb)
            end
            Expr(:if, cond, ifb) => let
               rtail = rearrange(tail)
               rifb = rearrange(merge_blocks(ifb, rtail))
               return Expr(:if, rearrange(cond), rifb, rtail)
            end
            Expr(:elseif, cond, ifb, elseb) => let
               rtail = rearrange(tail)
               rifb = rearrange(merge_blocks(ifb, rtail))
               relseb = rearrange(merge_blocks(elseb, rtail))
               return Expr(:elseif, rearrange(cond), rifb, relseb)
            end
            Expr(:elseif, cond, ifb) => let
               rtail = rearrange(tail)
               rifb = rearrange(merge_blocks(ifb, rtail))
               return Expr(:if, rearrange(cond), rifb, rtail)
            end
            head => let
               return merge_blocks(rearrange(head), rearrange(tail))
            end
         end
      end
      Expr(head, args...) => return Expr(head, map(rearrange, args)...)
   end
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


"""
    sanitize(exs, ln, F, current = Dict())

Enforce the following hygiene rules on a block of expressions:

It is not allowed to
 - modify anything from an outer scope within the body of a function (like `f(x) = (y = 10)` if `y` is defined somewhere).
 - make assignments within the top-level scope of the body of an assignment (like `x = (y = 20)`).
 - use `+=` and friends on things that are not yet defined.

# Arguments:
- `exs::AbstractArray`: vector of  `Expr`s, `LineNumberNode`s, `Number`s and `Symbols`.
- `ln::LineNumberNode`: the current line and file.
- `F`: Names of the functions in whose bodys the `exs` live.
- `current = Dict()`: the variables that are assigned to in the current scope, that is within the current function body.
"""
function sanitize(exs::AbstractArray, ln::LineNumberNode, F = [], current = Dict()) :: Tuple{Dict, Dict}

    inner = Dict()

    for ex in exs
        @match ex begin
            ::LineNumberNode => begin ln = ex end;

            Expr(:function, head, body) => let
                if  head.head  == :(::)
                    head = head.args[1] # ignore annotation
                end

                # collect this function's variables
                vs = []
                for a in head.args[2:end]
                    @match a begin
                        ::Symbol => push!(vs, a)
                        Expr(:(::), s, T) => let
                            if !type_allowed(eval(T))
                                if (eval(T) <: Number)
                                   error("Dispatch on number types finer than Real or Integer is not allowed!
                                          Argument $s has type $T in definition of function $head")
				else
				   error("Type $T not supported as function argument type of $s in definition of function $head")
 				end
                            else
                                push!(vs, s)
                            end
                        end;
                        x => error("Invalid function argument $x in $(ln.file) line $(ln.line)")
                    end;
                end

                # sanitize the body, with only the arguments in scope.
                fin, fcur = sanitize(body, ln, F ∪ [head.args[1]], Dict(v => body.args[1] for v in vs))

                # if inner scopes within the function body modify the function arguments, error
                culprits = vs ∩ keys(fin)
                if !isempty(culprits)
                    err = "forbidden mutation of a variable from an outer scope!\n"
                    for k in culprits
                        err *= "    Variable $k, argument of function $(head.args[1])"
                        err *= " defined at $(body.args[1].file) line $(body.args[1].line),"
                        err *= " is assigned to in a nested scope in $(fin[k].file) line $(fin[k].line)\n"
                    end
                    error(err)
                end

                # everything that was assigned to in the function body gets collected in "inner" of this exs.
                # then once we are done with the current scope we can check if some inner scope modified
                # anything from the "current" scope.
                # we can't just check if (current ∩ (fcur ∪ fin) = ∅) because it is possible that variables are
                # defined after the function definition:
                # function f()
                #    g() = (b = 100)
                #    b = 10
                #    g()
                #    b
                # end     ----> returns 100

                # the argument variables are not added to the forbidden scope, as the are local to the function.
                for v in vs
                    delete!(fcur, v)
                end
                inner = merge(fin, fcur, inner)

                # add function name as current variable
                # this means no method definitions in inner scopes
                fname = head.args[1]
                if !haskey(current, fname) current[fname] = ln end
            end;

            Expr(:(->), argt, body) => let
                # arguments of the lambda
                largs = argt isa Symbol ? [argt] : argt.args

                # give the lambda a temporary name so we can use the code for :function
                tempname = gensym()
                fin, fcur = sanitize(Expr(:function, Expr(:call, tempname, largs...), body), ln, F, current)
                # the temporary name should not stay in cur tho
                delete!(fcur, tempname)

                inner = merge(fin, inner)
                current = merge(fcur, current)
            end;

            Expr(:(=), ase, asd) => let
                @match ase begin
                    Expr(:call, f...) => let
                        fin, fcur = sanitize(Expr(:function, ase, asd), ln, F, current)
                        inner = merge(fin, inner)
                        current = merge(fcur, current)
                        continue;
                    end;
                    ::Symbol => let
                        if !haskey(current, ase) current[ase] = ln end
                    end
                    Expr(:(::), s, T) => let
                        if (s isa Symbol && !haskey(current, s))
                           current[s] = ln
                        elseif s isa Expr && s.head == :call
                           fin, fcur = sanitize(Expr(:function, ase, asd), ln, F, current)
                           inner = merge(fin, inner)
                           current = merge(fcur, current)
                           continue;
                        else
                           error("unsupported assignment in $ex, $(ln.file) line $(ln.line)")
                        end
                    end
                    Expr(:tuple, tnames...) => let
                        function handle_elem(eex::Expr)
                           if eex.head == :(::)
                              handle_elem(eex.args[1])
                           else
                              println("expression was $e")
                              error("unsupported assignment in $ex, $(ln.file) line $(ln.line)")
                           end
                        end
                        function handle_elem(s::Symbol)
                           if !haskey(current, s)
                              current[s] = ln
                           end
                        end
                        map(handle_elem, tnames)
                    end
                    _ => error("unsupported assignment in $ex, $(ln.file) line $(ln.line)")
                end;

                din, dcur = sanitize(asd, ln, F)

                # julia allows x = y = 10, we don't
                if !isempty(keys(dcur))
                    err = "assignments within assignments are forbidden\n"
                    for k in keys(dcur)
                        err *= "    Variable $k is assigned to at $(dcur[k].file) line $(dcur[k].line)\n"
                    end
                    error(err)
                end

                # we do allow things like f = x -> (y = 10) if y is local, so we need to keep din
                inner = merge(din, inner)
            end;

            Expr(:(+=), ase, asd) => let
                if !haskey(current, ase)
                    error("trying to overwrite variable $ase that is not in scope in $(ln.file) line $(ln.line)")
                end
                fin, fcur = sanitize(Expr(:(=), ase, Expr(:+, ase, asd)), ln, F, current)

                inner = merge(fin, inner)
                current = merge(fcur, current)
            end;

            Expr(:(-=), ase, asd) =>  let
                if !haskey(current, ase)
                    error("trying to overwrite variable $ase that is not in scope in $(ln.file) line $(ln.line)")
                end
                fin, fcur = sanitize(Expr(:(=), ase, Expr(:-, ase, asd)), ln, F, current)

                inner = merge(fin, inner)
                current = merge(fcur, current)
            end;

            Expr(:(*=), ase, asd) =>  let
                if !haskey(current, ase)
                    error("trying to overwrite variable $ase that is not in scope in $(ln.file) line $(ln.line)")
                end
                fin, fcur = sanitize(Expr(:(=), ase, Expr(:*, ase, asd)), ln, F, current)

                inner = merge(fin, inner)
                current = merge(fcur, current)
            end;

            Expr(:call, f, args...) => let
                if f in F
                   error("recursive call of $f in in $(ln.file) line $(ln.line)")
                end
                if f == :include
                    if length(args) != 1
                        error("include with mapexpr not supported: $ex in $(ln.file) line $(ln.line)")
                    end

                    # parse and sanitize the whole included file, too
                    inast = Meta.parseall(read(args[1], String), filename = args[1])
                    iinn, icur = sanitize(inast.args, inast.args[1], [], current)
                    inner = merge(inner, iinn)
                    current = merge(current, icur)

                elseif !(f isa Symbol)
                    fin, fcur = sanitize(f, ln, F, current)
                    inner = merge(fin, inner)
                    current = merge(fcur, current)
                end
            end;

            Expr(_, args...) => let
                ein, ecur = sanitize(args, ln, F, current)
                inner = merge(ein, inner)
                current = merge(ecur, current)
            end;

            _ => nothing;
        end

    end # end loop

    # inner contains everything that was assigned to in any inner scope of exs
    # current contains everything that was assigned to in the top-level scope of exs,
    # plus the arguments of the function if exs is in the top-level scope of a function.
    culprits = keys(inner) ∩ keys(current)
    if !isempty(culprits)
        err = "forbidden mutation of a variable from an outer scope!\n"
        for k in culprits
            err *= "    Variable $k, defined at $(current[k].file) line $(current[k].line),"
            err *= " is assigned to in a nested scope in $(inner[k].file) line $(inner[k].line)\n"
        end
        error(err)
    end

    return (inner, current)
end
