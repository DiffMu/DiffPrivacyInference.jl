using IRTools: IR, Variable

parse_tuple(s::AbstractString) = Tuple(parse(Float64,t) for t in split(s ,[',','(',')'], keepempty=false))

# match
# # builtin ctr
# # sensitivity S
# # privacy (E1,D1) (E2,D2) (E3,D3)
# where ctr is the DMTerm constructor for the builtin and S, E* are real numbers (including Inf)
# no match returns "none", nothing
function read_comment(path::AbstractString, line::Integer)
    # read until line, extract comment
    for (i, l) in enumerate(eachline(path))
        #TODO in v1.5 we won't need the -2 anymore, which will point to the header directly
        if i == line-2
            if startswith(l, "#")
                try # if parsing fails somewhere, return nothing
                    s = split(l[2:end], ' ', keepempty=false)

                    if s[1] == "sensitivity"
                        #TODO multiple arguments?
                        return s[1], map(x->parse(Float64,x), s[2:end])

                    elseif s[1] == "privacy"
                        return s[1], map(parse_tuple, s[2:end])

                    elseif s[1] == "builtin"
                        return s[1], Meta.parse(s[2])
                    end

                catch e
                    println("malformed annotation in $e")
                    return "none", nothing
                end
            end
            # there is no comment before the function definition
            return "none", nothing
        end
    end
end

# return annotation of the function called/invoked at given expression in given CodeInfo
#
# example usage:
# julia> get_annotation(code_typed(foo)[1][1], code_typed(foo)[1][1].code[2])
#
# annotations are assumed to be one of
# # builtin ctr
# # sensitivity S
# # privacy (E1,D1) (E2,D2) (E3,D3)
# where ctr is the DMTerm constructor for the builtin and S, E* are real numbers (including Inf)
# returns what kind of annotation it has, the annotation itself, and the Method that was called
# no match returns "none", nothing, nothing
function get_annotation(ir::IR, expr::Expr)

    #TODO :foreigncall? other possible Expr heads?

    if expr.head == :invoke
        println("invoked: ", expr.args[1])
        #println("module: ", expr.args[1].def.module)

        # get location of the function source code
        path, line = functionloc(expr.args[1])
        annotation = read_comment(path, line)

        return annotation, (eval(expr.args[1].def.name), expr.args[1].def.sig.parameters[2:end])
    end

    if expr.head == :call


        # collect argument types
        args = DataType[]
        for a in expr.args[2:end]
            if isa(a, Variable)
                # SSA statements
                block, stmt_id = ir.defs[a.id]
                if stmt_id > 0
                    t = ir.blocks[block].stmts[stmt_id].type
                else # it's an argument of the block
                    t = ir.blocks[block].argtypes[-stmt_id]
                end
                if t isa Core.Compiler.Const
                    t = typeof(t.val)
                end
                push!(args, t)
            else #TODO are there other possible types?
                # constants
                push!(args, typeof(a))
            end
        end

        println("called: ", expr.args[1],"(::",args,")")

        #TODO expr.args[1] could be an SSA val pointing to the function def...

        # get location of the function source code
        method = which(eval(expr.args[1]), args)
        path, line = functionloc(method)
        annotation = read_comment(path, line)


        return annotation, (eval(expr.args[1]), args)
    end

    throw(ErrorException("no annotation extraction supported for $(expr.head) expressions"))
end

