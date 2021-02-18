
"Construct a `TC` monad containing the computation of inferring `t`'s sensitivity."
function build_tc(t::DMTerm) :: TC
    @mdo TC begin
        checkr <- check_term(t) # typecheck the term
        tau <- simplify_constraints_lose_generality() # simplify all constraints
        r <- apply_subs(checkr) # apply substitutions made during simplification
        return r
    end
end


"""
   infer_sensitivity_from_string(s::String) :: DMType

Given a `String` of julia code, infer the type of the corresponding expression. The return value
is the type of the expression, a `DMType`, our custom types defined in `definitions.jl`. If the
expression is a function, it should be an `Arr` type with the argument sensitivities encoded next
to the argument types.

# Examples
julia> t = infer_sensitivity_from_string("
         function test(x, y)
           f(x) = 500*(x + y)
           z = 1
           g(x) = z*x
           z = 2/5
           f(g(x))
         end
         ")
         pretty_print(t)
Arr(Tuple{Union{Number, SymbolicUtils.Symbolic, var"#s18"} where var"#s18"<:SymbolicUtils.Sym,DMType}[(200.0, TVar(:op_arg_3)), (500, TVar(:op_arg_17))], TVar(:sup_29))

julia> pretty_print(t)
"(tvar.op_arg_3 @(200.0), tvar.op_arg_17 @(500)) ==> tvar.sup_29"
```
The output means that the expression is a two-argument function that is 200-sensitive in the first
and 500-sensitive in the second argument. The first argument is an Integer, and the second arguments'
and the return type could not be inferred (that's what the TVar means).
"""
function infer_sensitivity_from_string(s::String) :: DMType
    t = string_to_dmterm(s)
    infer_sensitivity(t)
end


"""
   infer_sensitivity_from_file(s::String) :: DMType

Given a filename pointing to some julia code, infer the type of the corresponding expression. `include`s
are resolved and parsed as well. The return value is the type of the expression, a `DMType`, our custom
types defined in `definitions.jl`. If the expression is a function, it should be an `Arr` type with
the argument sensitivities encoded next to the argument types.
"""
function infer_sensitivity_from_file(file::AbstractString) :: DMType
    t = file_to_dmterm(file)
    infer_sensitivity(t)
end

"Infer the type of a `DMTerm`."
function infer_sensitivity(t::DMTerm)
    m = build_tc(t)
    (c, τ) = run(m)
    return τ
end
