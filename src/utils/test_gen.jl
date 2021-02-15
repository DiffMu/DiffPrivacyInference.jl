using Serialization

include("../parsing/parse.jl")
include("../typechecking/typecheck.jl")
include("../typechecking/simplify.jl")


# parse function f and write testcases for check_sens, evaluate_constraints and simplifyConstraints_LoseGenerality
function write_testcases_all(f::Function)
    t = func_to_dmterm(f)
    name = string(f)
    write_testcases_all(name, t)
end

function write_testcases_all(name::String, t::DMTerm)
    dir = (@__DIR__)*"/../test/files"
    R = write_testcase("$dir/$(name)_check.jls", t, check_sens)[1:2]
    R = write_testcase("$dir/$(name)_eval.jls", R, r -> evaluate_constraints(r...))
    R = write_testcase("$dir/$(name)_simpl.jls", R, r -> simplifyConstraints_LoseGenerality(r...))
    return (t, R)
end

function write_testcase(filename::AbstractString, inp::Any, testee::Function)
    outp = testee(inp)

    serialize(filename, (inp, outp))
    # consider transparent serialization:
    #    open(filename, "w") do io
    #        write(io, string(inp), "\n")
    #        write(io, string(outp), "\n")
    #    end;

    return outp
end
