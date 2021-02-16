
using Test

@testset "Parsing" begin

    include("../src/parsing/parse.jl")
#=
    dir = (@__DIR__)*"/files/looptest_parse.jl"
    term = file_to_dmterm(dir)

    evaled = eval(evaluate(term))

    # generate some random input
    as = rand(-100:1:100, 10)

    for a in as
        @test evaled(a) == looptest(a);
    end

    @test evaled(as) == looptest(as);
=#

    dir = (@__DIR__)*"/files/parse_ops.jl"
    term = file_to_dmterm(dir)

    evaled = eval(evaluate(term))

    # generate some random input
    for _ in 1:10
        as = rand(-100:1:100, 4)
        @test evaled(as...) == parse_ops(as...);
    end
end;


