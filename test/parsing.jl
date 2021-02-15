
using Test

@testset "Parsing" begin

    include("../src/parse.jl")

    dir = (@__DIR__)*"/files/looptest_parse.jl"
    term = file_to_jterm(dir)

    evaled = eval(evaluate(term))

    # generate some random input
    as = rand(-100:1:100, 10)

    for a in as
        @test evaled(a) == looptest(a);
    end

    @test evaled(as) == looptest(as);

end;


