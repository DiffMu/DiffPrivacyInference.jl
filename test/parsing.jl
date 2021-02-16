
using Test

@testset "Parsing" begin
    code = "parse_ops(w,x,y,z) = 3*(x+y) - z*ceil(x) + ceil(y) % 4 - 3/x + w/3"
    term = string_to_dmterm(code)

    evaled = eval(evaluate(term))
    eval(code)

    # generate some random input
    for _ in 1:10
        as = rand(-100:1:100, 4)
        @test evaled(as...) == parse_ops(as...);
    end
end;


