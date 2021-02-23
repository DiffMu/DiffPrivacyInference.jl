
using Test

@testset "Parsing" begin
    code = "function parse_test(w::Integer,x,y::Real,z)
                x = 3*(x+y) - z*ceil(x) + ceil(y) % 4 - 3/x + w/3
                l :: Integer = 100
                if l < 1
                   p = x*y
                elseif l > 1
                   p = ((x, y::Integer) -> x+1-y)(l,x)
                else
                   f(x) = 100
                   p = f(l)
                end
                return p
            end"
    term = string_to_dmterm(code)

    evaled = eval(evaluate(term))
    eval(code)

    # generate some random input
    for _ in 1:10
        as = rand(-100:1:100, 4)
        @test evaled(as...) == parse_ops(as...);
    end
end;


