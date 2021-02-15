
using Test
include("../src/subtyping.jl");
include("../src/definitions.jl")


@testset "Subtyping" begin

    @testset "check no arrow" begin
        @test check_isSubtypeOf_noarr(DMInt(), DMInt()) == ([],[])
        @test check_isSubtypeOf_noarr(Constant(DMInt(), 7), DMReal()) == ([],[])
        @test_throws ErrorException check_isSubtypeOf_noarr(DMReal(), DMInt())
    end;

end;
