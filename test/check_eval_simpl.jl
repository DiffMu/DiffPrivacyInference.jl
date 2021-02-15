
using Test
using Serialization

@testset "Checking" begin
    include("../src/typecheck.jl")
    dir = (@__DIR__)*"/files/"
    for f in filter(f->endswith(f, "check.jls"), readdir(dir))
        t, Gτs = deserialize(dir*f)
        println("testing $f")
        @test isequal(check_sens(t), Gτs);
    end
end;

@testset "Evaluating" begin
    include("../src/typecheck.jl")
    include("../src/simplify.jl")
    dir = (@__DIR__)*"/files/"
    for f in filter(f->endswith(f, "eval.jls"), readdir(dir))
        Gτ, res = deserialize(dir*f)
        println("testing $f")
        @test isequal(evaluateConstraints(Gτ...), res);
    end
end;

@testset "Simplifying" begin
    include("../src/typecheck.jl")
    include("../src/simplify.jl")
    dir = (@__DIR__)*"/files/"
    for f in filter(f->endswith(f, "simpl.jls"), readdir(dir))
        Gτ, res = deserialize(dir*f)
        println("testing $f")
        @test isequal(simplifyConstraints_LoseGenerality(Gτ...), res);
    end
end;
