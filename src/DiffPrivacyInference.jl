module DiffPrivacyInference

using SymbolicUtils
using CodeTracking
using MLStyle
using SimplePosets
using Compat

include("utils/logging.jl")
include("core/definitions.jl")
include("core/DMIR.jl")
include("core/operations.jl")
include("core/substitutions.jl")
include("core/unification.jl")
include("core/contexts.jl")
include("core/monads.jl")

include("parsing/sanitize.jl")
include("parsing/parse.jl")

include("typechecking/subtyping.jl")
include("typechecking/monadic_simplify.jl")
include("typechecking/monadic_typecheck.jl")
include("typechecking/monadic_simplify.jl")


include("parsing/parse.jl")
include("typechecking/monadic_typecheck.jl")
include("typechecking/lose_generality.jl")

greet() = print("Hello World!")
#=
function infer_sensitivity(s::String)
    t = string_to_dmterm(s)
    infer_sensitivity(t)
end

function infer_sensitivity(file::AbstractString)
    t = file_to_dmterm(file)
    infer_sensitivity(t)
end

function infer_sensitivity(t::DMTerm)
    d = Dict{Symbol,Array{DMTerm,1}}()
    m = @mdo TC begin
        checkr <- mcheck_sens(t, d)
        tau <- simplify_constraints_lose_generality()
        r <- apply_subs(checkr)
        return r
    end
    (c, τ) = run(m)
    println("Function type is $τ.")
end
=#

export DMTerm, sng , var , arg , op , phi , ret , lam , lam_star , dphi , apply , iter , flet , abstr
export tup , tlet , loop , slet , vcreate , vect , index , len , chce

export DMType, DMInt, DMReal, Constant, DMTyp, DMVec, TVar, Arr, ForAll

end # module
