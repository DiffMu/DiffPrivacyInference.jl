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

include("utils/exposed.jl")

greet() = print("Hello World!")

export DMTerm, sng , var , arg , op , phi , ret , lam , lam_star , dphi , apply , iter , flet , abstr
export tup , tlet , loop , slet , vcreate , vect , index , len , chce

export DMType, DMInt, DMReal, Constant, DMTyp, DMVec, TVar, Arr, ForAll

export infer_sensitivity

end # module