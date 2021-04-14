module DiffPrivacyInference

using SymbolicUtils
using CodeTracking
using MLStyle
using SimplePosets
using Distributions

include("utils/logging.jl")
include("utils/errors.jl")
include("utils/symbolic.jl")
include("core/definitions.jl")
include("core/builtins.jl")
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
include("typechecking/lose_generality.jl")


include("public/public.jl")

greet() = print("Hello World!")

export NotInScope, ArithmeticsError, WrongNoOfArgs, WrongArgType, NotNumeric, NoChoiceFound, NotSubtype, NotSupremum, UnificationError, NotInScope

export DMTerm, sng , var , arg , op , phi , ret , lam , lam_star , dphi , apply , iter , flet , abstr
export tup , tlet , loop , slet , index , len , chce, gauss, mcreate, dmclip

export DMType, DMInt, DMReal, Constant, DMTyp, TVar, Arr, ArrStar, DMMatrix, DMTup

export L1, L2, L∞, U

export gaussian_mechanism, clip

export string_to_dmterm, file_to_dmterm, evaluate
export infer_sensitivity, infer_sensitivity_from_string, infer_sensitivity_from_file, Priv
export pretty_print

end # module
