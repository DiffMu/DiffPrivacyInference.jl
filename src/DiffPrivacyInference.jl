module DiffPrivacyInference

using CodeTracking
using MLStyle
using Distributions

include("core/DMIR.jl")
include("core/builtins.jl")

include("parsing/sanitize.jl")
include("parsing/parse.jl")

include("ffi/haskell_interface.jl")

greet() = print("Hello World!")

#export NotInScope, ArithmeticsError, WrongNoOfArgs, WrongArgType, NotNumeric, NoChoiceFound, NotSubtype, NotSupremum, UnificationError, NotInScope

export DMTerm, sng , var , arg , op , phi , ret , lam , lam_star , dphi , apply , iter , flet , abstr
export tup , tlet , loop , slet , index , len , chce, gauss, mcreate, dmclip

#export DMType, DMInt, DMReal, Constant, DMTyp, TVar, Arr, ArrStar, DMMatrix, DMTup

export L1, L2, L∞, U

export gaussian_mechanism, clip

export string_to_dmterm, file_to_dmterm, evaluate, Priv, NoData
#export infer_sensitivity, infer_sensitivity_from_string, infer_sensitivity_from_file, Priv
export pretty_print

export typecheck_hs_from_dmterm, test_hs, test_expr_parser

end # module
