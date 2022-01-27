module DiffPrivacyInference

using CodeTracking
using MLStyle
using Distributions
using LinearAlgebra
using Flux
using Zygote

include("builtins.jl")
include("haskell_interface.jl")

greet() = print("Hello World!")

export L1, L2, L∞, U

export gaussian_mechanism!, laplacian_mechanism!, clip!, subtract_gradient!, scale_gradient!, norm_convert!, sample, sum_gradients, zero_gradient
export internal_expect_const, new_box, get_box, map_box!
export Priv, NoData, BlackBox, PrivacyFunction

export typecheck_hs_from_string, typecheck_hs_from_string_detailed, test_hs, test_single_hs, test_expr_parser, typecheck_from_file, typecheck_from_file_detailed

export DMModel, DMGrads

end # module
