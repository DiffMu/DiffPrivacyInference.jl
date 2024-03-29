module DiffPrivacyInference

using CodeTracking
using Distributions
using Random
using LinearAlgebra
using Flux
using Zygote

include("builtins.jl")
include("haskell_interface.jl")

greet() = print("Hello World!")

export Norm, L1, L2, LInf, U

export gaussian_mechanism!, laplacian_mechanism!, gaussian_mechanism, laplacian_mechanism, exponential_mechanism, clip!, subtract_gradient!, scale_gradient!, norm_convert!, sample, sum_gradients, zero_gradient, above_threshold, clone, clip, unbox, map_rows, map_cols, row_to_vec, vec_to_row, reduce_cols, fold, map_cols_binary, map_rows_binary, parallel_private_fold_rows
export internal_expect_const, new_box, get_box, map_box!, discrete, undisc, undisc_container, undisc_container!
export Priv, Static, BlackBox, PrivacyFunction, Data, MetricMatrix, MetricVector, MetricGradient

export typecheck_from_string, typecheck_from_string_detailed, typecheck_from_string_debug, test_hs, test_single_hs, test_expr_parser, typecheck_from_file, typecheck_from_file_detailed, typecheck_from_file_debug

export DMModel, DMGrads

end # module
