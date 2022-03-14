
push!(LOAD_PATH,"../src/")

using Documenter, DiffPrivacyInference

makedocs(sitename="DiffPrivacyInference",
         pages = [
             "index.md",
             "Getting Started" => [
                 "getting_started/installation.md"
             ],
             "Tutorial" => [
                 "tutorial/01_sensitivity_functions.md",
                 "tutorial/02_privacy_functions.md"
             ],
             "Full Reference" => [
                 "full_reference/builtins.md"
                 # "reference/public.md",
                 # "reference/core.md",
                 # "reference/parsing.md",
                 # "reference/typechecking.md",
             ]
         ]
)

deploydocs(
    repo = "github.com/DiffMu/DiffPrivacyInference.jl.git",
    devbranch = "main",
)


