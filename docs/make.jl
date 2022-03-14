
push!(LOAD_PATH,"../src/")

using Documenter, DiffPrivacyInference

makedocs(sitename="DiffPrivacyInference",
         pages = [
             "index.md",
             "Documentation" => [
                 "docs/builtins.md"
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


