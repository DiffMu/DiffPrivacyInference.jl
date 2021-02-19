
using Documenter, DiffPrivacyInference

makedocs(sitename="DiffPrivacyInference",
         pages = [
             "index.md",
             "Documentation" => [
                 "reference/public.md",
                 "reference/core.md",
                 "reference/parsing.md",
                 "reference/typechecking.md",
             ]
         ]
)

deploydocs(
    repo = "github.com/DiffMu/DiffPrivacyInference.jl.git",
    devbranch = "main",
)


