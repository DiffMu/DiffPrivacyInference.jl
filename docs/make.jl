
push!(LOAD_PATH,"../src/")

using Documenter, DiffPrivacyInference

makedocs(sitename="DiffPrivacyInference",
         pages = [
             "index.md",
             "Getting Started" => [
                 "getting_started/installation.md",
                 "getting_started/quick_guide.md"
             ],
             "Tutorial" => [
                 "tutorial/01_sensitivity_functions.md",
                 "tutorial/02_privacy_functions.md"
             ],
             "Full Reference" => [
                 "full_reference/types.md",
                 "full_reference/annotations.md",
                 "full_reference/builtins.md",
                 "full_reference/scoping_rules.md",
                 "full_reference/mutating_functions.md"
             ],
             "Development Notes" => [
                 "development_notes/updating_haskell.md"
             ]
         ]
)

deploydocs(
    repo = "github.com/DiffMu/DiffPrivacyInference.jl.git",
    devbranch = "main",
)

