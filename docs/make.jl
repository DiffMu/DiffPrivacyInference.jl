
push!(LOAD_PATH,"../src/")

using Documenter, DiffPrivacyInference

makedocs(sitename="DiffPrivacyInference",
         modules=DiffPrivacyInference,
         pages = [
             "index.md",
             "Getting Started" => [
                 "getting_started/installation.md",
                 "getting_started/quick_guide.md"
             ],
             "Tutorial" => [
                 "tutorial/01_sensitivity_functions.md",
                 "tutorial/02_privacy_functions.md",
                 "tutorial/03_flux_dp.md",
             ],
             "User Reference" => [
                 "full_reference/overview.md",
                 "full_reference/syntax.md",
                 "full_reference/annotations.md",
                 "full_reference/builtins.md",
                 "full_reference/black_boxes.md",
                 "full_reference/demutation.md",
                 "full_reference/scoping_rules.md",
                 "full_reference/measuring_distance.md",
                 "full_reference/types.md",
                 "full_reference/constraints.md",
             ],
             "Development Notes" => [
                 "development_notes/project_structure.md",
                 "development_notes/technical_description.md",
                 "development_notes/updating_haskell.md"
             ]
         ]
)

deploydocs(
    repo = "github.com/DiffMu/DiffPrivacyInference.jl.git",
    devbranch = "main",
)


