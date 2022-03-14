var documenterSearchIndex = {"docs":
[{"location":"tutorial/02_privacy_functions/#Privacy-functions","page":"Privacy functions","title":"Privacy functions","text":"","category":"section"},{"location":"full_reference/types/#Types","page":"Types","title":"Types","text":"","category":"section"},{"location":"full_reference/types/","page":"Types","title":"Types","text":"DP type Julia type\nData {Real,Int}\nReal Real\nmathbbN Int\nVector[nxm]{A} Vector{A}","category":"page"},{"location":"getting_started/installation/#Installation","page":"Installation","title":"Installation","text":"","category":"section"},{"location":"getting_started/installation/#Using-the-julia-package-manager","page":"Installation","title":"Using the julia package manager","text":"","category":"section"},{"location":"getting_started/installation/","page":"Installation","title":"Installation","text":"This is currently not possible. For now, see the next section.","category":"page"},{"location":"getting_started/installation/#From-source","page":"Installation","title":"From source","text":"","category":"section"},{"location":"getting_started/installation/#Dependencies","page":"Installation","title":"Dependencies","text":"","category":"section"},{"location":"getting_started/installation/","page":"Installation","title":"Installation","text":"This project uses both Julia and Haskell, as such, you need to have both languages installed. In particular, in order to run/build from source, you need:","category":"page"},{"location":"getting_started/installation/","page":"Installation","title":"Installation","text":"Julia, a relatively recent version, e.g. >= 1.6.1\nHaskell Tool Stack version >= 1.6.0\nGNU Make","category":"page"},{"location":"getting_started/installation/#Getting-the-source-and-building","page":"Installation","title":"Getting the source and building","text":"","category":"section"},{"location":"getting_started/installation/","page":"Installation","title":"Installation","text":"Clone this repository, as well as the julia frontend. (They do not have to be cloned into the same directory)\n~ $ git clone https://github.com/DiffMu/DiffPrivacyInferenceHs\n~ $ git clone https://github.com/DiffMu/DiffPrivacyInference.jl\nBuild the haskell project.\n~/DiffPrivacyInferenceHs $ make install\nNOTE: The makefile is a small wrapper which calls stack build, and then copies the built library libdiffmu-wrapper to the location given at the top of the makefile, LIB_INSTALL_DIR = $${HOME}/.local/lib. This is the location where the julia frontend expects to find the library, but by updating it in both places (makefile and in DiffPrivacyInference.jl/src/haskell_interface.jl) it can be changed.\nRegister DiffPrivacyInference.jl as a local package by navigating into the directory you cloned the julia frontend repo into and launching the julia REPL. There, first activate the package by entering\n] activate .\nThen install all dependencies:\n] instantiate\nStill in the julia REPL, load the project with\njulia> using DiffPrivacyInference","category":"page"},{"location":"getting_started/installation/#Usage","page":"Installation","title":"Usage","text":"","category":"section"},{"location":"getting_started/installation/","page":"Installation","title":"Installation","text":"To parse a string and then typecheck it using the haskell backend, do\n```julia\njulia> term = string_to_dmterm(\"function my_identity(a)\n                                  return a\n                                end\")\n\njulia> typecheck_hs_from_dmterm(term)\n```\nTo execute all (haskell-)tests, simply run\n```julia\njulia> test_hs()\n```","category":"page"},{"location":"getting_started/installation/#Tips-and-Tricks","page":"Installation","title":"Tips & Tricks","text":"","category":"section"},{"location":"getting_started/installation/","page":"Installation","title":"Installation","text":"You may want to use [`Revise.jl`]() so you don't have to restart the REPL everytime you change the code. If you put\n```\nusing Revise\n```\nin your `~/.julia/config/startup.jl` (or wherever you keep your julia config), you won't have to type it on every REPL restart.","category":"page"},{"location":"reference/typechecking/#Typechecking","page":"Typechecking","title":"Typechecking","text":"","category":"section"},{"location":"reference/typechecking/","page":"Typechecking","title":"Typechecking","text":"Modules = [DiffPrivacyInference]\nPages = [\"typechecking/subtyping.jl\", \n        , \"typechecking/monadic_simplify.jl\"\n        , \"typechecking/monadic_typecheck.jl\"\n        , \"typechecking/lose_generality.jl\"]","category":"page"},{"location":"reference/typechecking/#DiffPrivacyInference.typecheck_from_file-Tuple{AbstractString}","page":"Typechecking","title":"DiffPrivacyInference.typecheck_from_file","text":"typecheckfromfile(file::AbstractString)\n\nTypecheck the file named file, calling the haskell bcakend. Includes are resolved and parsed as well. The typechecking result will be printed to the REPL. It will be the inferred type of the last statement in the file.\n\n\n\n\n\n","category":"method"},{"location":"full_reference/annotations/#Annotations","page":"Annotations","title":"Annotations","text":"","category":"section"},{"location":"tutorial/01_sensitivity_functions/#Sensitivity-functions","page":"Sensitivity functions","title":"Sensitivity functions","text":"","category":"section"},{"location":"reference/core/#Core","page":"Core","title":"Core","text":"","category":"section"},{"location":"reference/core/","page":"Core","title":"Core","text":"Modules = [DiffPrivacyInference]\nPages = [\"core/definitions.jl\"\n        , \"core/DMIR.jl\"\n        , \"core/operations.jl\"\n        , \"core/substitutions.jl\"\n        , \"core/unification.jl\"\n        , \"core/contexts.jl\"\n        , \"core/monads.jl\"]","category":"page"},{"location":"full_reference/mutating_functions/#Mutating-functions","page":"Mutating functions","title":"Mutating functions","text":"","category":"section"},{"location":"full_reference/builtins/#Builtins","page":"Builtins","title":"Builtins","text":"","category":"section"},{"location":"full_reference/builtins/","page":"Builtins","title":"Builtins","text":"Here is some text.","category":"page"},{"location":"full_reference/builtins/","page":"Builtins","title":"Builtins","text":"Modules = [DiffPrivacyInference]\nPages = [\"builtins.jl\"]","category":"page"},{"location":"full_reference/builtins/#DiffPrivacyInference.DMGrads","page":"Builtins","title":"DiffPrivacyInference.DMGrads","text":"A wrapper for Zygote.Grads, so we can control that only typecheckable operations are executed on the gradient.\n\nExamples\n\nA black-box function computing the gradient of some DMModel, given a loss function loss:\n\nfunction unbounded_gradient(model::DMModel, d::Vector, l) :: BlackBox()\n   gs = Flux.gradient(Flux.params(model.model)) do\n           loss(d,l,model)\n        end\n   return DMGrads(gs)\nend\n\n\n\n\n\n","category":"type"},{"location":"full_reference/builtins/#DiffPrivacyInference.DMModel","page":"Builtins","title":"DiffPrivacyInference.DMModel","text":"A wrapper for Flux models, so we can control that only typecheckable operations are executed on the model. What you put inside this wrapper needs to at least support calling Flux.params on it.\n\nExamples\n\nIntialize a Flux neural network:\n\n DMModel(Flux.Chain(\n         Flux.Dense(28*28,40, Flux.relu),\n         Flux.Dense(40, 10),\n         Flux.softmax))\n\nNote that construction of models cannot be typechecked and needs to happen inside black-box functions that return the model. So a typecheckable function could look like this:\n\nfunction init_model() :: BlackBox()\n   DMModel(Flux.Chain(\n           Flux.Dense(28*28,40, Flux.relu),\n           Flux.Dense(40, 10),\n           Flux.softmax))\nend\n\n\n\n\n\n","category":"type"},{"location":"full_reference/builtins/#DiffPrivacyInference.PrivacyFunction","page":"Builtins","title":"DiffPrivacyInference.PrivacyFunction","text":"Annotation for variables of a function that are privacy functions themselves. You have to annotate privacy function function arguments, otherwise typechecking will assume a non-private function and fail if you insert a privacy function.\n\n\n\n\n\n","category":"type"},{"location":"full_reference/builtins/#DiffPrivacyInference.BlackBox-Tuple{}","page":"Builtins","title":"DiffPrivacyInference.BlackBox","text":"Annotation for functions that cannot be typechecked. Their arguments will be assigned infinite sensitivity. Note that it is not allowed to mutate any of the arguments in a function like this, if you do the typechecking result will be invalid!\n\nExamples\n\nA function calling an imported qualified name, which is not permissible in non-black-boxes:\n\nloss(X, y, m::DMModel) :: BlackBox() = Flux.crossentropy(m.model(X), y)\n\n\n\n\n\n","category":"method"},{"location":"full_reference/builtins/#DiffPrivacyInference.NoData-Tuple{}","page":"Builtins","title":"DiffPrivacyInference.NoData","text":"Annotation for function arguments whose privacy is of no interest to us. Their privacy will most likely be set to infinity to allow tighter bounds on other arguments.\n\nExamples\n\nA privacy function with argument x whose privacy will be inferred and argument y of type Integer whose privacy we're not interested in:\n\nfunction foo(x, y::NoData(Integer)) :: Priv()\n   x\nend\n\n\n\n\n\n","category":"method"},{"location":"full_reference/builtins/#DiffPrivacyInference.Priv-Tuple{}","page":"Builtins","title":"DiffPrivacyInference.Priv","text":"Annotation for functions whose differential privacy we want to infer.\n\nExamples\n\nA privacy function with argument x whose privacy will be inferred and argument y of type Integer whose privacy we're not interested in:\n\nfunction foo(x, y::NoData(Integer)) :: Priv()\n   x\nend\n\n\n\n\n\n","category":"method"},{"location":"full_reference/builtins/#DiffPrivacyInference.above_threshold-Tuple{Vector{F} where F<:Function, Real, Any, Number}","page":"Builtins","title":"DiffPrivacyInference.above_threshold","text":"above_threshold(queries :: Vector{Function}, epsilon :: Real, d, T :: Number) :: Integeri\n\nThe above-threshold mechanism. Input is a vector of 1-sensitive queries on dataset d mapping to the reals. Returns the index of the first query whose result at d plus (4/epsilon)-Laplacian noise is above the given threshold T plus (2/epsilon)-Laplacian noise. This is (epsilon,0)-private in d!\n\n\n\n\n\n","category":"method"},{"location":"full_reference/builtins/#DiffPrivacyInference.clip!-Tuple{DiffPrivacyInference.Norm, DMGrads}","page":"Builtins","title":"DiffPrivacyInference.clip!","text":"clip!(l::Norm, g::DMGrads) :: Tuple{}\n\nClip the gradient, i.e. scale by 1/norm(g) if norm(g) > 1. Mutates the gradient, returns ().\n\n\n\n\n\n","category":"method"},{"location":"full_reference/builtins/#DiffPrivacyInference.clip-Tuple{DiffPrivacyInference.Norm, AbstractVector}","page":"Builtins","title":"DiffPrivacyInference.clip","text":"clip(l::Norm, g::AbstractVector)\n\nReturn a clipped copy of the input vector, i.e. scale by 1/norm(g) if norm(g) > 1.\n\n\n\n\n\n","category":"method"},{"location":"full_reference/builtins/#DiffPrivacyInference.clip-Union{Tuple{T}, Tuple{T, T, T}} where T<:Number","page":"Builtins","title":"DiffPrivacyInference.clip","text":"clip(v::T, upper::T, lower::T) where T <: Number\n\nClip the number v, i.e. return v if it is in [lower,upper], return upper if v is larger than upper, and return lower if v is smaller than lower.\n\n\n\n\n\n","category":"method"},{"location":"full_reference/builtins/#DiffPrivacyInference.clone-Tuple{DMGrads}","page":"Builtins","title":"DiffPrivacyInference.clone","text":"clone(g::DMGrads)\n\nCreate and return a copy of a DMGrads object, where only the gradient part of the Zygote gradient is copied while the part pointing to the parameters of a model is kept. Thus we get an object that we can mutate safely while retaining information on which entry of the gradient belongs to which parameter of which model. If you want to return a DMGrads object from a function, you have to return a copy.\n\nExamples\n\nA function returning a copy of the gradient object:\n\nfunction compute_and_scale_gradient(model::DMModel, d, l) :: BlackBox()\n   gs = unbounded_gradient(model, d, l)\n   scale_gradient!(100, gs)\n   return clone(gs)\nend\n\n\n\n\n\n","category":"method"},{"location":"full_reference/builtins/#DiffPrivacyInference.exponential_mechanism-NTuple{4, Any}","page":"Builtins","title":"DiffPrivacyInference.exponential_mechanism","text":"exponential_mechanism(r::Number, eps::Number, xs::Vector, u::Function)\n\nReturn an element of the input vector xs based on the score given by the function u, mapping from the elements of xs to a real number. The probability for element e to be chosen is proportional to exp(eps*u(e)/(2*r)). The mechanism is (eps,0)-private in the variables that u is r-sensitive in.\n\n\n\n\n\n","category":"method"},{"location":"full_reference/builtins/#DiffPrivacyInference.gaussian_mechanism!-Tuple{Real, Real, Real, DMGrads}","page":"Builtins","title":"DiffPrivacyInference.gaussian_mechanism!","text":"gaussian_mechanism!(s::Real, ϵ::Real, δ::Real, g::DMGrads) :: Tuple{}\n\nApply the gaussian mechanism to the input gradient, adding gaussian noise with SD of (2 * log(1.25/δ) * s^2) / ϵ^2) to each gradient entry seperately. This introduces (ϵ, δ)-differential privacy to all variables the gradient depends on with sensitivity at most s. Mutates the gradient, returns ().\n\n\n\n\n\n","category":"method"},{"location":"full_reference/builtins/#DiffPrivacyInference.gaussian_mechanism-Tuple{Real, Real, Real, Any}","page":"Builtins","title":"DiffPrivacyInference.gaussian_mechanism","text":"gaussian_mechanism(s::Real, ϵ::Real, δ::Real, g)\n\nApply the gaussian mechanism to the input, adding gaussian noise with SD of (2 * log(1.25/δ) * s^2) / ϵ^2). This introduces (ϵ, δ)-differential privacy to all variables the input depends on with sensitivity at most s. Makes a copy of the input and returns the noised copy.\n\n\n\n\n\n","category":"method"},{"location":"full_reference/builtins/#DiffPrivacyInference.laplacian_mechanism!-Tuple{Real, Real, DMGrads}","page":"Builtins","title":"DiffPrivacyInference.laplacian_mechanism!","text":"laplacian_mechanism!(s::Real, ϵ::Real, g::DMGrads) :: Tuple{}\n\nApply the laplacian mechanism to the input, adding laplacian noise with scaling parameter of (s / ϵ) and location zero to each gradient entry seperately. This introduces (ϵ, 0)-differential privacy to all variables the input depends on with sensitivity at most s. Mutates the input, returns ().\n\n\n\n\n\n","category":"method"},{"location":"full_reference/builtins/#DiffPrivacyInference.laplacian_mechanism-Tuple{Real, Real, Any}","page":"Builtins","title":"DiffPrivacyInference.laplacian_mechanism","text":"laplacian_mechanism(s::Real, ϵ::Real, g)\n\nApply the laplacian mechanism to the input, adding laplacian noise with scaling parameter of (s / ϵ) and location zero to each gradient entry seperately. This introduces (ϵ, 0)-differential privacy to all variables the input depends on with sensitivity at most s. Makes a copy of the input, then noises and returns the copy.\n\n\n\n\n\n","category":"method"},{"location":"full_reference/builtins/#DiffPrivacyInference.map_cols-Tuple{Function, AbstractMatrix}","page":"Builtins","title":"DiffPrivacyInference.map_cols","text":"map_cols(f::Function, m::AbstractMatrix)\n\nMap the Vector-to-Vector-function f to the columns of m. \n\n\n\n\n\n","category":"method"},{"location":"full_reference/builtins/#DiffPrivacyInference.map_cols_binary-Tuple{Function, AbstractMatrix, AbstractMatrix}","page":"Builtins","title":"DiffPrivacyInference.map_cols_binary","text":"map_cols_binary(f::Function, m::AbstractMatrix)\n\nMap the binary Vector-to-Vector-function f to the columns of m and n. \n\n\n\n\n\n","category":"method"},{"location":"full_reference/builtins/#DiffPrivacyInference.map_rows-Tuple{Function, AbstractMatrix}","page":"Builtins","title":"DiffPrivacyInference.map_rows","text":"map_rows(f::Function, m::AbstractMatrix)\n\nMap the Vector-to-Vector function f to the rows of m. \n\n\n\n\n\n","category":"method"},{"location":"full_reference/builtins/#DiffPrivacyInference.norm_convert!-Tuple{Any}","page":"Builtins","title":"DiffPrivacyInference.norm_convert!","text":"norm_convert!(m::T) :: T\n\nMake a clipped vector/gradient measured using the discrete norm into a vector/gradient measured with the clipping norm instead. Does not change the value of the argument. It can be used to enable using a gradient obtained from a black box computation (hence being in discrete-norm land) to be put into e.g. the gaussian mechanism (which expects the input to be in L2-norm land).\n\n\n\n\n\n","category":"method"},{"location":"full_reference/builtins/#DiffPrivacyInference.reduce_cols-Tuple{Function, AbstractMatrix}","page":"Builtins","title":"DiffPrivacyInference.reduce_cols","text":"reduce_cols(f::Function, m::AbstractMatrix)\n\nApply the privacy function f to each column of the matrix m, return a vector of the results. \n\n\n\n\n\n","category":"method"},{"location":"full_reference/builtins/#DiffPrivacyInference.sample-Tuple{Integer, AbstractMatrix, AbstractMatrix}","page":"Builtins","title":"DiffPrivacyInference.sample","text":"sample(n::Integer, m::AbstractMatrix, v::AbstractMatrix) :: Tuple\n\nTake a uniform sample (with replacement) of n rows of the matrix m and corresponding rows of matrix v.\n\n\n\n\n\n","category":"method"},{"location":"full_reference/builtins/#DiffPrivacyInference.scale_gradient!-Tuple{Number, DMGrads}","page":"Builtins","title":"DiffPrivacyInference.scale_gradient!","text":"scale_gradient!(s::Number, gs::DMGrads) :: Tuple{}\n\nScale the gradient represented by the Zygote.Grads struct wrapped in the input DMGrads gs by the scalar s. Mutates the gradient, returs ().\n\n\n\n\n\n","category":"method"},{"location":"full_reference/builtins/#DiffPrivacyInference.subtract_gradient!-Tuple{DMModel, DMGrads}","page":"Builtins","title":"DiffPrivacyInference.subtract_gradient!","text":"subtract_gradient!(m::DMModel, gs::DMGrads) :: Tuple{}\n\nSubtract the gradient represented by the Zygote.Grads struct wrapped in the input DMGrads gs from the parameters of the model m. Mutates the model, returns ().\n\n\n\n\n\n","category":"method"},{"location":"full_reference/builtins/#DiffPrivacyInference.sum_gradients-Tuple{DMGrads, Vararg{DMGrads}}","page":"Builtins","title":"DiffPrivacyInference.sum_gradients","text":"sum_gradients(g::DMGrads, gs::DMGrads...) :: DMGrads\n\nSum two or more DMGrads gradients. Errors if they belong to different DMModels.\n\n\n\n\n\n","category":"method"},{"location":"full_reference/builtins/#DiffPrivacyInference.zero_gradient-Tuple{DMModel}","page":"Builtins","title":"DiffPrivacyInference.zero_gradient","text":"zero_gradient(m::DMModel) :: DMGrads\n\nCreate a zero gradient for the given model.\n\n\n\n\n\n","category":"method"},{"location":"reference/public/#Public-interface","page":"Public interface","title":"Public interface","text":"","category":"section"},{"location":"reference/public/","page":"Public interface","title":"Public interface","text":"Modules = [DiffPrivacyInference]\nPages = [\"public/public.jl\"]","category":"page"},{"location":"reference/parsing/#Parsing","page":"Parsing","title":"Parsing","text":"","category":"section"},{"location":"reference/parsing/","page":"Parsing","title":"Parsing","text":"Modules = [DiffPrivacyInference]\nPages = [\"parsing/sanitize.jl\", \"parsing/parse.jl\"]","category":"page"},{"location":"#Overview","page":"Overview","title":"Overview","text":"","category":"section"},{"location":"","page":"Overview","title":"Overview","text":"The goal of this project is to create a type checker which can automatically analyze Julia programs with respect to differential privacy guarantees.","category":"page"},{"location":"","page":"Overview","title":"Overview","text":"This is a work in progress. We intend to implement a type inference algorithm for Julia code based on the type system described in this paper and the corresponding haskell implementation.","category":"page"},{"location":"","page":"Overview","title":"Overview","text":"Currently, we can do the following:","category":"page"},{"location":"","page":"Overview","title":"Overview","text":"Parse a very basic subset of Julia code into a representation suitable for type checking. We support arithmetics on Real and Integer types, procedural variable and function declarations and multiple dispatch.\nInfer the sensitivity w.r.t. the inputs of the functions in the parsing results. This is an important first step towards the inference of differential privacy bounds.","category":"page"},{"location":"","page":"Overview","title":"Overview","text":"Next up is adding support for more Julia language constructs and data types to the parser, so we can handle e.g. vector and matrix operations, loops and conditionals. Further, we will implement and verify some standard differentially private mechanisms and provide a convenient interface.","category":"page"},{"location":"#Installation","page":"Overview","title":"Installation","text":"","category":"section"},{"location":"","page":"Overview","title":"Overview","text":"It is advisable, for now, to avoid precompilation and optimization by starting Julia with","category":"page"},{"location":"","page":"Overview","title":"Overview","text":"julia -O0 --compile=min","category":"page"},{"location":"","page":"Overview","title":"Overview","text":"Then install the package with","category":"page"},{"location":"","page":"Overview","title":"Overview","text":"] add \"https://github.com/DiffMu/DiffPrivacyInference.jl\"","category":"page"},{"location":"","page":"Overview","title":"Overview","text":"Start using it with","category":"page"},{"location":"","page":"Overview","title":"Overview","text":"julia> using DiffPrivacyInference","category":"page"},{"location":"#Examples","page":"Overview","title":"Examples","text":"","category":"section"},{"location":"","page":"Overview","title":"Overview","text":"Using infer_sensitivity_from_string, we can parse Julia code from strings and do type inference:","category":"page"},{"location":"","page":"Overview","title":"Overview","text":"julia> pretty_print(infer_sensitivity_from_string(\"f(x::Integer) = 23*x\"))\n\"(Int @(23)) ==> Int\"","category":"page"},{"location":"","page":"Overview","title":"Overview","text":"The output tells us that the input expression is a one-argument function mapping an integer to another integer with sensitivity 23.","category":"page"},{"location":"","page":"Overview","title":"Overview","text":"Currently we can only do function and variable declaration, multiple dispatch, and basic arithmetics on real and integer numbers. Here's a more complicated example:","category":"page"},{"location":"","page":"Overview","title":"Overview","text":"julia> pretty_print(infer_sensitivity_from_string(\"\n                              function test(x::Integer, y)\n                                f(x) = 23*(x + y)\n                                z = 1\n                                g(x) = z*x\n                                z = 42/23\n                                f(g(x))\n                              end\n                     \"))\n\"(Int @(42.0), tvar.op_arg_16 @(23)) ==> tvar.ret23\"","category":"page"},{"location":"","page":"Overview","title":"Overview","text":"The output tells us that this is a two-argument function which is 42-sensitive in its first argument, which is of type Integer, and 23-sensitive in its second argument, whose type (like the function's return type) could not be inferred.","category":"page"},{"location":"","page":"Overview","title":"Overview","text":"We can analyse entire files using infer_sensitivity_from_file, also resolving includes. Running the inference algorithm like this will result in the type of the last statement in the file, i.e. of the thing that running all commands in the file would entail.","category":"page"},{"location":"","page":"Overview","title":"Overview","text":"<!– ## Implementation reference –> <!– @contents --> <!-- Pages = [\"docs/builtins.md\"] --> <!-- –>","category":"page"}]
}
