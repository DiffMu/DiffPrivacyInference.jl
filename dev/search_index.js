var documenterSearchIndex = {"docs":
[{"location":"tutorial/02_privacy_functions/#Privacy-functions","page":"Privacy functions","title":"Privacy functions","text":"","category":"section"},{"location":"full_reference/types/#Types","page":"Types","title":"Types","text":"","category":"section"},{"location":"full_reference/types/","page":"Types","title":"Types","text":"DP type Julia type\nData {Real,Int}\nReal Real\nmathbbN Int\nVector[nxm]{A} Vector{A}","category":"page"},{"location":"getting_started/installation/#Installation","page":"Installation","title":"Installation","text":"","category":"section"},{"location":"getting_started/installation/#Using-the-julia-package-manager","page":"Installation","title":"Using the julia package manager","text":"","category":"section"},{"location":"getting_started/installation/","page":"Installation","title":"Installation","text":"The easiest way to install this package is using the julia package manager.","category":"page"},{"location":"getting_started/installation/#Prerequisites","page":"Installation","title":"Prerequisites","text":"","category":"section"},{"location":"getting_started/installation/","page":"Installation","title":"Installation","text":"Since part of this project is written in Haskell and build with the haskell tool stack, you will also need it for installing this package. Fortunately, this is the only thing you need, as managing and installing the rest of the haskell dependencies is done by stack.","category":"page"},{"location":"getting_started/installation/","page":"Installation","title":"Installation","text":"For installing stack best follow the offical instructions.","category":"page"},{"location":"getting_started/installation/#Getting-this-package","page":"Installation","title":"Getting this package","text":"","category":"section"},{"location":"getting_started/installation/","page":"Installation","title":"Installation","text":"Simply execute the following command in the julia shell:","category":"page"},{"location":"getting_started/installation/","page":"Installation","title":"Installation","text":"] add https://github.com/DiffMu/DiffPrivacyInference.jl","category":"page"},{"location":"getting_started/installation/","page":"Installation","title":"Installation","text":"This should produce something similar to the following output, while julia installs all required dependencies:","category":"page"},{"location":"getting_started/installation/","page":"Installation","title":"Installation","text":"(my-env) pkg> add https://github.com/DiffMu/DiffPrivacyInference.jl\n    Updating git-repo `https://github.com/DiffMu/DiffPrivacyInference.jl`\n    Updating registry at `~/.julia/registries/General.toml`\n   Resolving package versions...\n    Updating `~/my-env/Project.toml`\n  [c8299d45] + DiffPrivacyInference v0.1.0 `https://github.com/DiffMu/DiffPrivacyInference.jl#main`\n    Updating `~/my-env/Manifest.toml`\n  [621f4979] + AbstractFFTs v1.1.0\n  ...\n  (lots of julia packages here)\n  ...\n  [3f19e933] + p7zip_jll\n    Building DiffPrivacyInference → `~/.julia/scratchspaces/44cfe95a-1eb2-52ea-b672-e2afdf69b78f/ced72be8f47015fe6f6ec85b815ac8d979225462/build.log`\n  Progress [>                                        ]  0/1","category":"page"},{"location":"getting_started/installation/","page":"Installation","title":"Installation","text":"This last step might take a long time, since here the haskell build (including all dependencies) happens. To get some feedback about progress, you can watch the content of the given build.log file (e.g. using tail path-to-log/build.log).","category":"page"},{"location":"getting_started/installation/","page":"Installation","title":"Installation","text":"When this is done, you can load the DiffPrivacyInference package in your julia shell:","category":"page"},{"location":"getting_started/installation/","page":"Installation","title":"Installation","text":"julia> using DiffPrivacyInference","category":"page"},{"location":"getting_started/installation/#From-source","page":"Installation","title":"From source","text":"","category":"section"},{"location":"getting_started/installation/#Dependencies","page":"Installation","title":"Dependencies","text":"","category":"section"},{"location":"getting_started/installation/","page":"Installation","title":"Installation","text":"This project uses both Julia and Haskell, as such, you need to have both languages installed. In particular, in order to run/build from source, you need:","category":"page"},{"location":"getting_started/installation/","page":"Installation","title":"Installation","text":"Julia, a relatively recent version, e.g. >= 1.6.1\nHaskell Tool Stack version >= 1.6.0\nGNU Make","category":"page"},{"location":"getting_started/installation/#Getting-the-source-and-building","page":"Installation","title":"Getting the source and building","text":"","category":"section"},{"location":"getting_started/installation/","page":"Installation","title":"Installation","text":"Clone this repository, as well as the julia frontend. (They do not have to be cloned into the same directory)\n~ $ git clone https://github.com/DiffMu/DiffPrivacyInferenceHs\n~ $ git clone https://github.com/DiffMu/DiffPrivacyInference.jl\nBuild the haskell project.\n~/DiffPrivacyInferenceHs $ make install\nNOTE: The makefile is a small wrapper which calls stack build, and then copies the built library libdiffmu-wrapper to the location given at the top of the makefile, LIB_INSTALL_DIR = $${HOME}/.local/lib. This is the location where the julia frontend expects to find the library, but by updating it in both places (makefile and in DiffPrivacyInference.jl/src/haskell_interface.jl) it can be changed.\nRegister DiffPrivacyInference.jl as a local package by navigating into the directory you cloned the julia frontend repo into and launching the julia REPL. There, first activate the package by entering\n] activate .\nThen install all dependencies:\n] instantiate\nStill in the julia REPL, load the project with\njulia> using DiffPrivacyInference","category":"page"},{"location":"getting_started/installation/#Usage","page":"Installation","title":"Usage","text":"","category":"section"},{"location":"getting_started/installation/","page":"Installation","title":"Installation","text":"To parse a string and then typecheck it using the haskell backend, do","category":"page"},{"location":"getting_started/installation/","page":"Installation","title":"Installation","text":"julia> term = string_to_dmterm(\"function my_identity(a)\n                                  return a\n                                end\")\n\njulia> typecheck_hs_from_dmterm(term)","category":"page"},{"location":"getting_started/installation/","page":"Installation","title":"Installation","text":"To execute all (haskell-)tests, simply run","category":"page"},{"location":"getting_started/installation/","page":"Installation","title":"Installation","text":"julia> test_hs()","category":"page"},{"location":"getting_started/installation/#Tips-and-Tricks","page":"Installation","title":"Tips & Tricks","text":"","category":"section"},{"location":"getting_started/installation/","page":"Installation","title":"Installation","text":"You may want to use Revise.jl so you don't have to restart the REPL everytime you change the code. If you put","category":"page"},{"location":"getting_started/installation/","page":"Installation","title":"Installation","text":"using Revise","category":"page"},{"location":"getting_started/installation/","page":"Installation","title":"Installation","text":"in your ~/.julia/config/startup.jl (or wherever you keep your julia config), you won't have to type it on every REPL restart.","category":"page"},{"location":"development_notes/updating_haskell/#Managing-the-two-repositories","page":"Managing the two repositories","title":"Managing the two repositories","text":"","category":"section"},{"location":"development_notes/updating_haskell/","page":"Managing the two repositories","title":"Managing the two repositories","text":"The actual typechecker is written in Haskell and is available here.","category":"page"},{"location":"development_notes/updating_haskell/","page":"Managing the two repositories","title":"Managing the two repositories","text":"That project is included in this one using git subtree. For future reference we describe how that is done. We follow these instructions.","category":"page"},{"location":"development_notes/updating_haskell/#Adding-the-subtree","page":"Managing the two repositories","title":"Adding the subtree","text":"","category":"section"},{"location":"development_notes/updating_haskell/","page":"Managing the two repositories","title":"Managing the two repositories","text":"NOTE This only has to be done once; and has already been done. It is written here only for completeness.","category":"page"},{"location":"development_notes/updating_haskell/","page":"Managing the two repositories","title":"Managing the two repositories","text":"Create new remote.","category":"page"},{"location":"development_notes/updating_haskell/","page":"Managing the two repositories","title":"Managing the two repositories","text":"git remote add -f DiffPrivacyInferenceHs git@github.com:DiffMu/DiffPrivacyInferenceHs.git","category":"page"},{"location":"development_notes/updating_haskell/","page":"Managing the two repositories","title":"Managing the two repositories","text":"Add the subtree.","category":"page"},{"location":"development_notes/updating_haskell/","page":"Managing the two repositories","title":"Managing the two repositories","text":"git subtree add --prefix deps/DiffPrivacyInferenceHs DiffPrivacyInferenceHs main --squash","category":"page"},{"location":"development_notes/updating_haskell/#Updating-the-typechecker-version","page":"Managing the two repositories","title":"Updating the typechecker version","text":"","category":"section"},{"location":"development_notes/updating_haskell/","page":"Managing the two repositories","title":"Managing the two repositories","text":"In order to update the included version of the typechecker to the newest commit on main over at the Haskell repository, execute the following two commands.","category":"page"},{"location":"development_notes/updating_haskell/","page":"Managing the two repositories","title":"Managing the two repositories","text":"git fetch DiffPrivacyInferenceHs main\ngit subtree pull --prefix deps/DiffPrivacyInferenceHs DiffPrivacyInferenceHs main --squash","category":"page"},{"location":"full_reference/annotations/#Annotations","page":"Annotations","title":"Annotations","text":"","category":"section"},{"location":"tutorial/01_sensitivity_functions/#Sensitivity-functions","page":"Sensitivity functions","title":"Sensitivity functions","text":"","category":"section"},{"location":"full_reference/scoping_rules/#Scoping-rules","page":"Scoping rules","title":"Scoping rules","text":"","category":"section"},{"location":"full_reference/mutating_functions/#Mutating-functions","page":"Mutating functions","title":"Mutating functions","text":"","category":"section"},{"location":"full_reference/builtins/#Builtins","page":"Builtins","title":"Builtins","text":"","category":"section"},{"location":"full_reference/builtins/","page":"Builtins","title":"Builtins","text":"Modules = [DiffPrivacyInference]\nPages = [\"builtins.jl\"]","category":"page"},{"location":"full_reference/builtins/#DiffPrivacyInference.DMGrads","page":"Builtins","title":"DiffPrivacyInference.DMGrads","text":"A wrapper for Zygote.Grads, so we can control that only typecheckable operations are executed on the gradient.\n\nExamples\n\nA black-box function computing the gradient of some DMModel, given a loss function loss:\n\nfunction unbounded_gradient(model::DMModel, d::Vector, l) :: BlackBox()\n   gs = Flux.gradient(Flux.params(model.model)) do\n           loss(d,l,model)\n        end\n   return DMGrads(gs)\nend\n\n\n\n\n\n","category":"type"},{"location":"full_reference/builtins/#DiffPrivacyInference.DMModel","page":"Builtins","title":"DiffPrivacyInference.DMModel","text":"A wrapper for Flux models, so we can control that only typecheckable operations are executed on the model. What you put inside this wrapper needs to at least support calling Flux.params on it.\n\nExamples\n\nIntialize a Flux neural network:\n\n DMModel(Flux.Chain(\n         Flux.Dense(28*28,40, Flux.relu),\n         Flux.Dense(40, 10),\n         Flux.softmax))\n\nNote that construction of models cannot be typechecked and needs to happen inside black-box functions that return the model. So a typecheckable function could look like this:\n\nfunction init_model() :: BlackBox()\n   DMModel(Flux.Chain(\n           Flux.Dense(28*28,40, Flux.relu),\n           Flux.Dense(40, 10),\n           Flux.softmax))\nend\n\n\n\n\n\n","category":"type"},{"location":"full_reference/builtins/#DiffPrivacyInference.Data","page":"Builtins","title":"DiffPrivacyInference.Data","text":"Annotation for real numbers with the discrete metric, i.e.     d(a,b) = (a==b) ? 1 : 0 Use it to tell the typechecker you want to infer sensitivity/privacy of a function variable w.r.t. to the discrete metric. An alias for julia's Real type, so you cannot dispatch on it.\n\n\n\n\n\n","category":"type"},{"location":"full_reference/builtins/#DiffPrivacyInference.PrivacyFunction","page":"Builtins","title":"DiffPrivacyInference.PrivacyFunction","text":"Annotation for variables of a function that are privacy functions themselves. You have to annotate privacy function function arguments, otherwise typechecking will assume a non-private function and fail if you insert a privacy function.\n\n\n\n\n\n","category":"type"},{"location":"full_reference/builtins/#DiffPrivacyInference.BlackBox-Tuple{}","page":"Builtins","title":"DiffPrivacyInference.BlackBox","text":"Annotation for functions that cannot be typechecked. Their arguments will be assigned infinite sensitivity. Note that it is not allowed to mutate any of the arguments in a function like this, if you do the typechecking result will be invalid!\n\nExamples\n\nA function calling an imported qualified name, which is not permissible in non-black-boxes:\n\nloss(X, y, m::DMModel) :: BlackBox() = Flux.crossentropy(m.model(X), y)\n\n\n\n\n\n","category":"method"},{"location":"full_reference/builtins/#DiffPrivacyInference.MetricGradient-Tuple{Any, DiffPrivacyInference.Norm}","page":"Builtins","title":"DiffPrivacyInference.MetricGradient","text":"MetricGradient(T, N<:Norm)\n\nAnnotate gradients with the desired metric you want them to be measured in by the typechecker. Just maps to DMGrad.\n\n\n\n\n\n","category":"method"},{"location":"full_reference/builtins/#DiffPrivacyInference.MetricMatrix-Tuple{Any, DiffPrivacyInference.Norm}","page":"Builtins","title":"DiffPrivacyInference.MetricMatrix","text":"MetricMatrix(T, N<:Norm)\n\nAnnotate matrices with the desired metric you want them to be measured in by the typechecker. Just maps to Matrix{T}.\n\n\n\n\n\n","category":"method"},{"location":"full_reference/builtins/#DiffPrivacyInference.MetricVector-Tuple{Any, DiffPrivacyInference.Norm}","page":"Builtins","title":"DiffPrivacyInference.MetricVector","text":"MetricVector(T, N<:Norm)\n\nAnnotate matrices with the desired metric you want them to be measured in by the typechecker. Just maps to Vector{T}.\n\n\n\n\n\n","category":"method"},{"location":"full_reference/builtins/#DiffPrivacyInference.Priv-Tuple{}","page":"Builtins","title":"DiffPrivacyInference.Priv","text":"Annotation for functions whose differential privacy we want to infer.\n\nExamples\n\nA privacy function with argument x whose privacy will be inferred and argument y of type Integer whose privacy we're not interested in:\n\nfunction foo(x, y::Static(Integer)) :: Priv()\n   x\nend\n\n\n\n\n\n","category":"method"},{"location":"full_reference/builtins/#DiffPrivacyInference.Static-Tuple{}","page":"Builtins","title":"DiffPrivacyInference.Static","text":"Annotation for function arguments whose privacy is of no interest to us. Their privacy will most likely be set to infinity to allow tighter bounds on other arguments.\n\nExamples\n\nA privacy function with argument x whose privacy will be inferred and argument y of type Integer whose privacy we're not interested in:\n\nfunction foo(x, y::Static(Integer)) :: Priv()\n   x\nend\n\n\n\n\n\n","category":"method"},{"location":"full_reference/builtins/#DiffPrivacyInference.above_threshold-Tuple{Vector{F} where F<:Function, Real, Any, Number}","page":"Builtins","title":"DiffPrivacyInference.above_threshold","text":"above_threshold(queries :: Vector{Function}, epsilon :: Real, d, T :: Number) :: Integeri\n\nThe above-threshold mechanism. Input is a vector of 1-sensitive queries on dataset d mapping to the reals. Returns the index of the first query whose result at d plus (4/epsilon)-Laplacian noise is above the given threshold T plus (2/epsilon)-Laplacian noise. This is (epsilon,0)-private in d!\n\n\n\n\n\n","category":"method"},{"location":"full_reference/builtins/#DiffPrivacyInference.clip!-Tuple{DiffPrivacyInference.Norm, DMGrads}","page":"Builtins","title":"DiffPrivacyInference.clip!","text":"clip!(l::Norm, g::DMGrads) :: Nothing\n\nClip the gradient, i.e. scale by 1/norm(g) if norm(g) > 1. Mutates the gradient, returns nothing.\n\n\n\n\n\n","category":"method"},{"location":"full_reference/builtins/#DiffPrivacyInference.clip-Tuple{DiffPrivacyInference.Norm, AbstractVector}","page":"Builtins","title":"DiffPrivacyInference.clip","text":"clip(l::Norm, g::AbstractVector)\n\nReturn a clipped copy of the input vector, i.e. scale by 1/norm(g) if norm(g) > 1.\n\n\n\n\n\n","category":"method"},{"location":"full_reference/builtins/#DiffPrivacyInference.clip-Tuple{DiffPrivacyInference.Norm, DMGrads}","page":"Builtins","title":"DiffPrivacyInference.clip","text":"clip(l::Norm, g::DMGrads) :: Nothing\n\nReturn a clipped copy of the gradient, i.e. scale by 1/norm(g) if norm(g) > 1.\n\n\n\n\n\n","category":"method"},{"location":"full_reference/builtins/#DiffPrivacyInference.clip-Union{Tuple{T}, Tuple{T, T, T}} where T<:Number","page":"Builtins","title":"DiffPrivacyInference.clip","text":"clip(v::T, upper::T, lower::T) where T <: Number\n\nClip the number v, i.e. return v if it is in [lower,upper], return upper if v is larger than upper, and return lower if v is smaller than lower.\n\n\n\n\n\n","category":"method"},{"location":"full_reference/builtins/#DiffPrivacyInference.clone-Tuple{DMGrads}","page":"Builtins","title":"DiffPrivacyInference.clone","text":"clone(g::DMGrads)\n\nCreate and return a copy of a DMGrads object, where only the gradient part of the Zygote gradient is copied while the part pointing to the parameters of a model is kept. Thus we get an object that we can mutate safely while retaining information on which entry of the gradient belongs to which parameter of which model. If you want to return a DMGrads object from a function, you have to return a copy.\n\nExamples\n\nA function returning a copy of the gradient object:\n\nfunction compute_and_scale_gradient(model::DMModel, d, l) :: BlackBox()\n   gs = unbounded_gradient(model, d, l)\n   scale_gradient!(100, gs)\n   return clone(gs)\nend\n\n\n\n\n\n","category":"method"},{"location":"full_reference/builtins/#DiffPrivacyInference.disc-Tuple{Real}","page":"Builtins","title":"DiffPrivacyInference.disc","text":"disc(n::Real) :: Data\n\nReturn n, but let the typechecker know that you want it to be measured in the discrete metric.\n\n\n\n\n\n","category":"method"},{"location":"full_reference/builtins/#DiffPrivacyInference.exponential_mechanism-NTuple{4, Any}","page":"Builtins","title":"DiffPrivacyInference.exponential_mechanism","text":"exponential_mechanism(r::Number, eps::Number, xs::Vector, u::Function)\n\nReturn an element of the input vector xs based on the score given by the function u, mapping from the elements of xs to a real number. The probability for element e to be chosen is proportional to exp(eps*u(e)/(2*r)). The mechanism is (eps,0)-private in the variables that u is r-sensitive in.\n\n\n\n\n\n","category":"method"},{"location":"full_reference/builtins/#DiffPrivacyInference.fold-Tuple{Function, Any, AbstractMatrix}","page":"Builtins","title":"DiffPrivacyInference.fold","text":"fold(f::Function, i, m::AbstractMatrix)\n\nFold the function f over all entries of m, using initial value i.\n\n\n\n\n\n","category":"method"},{"location":"full_reference/builtins/#DiffPrivacyInference.gaussian_mechanism!-Tuple{Real, Real, Real, DMGrads}","page":"Builtins","title":"DiffPrivacyInference.gaussian_mechanism!","text":"gaussian_mechanism!(s::Real, ϵ::Real, δ::Real, g::DMGrads) :: Nothing\n\nApply the gaussian mechanism to the input gradient, adding gaussian noise with SD of (2 * log(1.25/δ) * s^2) / ϵ^2) to each gradient entry seperately. This introduces (ϵ, δ)-differential privacy to all variables the gradient depends on with sensitivity at most s. Mutates the gradient, returns nothing.\n\n\n\n\n\n","category":"method"},{"location":"full_reference/builtins/#DiffPrivacyInference.gaussian_mechanism-Tuple{Real, Real, Real, Any}","page":"Builtins","title":"DiffPrivacyInference.gaussian_mechanism","text":"gaussian_mechanism(s::Real, ϵ::Real, δ::Real, g)\n\nApply the gaussian mechanism to the input, adding gaussian noise with SD of (2 * log(1.25/δ) * s^2) / ϵ^2). This introduces (ϵ, δ)-differential privacy to all variables the input depends on with sensitivity at most s. Makes a copy of the input and returns the noised copy.\n\n\n\n\n\n","category":"method"},{"location":"full_reference/builtins/#DiffPrivacyInference.laplacian_mechanism!-Tuple{Real, Real, DMGrads}","page":"Builtins","title":"DiffPrivacyInference.laplacian_mechanism!","text":"laplacian_mechanism!(s::Real, ϵ::Real, g::DMGrads) :: Nothing\n\nApply the laplacian mechanism to the input, adding laplacian noise with scaling parameter of (s / ϵ) and location zero to each gradient entry seperately. This introduces (ϵ, 0)-differential privacy to all variables the input depends on with sensitivity at most s. Mutates the input, returns nothing.\n\n\n\n\n\n","category":"method"},{"location":"full_reference/builtins/#DiffPrivacyInference.laplacian_mechanism-Tuple{Real, Real, Any}","page":"Builtins","title":"DiffPrivacyInference.laplacian_mechanism","text":"laplacian_mechanism(s::Real, ϵ::Real, g)\n\nApply the laplacian mechanism to the input, adding laplacian noise with scaling parameter of (s / ϵ) and location zero to each gradient entry seperately. This introduces (ϵ, 0)-differential privacy to all variables the input depends on with sensitivity at most s. Makes a copy of the input, then noises and returns the copy.\n\n\n\n\n\n","category":"method"},{"location":"full_reference/builtins/#DiffPrivacyInference.map_cols-Tuple{Function, AbstractMatrix}","page":"Builtins","title":"DiffPrivacyInference.map_cols","text":"map_cols(f::Function, m::AbstractMatrix)\n\nMap the Vector-to-Vector-function f to the columns of m. \n\n\n\n\n\n","category":"method"},{"location":"full_reference/builtins/#DiffPrivacyInference.map_cols_binary-Tuple{Function, AbstractMatrix, AbstractMatrix}","page":"Builtins","title":"DiffPrivacyInference.map_cols_binary","text":"map_cols_binary(f::Function, m::AbstractMatrix, n::AbstractMatrix)\n\nMap the binary Vector-to-Vector-function f to the columns of m and n. \n\n\n\n\n\n","category":"method"},{"location":"full_reference/builtins/#DiffPrivacyInference.map_rows-Tuple{Function, AbstractMatrix}","page":"Builtins","title":"DiffPrivacyInference.map_rows","text":"map_rows(f::Function, m::AbstractMatrix)\n\nMap the Vector-to-Vector function f to the rows of m. \n\n\n\n\n\n","category":"method"},{"location":"full_reference/builtins/#DiffPrivacyInference.map_rows_binary-Tuple{Function, AbstractMatrix, AbstractMatrix}","page":"Builtins","title":"DiffPrivacyInference.map_rows_binary","text":"map_rows_binary(f::Function, m::AbstractMatrix, n::AbstractMatrix)\n\nMap the binary Vector-to-Vector-function f to the columns of m and n. \n\n\n\n\n\n","category":"method"},{"location":"full_reference/builtins/#DiffPrivacyInference.norm_convert!-Tuple{Any}","page":"Builtins","title":"DiffPrivacyInference.norm_convert!","text":"norm_convert!(m::T) :: T\n\nMake a clipped vector/gradient measured using the discrete metric into a vector/gradient measured with the clipping norm instead. Does not change the value of the argument. It can be used to enable using a gradient obtained from a black box computation (hence being in discrete-norm land) to be put into e.g. the gaussian mechanism (which expects the input to be in L2-norm land).\n\n\n\n\n\n","category":"method"},{"location":"full_reference/builtins/#DiffPrivacyInference.norm_convert-Tuple{Any}","page":"Builtins","title":"DiffPrivacyInference.norm_convert","text":"norm_convert(m::T) :: T\n\nMake a clipped vector/gradient measured using the discrete norm into a vector/gradient measured with the clipping norm instead. Does not change the value of the argument. It can be used to enable using a gradient obtained from a black box computation (hence being in discrete-norm land) to be put into e.g. the gaussian mechanism (which expects the input to be in L2-norm land).\n\n\n\n\n\n","category":"method"},{"location":"full_reference/builtins/#DiffPrivacyInference.parallel_private_fold_rows!-Tuple{Function, Any, AbstractMatrix, AbstractMatrix}","page":"Builtins","title":"DiffPrivacyInference.parallel_private_fold_rows!","text":"parallel_private_fold_rows(f::Function, i, m::AbstractMatrix, n::AbstractMatrix)\n\nFold the privacy function f :: Vector -> Vector -> I -> I over the two input matrices' rows simultaneously. Allows for f to mutate the accumulator, returns nothing.  This is parallel composition on the rows of m and n, so if f is (eps,del)-private in it's first two arguments, the fold is (eps,del)-private in the input matrices. The input matrices are expected to be measured in the discrete norm.\n\n\n\n\n\n","category":"method"},{"location":"full_reference/builtins/#DiffPrivacyInference.parallel_private_fold_rows-Tuple{Function, Any, AbstractMatrix, AbstractMatrix}","page":"Builtins","title":"DiffPrivacyInference.parallel_private_fold_rows","text":"parallel_private_fold_rows(f::Function, i, m::AbstractMatrix, n::AbstractMatrix)\n\nFold the privacy function f :: Vector -> Vector -> I -> I over the two input matrices' rows simultaneously. This is parallel composition on the rows of m and n, so if f is (eps,del)-private in it's first two arguments, the fold is (eps,del)-private in the input matrices. The input matrices are expected to be measured in the discrete norm.\n\n\n\n\n\n","category":"method"},{"location":"full_reference/builtins/#DiffPrivacyInference.reduce_cols-Tuple{Function, AbstractMatrix}","page":"Builtins","title":"DiffPrivacyInference.reduce_cols","text":"reduce_cols(f::Function, m::AbstractMatrix)\n\nApply the privacy function f :: (r x 1)-Matrix -> T to each column of the (r x c)-Matrix m, return a vector of the results. If f is (eps,del)-private in its argument, the reduction is (r*eps, r*del)-private in m.\n\n\n\n\n\n","category":"method"},{"location":"full_reference/builtins/#DiffPrivacyInference.row_to_vec-Tuple{AbstractMatrix}","page":"Builtins","title":"DiffPrivacyInference.row_to_vec","text":"row_to_vec(m::AbstractMatrix) :: Vector\n\nMake the one-row matrix m into a vector.\n\n\n\n\n\n","category":"method"},{"location":"full_reference/builtins/#DiffPrivacyInference.sample-Tuple{Integer, AbstractMatrix, AbstractMatrix}","page":"Builtins","title":"DiffPrivacyInference.sample","text":"sample(n::Integer, m::AbstractMatrix, v::AbstractMatrix) :: Tuple\n\nTake a uniform sample (with replacement) of n rows of the matrix m and corresponding rows of matrix v.\n\n\n\n\n\n","category":"method"},{"location":"full_reference/builtins/#DiffPrivacyInference.scale_gradient!-Tuple{Number, DMGrads}","page":"Builtins","title":"DiffPrivacyInference.scale_gradient!","text":"scale_gradient!(s::Number, gs::DMGrads) :: Nothing\n\nScale the gradient represented by the Zygote.Grads struct wrapped in the input DMGrads gs by the scalar s. Mutates the gradient, returs nothing.\n\n\n\n\n\n","category":"method"},{"location":"full_reference/builtins/#DiffPrivacyInference.subtract_gradient!-Tuple{DMModel, DMGrads}","page":"Builtins","title":"DiffPrivacyInference.subtract_gradient!","text":"subtract_gradient!(m::DMModel, gs::DMGrads) :: Nothing\n\nSubtract the gradient represented by the Zygote.Grads struct wrapped in the input DMGrads gs from the parameters of the model m. Mutates the model, returns nothing.\n\n\n\n\n\n","category":"method"},{"location":"full_reference/builtins/#DiffPrivacyInference.sum_gradients-Tuple{DMGrads, Vararg{DMGrads}}","page":"Builtins","title":"DiffPrivacyInference.sum_gradients","text":"sum_gradients(g::DMGrads, gs::DMGrads...) :: DMGrads\n\nSum two or more DMGrads gradients. Errors if they belong to different DMModels.\n\n\n\n\n\n","category":"method"},{"location":"full_reference/builtins/#DiffPrivacyInference.vec_to_row-Tuple{AbstractVector}","page":"Builtins","title":"DiffPrivacyInference.vec_to_row","text":"vec_to_row(v::AbstractVector) :: Matrix\n\nMake the vector v into a one-row matrix.\n\n\n\n\n\n","category":"method"},{"location":"full_reference/builtins/#DiffPrivacyInference.zero_gradient-Tuple{DMModel}","page":"Builtins","title":"DiffPrivacyInference.zero_gradient","text":"zero_gradient(m::DMModel) :: DMGrads\n\nCreate a zero gradient for the given model.\n\n\n\n\n\n","category":"method"},{"location":"#Overview","page":"Overview","title":"Overview","text":"","category":"section"},{"location":"","page":"Overview","title":"Overview","text":"The goal of this project is to create a type checker which can automatically analyze Julia programs with respect to differential privacy guarantees.","category":"page"},{"location":"","page":"Overview","title":"Overview","text":"This is a work in progress. We are implementing a type inference algorithm for Julia code based on the Duet type system and the corresponding haskell implementation.","category":"page"},{"location":"","page":"Overview","title":"Overview","text":"On this page, you can find installation instructions as well as a quick guide and examples that should enable you to write your first typecheckable code. The reference documentation is not complete yet, you can however access documentation for all builtin functions.","category":"page"},{"location":"getting_started/quick_guide/#Quick-Guide","page":"Quick Guide","title":"Quick Guide","text":"","category":"section"},{"location":"getting_started/quick_guide/#Supported-julia-syntax","page":"Quick Guide","title":"Supported julia syntax","text":"","category":"section"},{"location":"getting_started/quick_guide/","page":"Quick Guide","title":"Quick Guide","text":"We cannot check arbitrary julia code, instead we restrict to a subset of the language which is suited for our static analysis. Here's a list of language features we support at the moment:","category":"page"},{"location":"getting_started/quick_guide/","page":"Quick Guide","title":"Quick Guide","text":"Function definitions using function, one-line definitions and anonymous functions, as well as function application.\nMultiple dispatch on Number, Integer, Real, Matrix{T}, Tuple{T} and our special types (see below). Finer types are not allowed.\nSome arithmetics on numbers, vectors and matrices, as well as indexing on matrix using m[i,:] and m[i,j] and vector indexing using v[i]\nType annotations on function variables, like in f(x::Integer) = x + x\nVariable and tuple assignments like x = 1 or (a,b,c) = t\nLoops over integer ranges, where the loop head must be of the form for i in 1:2:n.\nif, ifelse and else statements where the condition can be an integer or of the form x == y.\nimport, which will just be ignored by the type checker. You can use stuff from imported modules, but only inside black boxes (see below).\ninclude statements. The typechecker will load the included file and check it as well.\nFunctions which mutate (some) of their arguments. Special rules apply, see Mutating functions.","category":"page"},{"location":"getting_started/quick_guide/#Forbidden-things","page":"Quick Guide","title":"Forbidden things","text":"","category":"section"},{"location":"getting_started/quick_guide/","page":"Quick Guide","title":"Quick Guide","text":"There are a few things you are not allowed to do (which the typechecker will tell you if you try). Namely:","category":"page"},{"location":"getting_started/quick_guide/","page":"Quick Guide","title":"Quick Guide","text":"Your code has to be valid julia code. If it is not, do not expect the typechecker to always tell you so or produce reasonable results.\nYou cannot reassign (or mutate) variables that were declared in a different scope. For example, the following is illegal:\nfunction foo()\n   x = 10\n   function bar()\n      x = 100\n      x\n   end\n   bar()\nend\nIf you want to use a variable, you have to define it first. E.g. the following is valid julia code but illegal:\nfunction foo()\n   bar() = a\n   a = 100\n   bar()\nend\nAs long a reassignment happens in the same scope as where the variable was defined, it is allowed. For example the following is valid code:\nfunction foo()\n   x = 1\n   y = x+2\n   x = 2\n   y\nend\nFor a detailed explanation see Scoping rules.\nRecursion is not supported.\nAssignments within assignments (like x = y = 10) are forbidden. Why would you, anyways.","category":"page"},{"location":"getting_started/quick_guide/#Special-Types","page":"Quick Guide","title":"Special Types","text":"","category":"section"},{"location":"getting_started/quick_guide/","page":"Quick Guide","title":"Quick Guide","text":"We have two special types, DMModel for wrapping Flux.jl models and DMGrads for wrapping Zygote.jl gradients. If you want to typecheck code that uses an object like that, you need to wrap it in our types so we can ensure you don't do anything illegal with it. See the type documentation in the REPL and the flux_dp.jl example in test/flux_dp for usage.","category":"page"},{"location":"getting_started/quick_guide/#Special-annotations","page":"Quick Guide","title":"Special annotations","text":"","category":"section"},{"location":"getting_started/quick_guide/","page":"Quick Guide","title":"Quick Guide","text":"In general, it is a good idea to annotate all function arguments as it will help the typechecker give you an inference result that is not too pessimistic and has a minimum number of unresolved constraints. There is, however, some special annotations that you should make to get a proper result:","category":"page"},{"location":"getting_started/quick_guide/","page":"Quick Guide","title":"Quick Guide","text":"Our typechecker can infer the sensitivity or the (ε, δ)-differential privacy of function arguments. For every function you write, you have to tell the typechecker whether you expect it to be differentially private by annotating the function head using function foo(x) :: Priv(). If you don't annotate, the typechecker will assume that the function is not DP, which might worsen the inferred bounds if it's not true.\nFor differentially private functions, you can tell the typechecker which of its arguments are actually interesting. For example, when training a model to some data with some learning rate, you are interested in the privacy of the input data, not the input model. You would then write your function signature like this: function train(data, model::Static(), eta::Static(Real)). This allows the typecheker to infer tighter bounds by setting the privacy of non-interesting arguments to infinity in certain tradeoff situations.\nIf you write a function that takes a function as an argument, you have to decide whether you want that argument to be a privacy function or not, so we can do inference properly. You have to annotate the argument by :: PrivacyFunction if you want it to be a privacy function. If you don't, we assume it is not, and the typechecker will not permit putting a privacy function into that argument.\nIf you want to use a function that contains unsupported julia syntax, like using qualified names from imported modules, you can make them a black box by annotating the function head using function foo(x) :: BlackBox(). You can only define a black box on the toplevel scope of what you want to typecheck (not inside a function, e.g.). Also, black boxes cannot have multiple methods. The typechecker will ignore a black box' function body and assign infinite sensitivity to all arguments. Warning: We cannot control what you do inside a black box, but the one thing that you really should not do is mutate the arguments. If you do that, the typechecking result will be invalid even though the typechecking code terminates without complaints.","category":"page"},{"location":"getting_started/quick_guide/#Usage-examples","page":"Quick Guide","title":"Usage examples","text":"","category":"section"},{"location":"getting_started/quick_guide/","page":"Quick Guide","title":"Quick Guide","text":"To infer the sensitivity of a simple function, use typecheck_hs_from_string:","category":"page"},{"location":"getting_started/quick_guide/","page":"Quick Guide","title":"Quick Guide","text":"\njulia> typecheck_hs_from_string(\"function foo(x::Matrix{Real}, y::Matrix{Real})\n                                    2*x - y\n                                 end\")","category":"page"},{"location":"getting_started/quick_guide/","page":"Quick Guide","title":"Quick Guide","text":"The result will be printed in the REPL:","category":"page"},{"location":"getting_started/quick_guide/","page":"Quick Guide","title":"Quick Guide","text":"---------------------------------------------------------------------------\nType:\nFun([([NoFun(Matrix<n: τ_10, c: τ_8>[s_5 × s_4](Num(τ_44[--]))) @ 2.0,NoFun(Matrix<n: τ_10, c: τ_11>[s_5 × s_4](Num(τ_38[--]))) @ 1] -> NoFun(Matrix<n: τ_10, c: U>[s_5 × s_4](Num(τ_40[--])))) @ Just [Matrix{Real},Matrix{Real}]])\n---------------------------------------------------------------------------\nConstraints:\n   - top:\nconstr_25 : [final,worst,global,exact,special] IsSupremum (τ_44,τ_38) :=: τ_40\n   - others:\n[]\n()","category":"page"},{"location":"getting_started/quick_guide/","page":"Quick Guide","title":"Quick Guide","text":"It says the checked code is a function (Fun(...)) of two arguments which is 2-sensitive in its first and 1-sensitive in its second input (indeicated by the @ 2.0 annotation). The imput types both need to be matrices of matching dimensions (the variables s_5 and s_4) whose elements are of some numeric type (Num(...)). But that is not quite all, as there is more output:","category":"page"},{"location":"getting_started/quick_guide/","page":"Quick Guide","title":"Quick Guide","text":"- constraints:\n   - top:\nconstr_25 : [final,worst,global,exact,special] IsSupremum (τ_44,τ_38) :=: τ_40","category":"page"},{"location":"getting_started/quick_guide/","page":"Quick Guide","title":"Quick Guide","text":"It is the list of constraints on the type variables that occur in the result type that the typechecker could not resolve. In this case it tells us that the element type of the output matrix, τ_40, is not just any type, but the supremum of the input matrices' element types τ_44 and τ_38.","category":"page"},{"location":"getting_started/quick_guide/","page":"Quick Guide","title":"Quick Guide","text":"For a full-blown example head to the test/flux_dp folder, where you will find a differentially private implementation of a gradient descent algorithm that is capable of learning to classify handwritten numbers.","category":"page"}]
}