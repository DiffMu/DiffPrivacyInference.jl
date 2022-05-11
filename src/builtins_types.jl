
# A type for norms, used to specify what to clip to.
#
# Since on the julia side these are always encoded as floats anyway,
# we merely define them transparently.
const global Norm = Float64
const global L1   = 1.0
const global L2   = 2.0
const global LInf = Inf


###########################################
# Annotations

"""
    Priv() :: DataType

Annotation for functions whose differential privacy we want to infer. This method denotes the function can return any type.

# Examples
A privacy function with argument `x` whose privacy will be inferred and argument `y` of type
Integer whose privacy we're not interested in:
```julia
function foo(x, y::Static(Integer)) :: Priv()
   x
end
```
"""
Priv() = Any

"""
    Priv(T::DataType) :: DataType

Annotation for functions whose differential privacy we want to infer and that return a subtype of `T`.

# Examples
A privacy function with return type `Real` argument `x` of type `Real` whose privacy will be inferred and argument `y` of type
Integer whose privacy we're not interested in:
```julia
function foo(x::Real, y::Static(Integer)) :: Priv(Real)
   x
end
```
"""
Priv(T::DataType) = T

"""
    Static() :: DataType

Annotation for function arguments whose privacy is of no interest to us and for which we do not give type annotations.
Their privacy will most likely be set to infinity to allow tighter bounds on other arguments.

# Examples
A privacy function with argument `x` whose privacy will be inferred and argument `y` whose privacy we're not interested in:
```julia
function foo(x, y::Static()) :: Priv()
   x
end
```
"""
Static() = Any


"""
    Static(T::DataType) :: DataType

Annotation for function arguments whose privacy is of no interest to us. Argument `T` denotes the
type annotation we give for this argument.
Their privacy will most likely be set to infinity to allow tighter bounds on other arguments.

# Examples
A privacy function with argument `x` whose privacy will be inferred and argument `y` of type
Integer whose privacy we're not interested in:
```julia
function foo(x, y::Static(Integer)) :: Priv()
   x
end
```
"""
Static(T::DataType) = T
Static(T::Type) = T

"""
    BlackBox() :: DataType

Annotation for functions that cannot be typechecked. Their arguments will be assigned infinite
sensitivity. Note that it is not allowed to mutate any of the arguments in a function like this,
if you do the typechecking result will be invalid! This method allows any return type.

# Examples
A function calling an imported qualified name, which is not permissible in non-black-boxes:
```julia
loss(X, y, m::DMModel) :: BlackBox() = Flux.crossentropy(m.model(X), y)
```
"""
BlackBox() = Any

"""
    BlackBox(T::DataType) :: DataType

Annotation for functions with return type `T` that cannot be typechecked. Their arguments will be assigned infinite
sensitivity. Note that it is not allowed to mutate any of the arguments in a function like this,
if you do the typechecking result will be invalid! This method allows any return type.

# Examples
A function returning `Real` and calling an imported qualified name, which is not permissible in non-black-boxes:
```julia
loss(X, y, m::DMModel) :: BlackBox(Real) = Flux.crossentropy(m.model(X), y)
```
"""
BlackBox(T::DataType) = T


"""
Annotation for variables of a function that are privacy functions themselves. You have to
annotate privacy function function arguments, otherwise typechecking will assume a non-private
function and fail if you insert a privacy function.

# Examples
A function that applies the argument privacy function to the other argument.
```julia
function appl_priv(f::PrivacyFunction, x) :: Priv()
   f(x)
end
```
"""
PrivacyFunction = Function


"""
Annotation for real numbers with the discrete metric, i.e.
    d(a,b) = (a==b) ? 1 : 0
Use it to tell the typechecker you want to infer sensitivity/privacy of a function variable
w.r.t. to the discrete metric. An alias for julia's `Real` type, so you cannot dispatch on it.
See the documentation on [measuring distance](@ref) for more info."""
Data = Real


"""
    MetricMatrix(T, N<:Norm)

Annotate matrices with the desired metric you want them to be measured in by the typechecker.
Just maps to Matrix{T}. See the documentation on [measuring distance](@ref) for more info.

# Examples
A function with a matrix argument with specified metric and unspecified output metric:
```julia
function sum2(m::MetricMatrix(Real, L2)) :: Matrix{Real}
   m + m
end
```
"""
MetricMatrix(T, L::Norm) = Matrix{<:T}


"""
    MetricVector(T, N<:Norm)

Annotate matrices with the desired metric you want them to be measured in by the typechecker.
Just maps to Vector{T}, so you cannot dispatch on it.
See the documentation on [measuring distance](@ref) for more info.

# Examples
A function with a vector argument with specified metric and unspecified output metric:
```julia
function sum2(m::MetricVector(Real, L2)) :: Vector{Real}
   m + m
end
```
"""
MetricVector(T, L::Norm) = Vector{<:T}


"""
    MetricGradient(T, N<:Norm)

Annotate gradients with the desired metric you want them to be measured in by the typechecker.
Just maps to DMGrads, so you cannot dispatch on it. See the documentation on [measuring distance](@ref) for more info.

# Examples
A function with a gradient argument with specified metric and unspecified output metric:
```julia
function sum2(m::MetricGradient(Real, L2)) :: DMGrads
   sum_gradients(m, m)
end
```
"""
MetricGradient(T, L::Norm) = DMGrads


###########################################
# Flux wrappers

"""
A wrapper for Flux models, so we can control that only typecheckable operations are executed on the model.
What you put inside this wrapper needs to at least support calling Flux.params on it.

# Examples
Intialize a Flux neural network:
```julia
 DMModel(Flux.Chain(
         Flux.Dense(28*28,40, Flux.relu),
         Flux.Dense(40, 10),
         Flux.softmax))
```
Note that construction of models cannot be typechecked and needs to happen inside black-box
functions that return the model. So a typecheckable function could look like this:
```julia
function init_model() :: BlackBox()
   DMModel(Flux.Chain(
           Flux.Dense(28*28,40, Flux.relu),
           Flux.Dense(40, 10),
           Flux.softmax))
end
```
"""
mutable struct DMModel
   model # a flux model
end

Base.size(m::DMModel) = (sum(length, Flux.params(m.model)),)

"""
A wrapper for Zygote.Grads, so we can control that only typecheckable operations are executed on the gradient.

# Examples
A black-box function computing the gradient of some `DMModel`, given a loss function `loss`:
```julia
function unbounded_gradient(model::DMModel, d::Vector, l) :: BlackBox()
   gs = Flux.gradient(Flux.params(model.model)) do
           loss(d,l,model)
        end
   return DMGrads(gs)
end
```
"""
mutable struct DMGrads
   grads :: Zygote.Grads
end

Base.size(gs::DMGrads) = (sum(length, gs.grads.params),)
