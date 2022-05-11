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

"""
    clone(g::DMGrads)
Create and return a copy of a DMGrads object, where only the gradient part of the Zygote
gradient is copied while the part pointing to the parameters of a model is kept. Thus we get
an object that we can mutate safely while retaining information on which entry of the gradient
belongs to which parameter of which model. If you want to return a `DMGrads` object from a function,
you have to return a copy.

# Examples
A function returning a copy of the gradient object:
```julia
function compute_and_scale_gradient(model::DMModel, d, l) :: BlackBox()
   gs = unbounded_gradient(model, d, l)
   scale_gradient!(100, gs)
   return clone(gs)
end
```
"""
clone(g::DMGrads) :: DMGrads = DMGrads(Zygote.Grads(IdDict(g.grads.grads), g.grads.params))
clone(g::AbstractVecOrMat) = deepcopy(g)



"""
    unbox(x, T)

Annotate a value that results from a call to a [black box function](@ref black-boxes)
with the return container type `T`. Every call to black box functions needs to be
wrapped in an `unbox` statement. If the returned type does not match the annotation,
a runtime error will be raised.

# Examples
```julia
loss(X, y) :: BlackBox(Real) = Flux.crossentropy(X, y)
function compute_loss(X,y)
   l = unbox(loss(X,y), Real)
   l
end
```
"""
unbox(x, t) = error("Cannot unbox value of type $t, please consult the documentation of black box functions for help.")
unbox(x::T where T<:Real, ::Type{Real}) = !(x isa Integer) ? x : error("Unbox encountered Integer where Real was expected.")
unbox(x::T where T<:Integer, ::Type{Integer}) = x

"""
    unbox(x, T, s)

Annotate a value that results from a call to a [black box function](@ref black-boxes)
with the return container type `T` and size `s`. Every call to black box functions needs to be
wrapped in an `unbox` statement. If the returned type does not match the annotation,
a runtime error will be raised.

# Examples
```julia
product(x, y) :: BlackBox() = x * y'
function compute_product(x,y)
   dx = length(x)
   dy = length(y)
   l = unbox(product(x,y), Matrix{<:Real}, (dx,dy))
   l
end
```
"""
unbox(x, t, s) = error("Cannot unbox value of type $t, please consult the documentation of black box functions for help.")
unbox(x::DMModel, ::Type{DMModel}, l) = unbox_size(x, (l,))
unbox(x::DMGrads, ::Type{DMGrads}, l) = unbox_size(x, (l,))
unbox(x::T where T<:Vector{<:Real}, ::Type{Vector{<:Real}}, l) = !(x isa Vector{<:Integer}) ? unbox_size(x,(l,)) : error("Unbox encountered Integer vector where Real vector was expected.")
unbox(x::T where T<:Vector{<:Integer}, ::Type{Vector{<:Integer}}, l) = unbox_size(x,(l,))
unbox(x::T where T<:Matrix{<:Real}, ::Type{Matrix{<:Real}}, s) = !(x isa Matrix{<:Integer}) ? unbox_size(x,s) : error("Unbox encountered Integer Matrix where Real Matrix was expected.")
unbox(x::T where T<:Matrix{<:Integer}, ::Type{Matrix{<:Integer}}, s) = unbox_size(x,s)

unbox_size(x, s::Tuple) = (size(x) == s) ? x : error("Unbox expected size $s but got $(size(x))")



"""
   undisc_container!(m::T) :: T

Make a clipped vector/gradient measured using the discrete metric into a vector/gradient measured with the
clipping norm instead. Does not change the value of the argument. It can be used to enable using a gradient
obtained from a black box computation (hence being in discrete-norm land) to be put into e.g. the gaussian
mechanism (which expects the input to be in L2-norm land).
See the documentation on [measuring distance](@ref) for more info.

# Example
Clip and noise a gradient, mutating the input.
```julia
function noise_grad!(g::MetricGradient(Data, LInf), eps, del) :: Priv()
    clip!(L2,g)
    undisc_container!(g)
    gaussian_mechanism!(2, eps, del, g)
    return
end
```
"""
undisc_container!(m) = m


"""
   undisc_container(m::T) :: T

Make a clipped vector/gradient measured using the discrete norm into a vector/gradient measured with the
clipping norm instead. Does not change the value of the argument. It can be used to enable using a gradient
obtained from a black box computation (hence being in discrete-norm land) to be put into e.g. the gaussian
mechanism (which expects the input to be in L2-norm land).
See the documentation on [measuring distance](@ref) for more info.

# Example
Clip and noise a gradient, not mutating the input.
```julia
function noise_grad(g::MetricGradient(Data, LInf), eps, del) :: Priv()
      cg = clip(L2,g)
      ug = undisc_container(cg)
      gaussian_mechanism(2, eps, del, ug)
end
```
"""
undisc_container(m) = clone(m)


"""
    discrete(n::Real) :: Data

Return `n`, but let the typechecker know that you want it to be measured in the discrete metric.
See the documentation on [measuring distance](@ref) for more info.
"""
discrete(n::Real) = float(n)

"""
    undisc(n::Data) :: Real

Return `n`, but let the typechecker know that you want it to be measured in the standard real metric.
See the documentation on [measuring distance](@ref) for more info.
"""
undisc(n::Data) = float(n)


"""
    norm_convert!(n::Norm, m)

Tell the typechecker to measure a matrix with a different norm `n`.
See the documentation on [measuring distance](@ref) for more info.

# Examples
Use `norm_convert` to measure the matrix in L1 norm instead of L2 norm. Mutates `m`
```julia
function foo!(m::MetricMatrix(Real, L2))
    norm_convert!(L1, m)
    return
end
```
The assigned type is:
```julia
{
|   - Matrix<n: L2, c: C>[s₂ × n]{τ₂₁}
|       @ √(n)
|   --------------------------
|    -> Matrix<n: L1, c: C>[s₂ × n]{τ₂₁}
}
```
You can see that we paid a sensitivity penalty of √n where n is the number of rows of `m`.
"""


norm_convert!(n::Norm,m) = m


"""
    norm_convert(n::Norm, m)

Return a copy of `m`, but tell the typechecker to measure a matrix with a different norm `n`.
See the documentation on [measuring distance](@ref) for more info.

# Examples
Use `norm_convert` to measure the matrix in L1 norm instead of L2 norm.
```julia
function foo(m::MetricMatrix(Real, L2))
    norm_convert(L1, m)
end
```
The assigned type is:
```julia
{
|   - Matrix<n: L2, c: C>[s₂ × n]{τ₂₁}
|       @ √(n)
|   --------------------------
|    -> Matrix<n: L1, c: C>[s₂ × n]{τ₂₁}
}
```
You can see that we paid a sensitivity penalty of √n where n is the number of rows of `m`.
"""
norm_convert(n::Norm,m) = clone(m)

###########################################
# custom samplers
# naive implementations have floating-point related vulnerabilities, we implement the sampling procedure
# presented in the following paper to mitigate some of them.
# Secure Random Sampling in Differential Privacy
# NAOISE HOLOHAN and STEFANO BRAGHIN 2021

struct SecureGaussSampler <: Sampleable{Univariate,Continuous}
   s :: Real
   m :: Real
end

function Base.rand(_::AbstractRNG, smp::SecureGaussSampler)
   CSRNG = RandomDevice()
   n = 6
   g = sum(rand(CSRNG, Normal(0,1)) for _ in 1:2*n) / sqrt(2*n)
   return smp.m*g + smp.s
end

struct SecureLaplaceSampler <: Sampleable{Univariate,Continuous}
   b :: Real
   m :: Real
end

function Base.rand(_::AbstractRNG, smp::SecureLaplaceSampler)
   sgs = SecureGaussSampler(0,1)
   l = rand(sgs) * rand(sgs) + rand(sgs) * rand(sgs)
   return smp.m * l + smp.b
end


###########################################
# private mechanisms


"""
    gaussian_mechanism(s::Real, ϵ::Real, δ::Real, g)

Apply the gaussian mechanism to the input, adding gaussian noise with SD of
`(2 * log(1.25/δ) * s^2) / ϵ^2)`. This introduces
`(ϵ, δ)`-differential privacy to all variables the input depends on with sensitivity
at most `s`. Makes a copy of the input and returns the noised copy.

The implementation follows the 2021 paper `Secure Random Sampling in Differential Privacy` by
NAOISE HOLOHAN and STEFANO BRAGHIN. It mitigates some floating point related vulnerabilities,
but not all the known ones.

# Example
Clip and noise a gradient, not mutating the input.
```julia
function noise_grad(g::MetricGradient(Data, LInf), eps, del) :: Priv()
      cg = clip(L2,g)
      ug = undisc_container(cg)
      gaussian_mechanism(2, eps, del, ug)
end
```
See the [flux-dp example](@ref fluxdp) for a full-blown implementation of private gradient
descent using this mechanism.
"""
gaussian_mechanism(s::Real, ϵ::Real, δ::Real, cf) = additive_noise(SecureGaussSampler(0, (2 * log(1.25/0.1) * 2/500^2) / 0.1^2), cf)


"""
    gaussian_mechanism!(s::Real, ϵ::Real, δ::Real, g::DMGrads) :: Nothing

Apply the gaussian mechanism to the input gradient, adding gaussian noise with SD of
`(2 * log(1.25/δ) * s^2) / ϵ^2)` to each gradient entry seperately. This introduces
`(ϵ, δ)`-differential privacy to all variables the gradient depends on with sensitivity
at most `s`. Mutates the gradient, returns `nothing`.

The implementation follows the 2021 paper `Secure Random Sampling in Differential Privacy` by
NAOISE HOLOHAN and STEFANO BRAGHIN. It mitigates some floating point related vulnerabilities,
but not all the known ones.

# Example
Clip and noise a gradient, mutating the input.
```julia
function noise_grad!(g::MetricGradient(Data, LInf), eps, del) :: Priv()
    clip!(L2,g)
    undisc_container!(g)
    gaussian_mechanism!(2, eps, del, g)
    return
end
```
See the [flux-dp example](@ref fluxdp) for a full-blown implementation of private gradient
descent using this mechanism.
"""
function gaussian_mechanism!(s::Real, ϵ::Real, δ::Real, cf::DMGrads) :: Nothing
   additive_noise!(SecureGaussSampler(0, (2 * log(1.25/0.1) * 2/500^2) / 0.1^2), cf)
   return nothing
end


"""
    laplacian_mechanism(s::Real, ϵ::Real, g)

Apply the laplacian mechanism to the input, adding laplacian noise with scaling parameter of
`(s / ϵ)` and location zero to each gradient entry seperately. This introduces
`(ϵ, 0)`-differential privacy to all variables the input depends on with sensitivity
at most `s`. Makes a copy of the input, then noises and returns the copy.

The implementation follows the 2021 paper `Secure Random Sampling in Differential Privacy` by
NAOISE HOLOHAN and STEFANO BRAGHIN. It mitigates some floating point related vulnerabilities,
but not all the known ones.


# Example
Clip and noise a matrix, not mutating the input.
```julia
function noise_grad!(g::MetricMatrix(Data, LInf), eps) :: Priv()
    cg = clip(L2,g)
    ug = undisc_container(cg)
    laplacian_mechanism(2, eps, ug)
end
```
"""
laplacian_mechanism(s::Real, ϵ::Real, cf) = additive_noise(SecureLaplaceSampler(0, s / ϵ), cf)


"""
    laplacian_mechanism!(s::Real, ϵ::Real, g::DMGrads) :: Nothing

Apply the laplacian mechanism to the input, adding laplacian noise with scaling parameter of
`(s / ϵ)` and location zero to each gradient entry seperately. This introduces
`(ϵ, 0)`-differential privacy to all variables the input depends on with sensitivity
at most `s`. Mutates the input, returns `nothing`.

The implementation follows the 2021 paper `Secure Random Sampling in Differential Privacy` by
NAOISE HOLOHAN and STEFANO BRAGHIN. It mitigates some floating point related vulnerabilities,
but not all the known ones.

# Example
Clip and noise a matrix, mutating the input.
```julia
function noise_grad!(g::MetricMatrix(Data, LInf), eps) :: Priv()
    clip!(L2,g)
    undisc_container!(g)
    laplacian_mechanism!(2, eps, g)
    return
end
```
"""
function laplacian_mechanism!(s::Real, ϵ::Real, cf :: DMGrads) :: Nothing
   additive_noise!(SecureLaplaceSampler(0, s / ϵ), cf)
   return nothing
end


function additive_noise!(dist, cf::DMGrads) :: Nothing
   for p in cf.grads.params
      cf.grads[p] += rand(dist, size(p))
   end
   return nothing
end
additive_noise(dist, m :: AbstractVector) = m + rand(dist, size(m))
additive_noise(dist, m :: Number) :: Number = m + rand(dist)
function additive_noise(dist, c::DMGrads) :: DMGrads
   cf = clone(c)
   additive_noise!(dist, cf)
   return cf
end


"""
    above_threshold(queries :: Vector{Function}, epsilon :: Real, d, T :: Number) :: Integeri

The above-threshold mechanism. Input is a vector of 1-sensitive queries on dataset `d` mapping to
the reals. Returns the index of the first query whose result at `d` plus `(4/epsilon)`-Laplacian
noise is above the given threshold `T` plus `(2/epsilon)`-Laplacian noise. This is `(epsilon,0)`-private in `d`!
"""
function above_threshold(queries :: Vector{F} where F <: Function, epsilon :: Real, d, T :: Number) :: Integer
   T = laplacian_mechanism(2, epsilon, T)
   for i in 1:length(queries)
      qq = queries[i](d)
      qq = laplacian_mechanism(4, epsilon, qq)
      if qq >= T
         return i
      end
   end
   return length(queries)
end

# the naive implementation of this is insecure, and the secure implementation is complicated.
# we can support this again once we have time to handle this.
# see https://arxiv.org/pdf/1912.04222.pdf and #258
#"""
#    exponential_mechanism(r::Number, eps::Number, xs::Vector, u::Function)
#
#Return an element of the input vector `xs` based on the score given by the function `u`,
#mapping from the elements of `xs` to a real number. The probability for element `e` to be
#chosen is proportional to `exp(eps*u(e)/(2*r))`. The mechanism is `(eps,0)`-private in the variables that `u`
#is `r`-sensitive in.
#"""
#function exponential_mechanism(r, eps, xs, u)
#    # compute score for each entry of xs
#    scores = [u(x) for x in xs]
#    
#    # compute probability weight for each entry 
#    p = [exp(eps * score / (2 * r)) for score in scores]
#    
#    # clip to make a probability vector
#    p = clip(L1, p)
#
#    # choose from xs based on the probabilities
#    return xs[rand(Distributions.Categorical(p))]
#end
#

"""
    sample(n::Integer, m::AbstractMatrix, v::AbstractMatrix) :: Tuple{Matrix, Matrix}

Take a uniform sample (with replacement) of `n` rows of the matrix `m` and corresponding rows of matrix `v`.
Returns a tuple of `n`-row submatrices of `m` and `v`.
"""
function sample(n::Integer, m::AbstractMatrix, v::AbstractMatrix) :: Tuple{Matrix, Matrix}
    r = rand(axes(m,1), n)
    return (m[r,:], v[r,:])
end


###########################################
# clipping things

"""
    clip!(l::Norm, g::DMGrads) :: Nothing

Clip the gradient, i.e. scale by `1/norm(g,l)` if `norm(g,l) > 1`. Mutates the gradient, returns `nothing`.
"""
function clip!(p::Norm, cg::DMGrads) :: Nothing

    n = norm(cg.grads.grads, p)

    if n > 1
       scale_gradient!(1/n, cg)
    end

    return nothing
end


"""
    clip(l::Norm, g::DMGrads) :: DMGrads

Return a clipped copy of the gradient, i.e. scale by `1/norm(g,l)` if `norm(g,l) > 1`.
"""
function clip(p::Norm, cg::DMGrads) :: DMGrads

    n = norm(cg.grads.grads, p)

    ccg = clone(cg)

    if n > 1
       scale_gradient!(1/n, ccg)
    end

    return ccg
end


"""
    clip(l::Norm, g::AbstractVector)

Return a clipped copy of the input vector, i.e. scale by `1/norm(g,l)` if `norm(g,l) > 1`.
"""
function clip(p::Norm, cg::AbstractVector)

    n = norm(cg, p)

    ccg = deepcopy(cg)

    if n > 1
       ccg .*= 1/n
    end

    return ccg
end


"""
    clipn(v::T, upper::T, lower::T) where T <: Number

Clip the number `v`, i.e. return `v` if it is in `[lower,upper]`, return `upper` if `v` is larger than `upper`,
and return `lower` if `v` is smaller than `lower`.
"""
function clipn(v::T, upper::T, lower::T) where T <: Number
   if lower > upper
      error("Lower bound must be less or equal upper bound.")
   elseif v > upper
      return upper
   elseif v < lower
      return lower
   else
      return v
   end
end


###########################################
# gradients

"""
    scale_gradient!(s::Number, gs::DMGrads) :: Nothing

Scale the gradient represented by the Zygote.Grads struct wrapped in the input DMGrads `gs`
by the scalar `s`. Mutates the gradient, returns `nothing`.
"""
function scale_gradient!(s :: Number, cg::DMGrads) :: Nothing
   for g in cg.grads
      rmul!(g, s)
   end
   return nothing
end


"""
    subtract_gradient!(m::DMModel, gs::DMGrads) :: Nothing

Subtract the gradient represented by the Zygote.Grads struct wrapped in the input DMGrads `gs`
from the parameters of the model `m`. Mutates the model, returns `nothing`.
"""
function subtract_gradient!(m::DMModel, gs::DMGrads) :: Nothing
   p = Flux.params(m.model)
   for i in 1:size(p.order.data)[1]
      p[i] .-= gs.grads[p[i]]
   end
   return nothing
end


"""
    sum_gradients(g::DMGrads, gs::DMGrads...) :: DMGrads

Sum two or more `DMGrads` gradients. Errors if they belong to different DMModels.
"""
function sum_gradients(g::DMGrads, gs::DMGrads...) :: DMGrads
   return DMGrads(.+(g.grads,[gg.grads for gg in gs]...))
end


"""
    zero_gradient(m::DMModel) :: DMGrads

Create a zero gradient for the given model.
"""
function zero_gradient(m::DMModel) :: DMGrads
  eg = Zygote.Grads(IdDict{Any,Any}(), Flux.params(m.model))
  for p in eg.params
     eg[p] = fill!(similar(p), 0)
  end
  return DMGrads(eg)
end


###########################################
# matrix stuff

"""
    map_rows(f::Function, m::AbstractMatrix)

Map the Vector-to-Vector function `f` to the rows of `m`. 
"""
map_rows(f::Function, m::AbstractMatrix) = mapslices(f,m;dims=(2,))


"""
    map_cols(f::Function, m::AbstractMatrix)

Map the Vector-to-Vector-function `f` to the columns of `m`. 
"""
map_cols(f::Function, m::AbstractMatrix) = mapslices(f,m;dims=(1,))


"""
    map_cols_binary(f::Function, m::AbstractMatrix, n::AbstractMatrix)

Map the binary Vector-to-Vector-function `f` to the columns of `m` and `n`. 
"""
function map_cols_binary(f::Function, m::AbstractMatrix, n::AbstractMatrix)
   a = [f(collect(x),collect(y)) for (x,y) in zip(eachcol(m),eachcol(n))]
   reshape(hcat(a...), (length(a[1]), length(a)))
end


"""
    map_rows_binary(f::Function, m::AbstractMatrix, n::AbstractMatrix)

Map the binary Vector-to-Vector-function `f` to the columns of `m` and `n`. 
"""
function map_rows_binary(f::Function, m::AbstractMatrix, n::AbstractMatrix)
   a = [f(collect(x),collect(y)) for (x,y) in zip(eachrow(m),eachrow(n))]
   Matrix(transpose(hcat(a...)))
end


"""
   fold(f::Function, i, m::AbstractMatrix)

Fold the function `f` over all entries of `m`, using initial value `i`.
"""
fold(f::Function, i, m::AbstractMatrix) = foldl(f, m, init=i)


"""
    reduce_cols(f::Function, m::AbstractMatrix)

Apply the privacy function `f :: (r x 1)-Matrix -> T` to each column of the `(r x c)`-Matrix `m`, return a vector of the results.
If `f` is `(eps,del)`-private in its argument, the reduction is `(r*eps, r*del)`-private in `m`.

"""
reduce_cols(f::Function, m::AbstractMatrix) = [f(vec_to_col(c)) for c in eachcol(m)]


"""
    parallel_private_fold_rows(f::Function, i, m::AbstractMatrix, n::AbstractMatrix)

Fold the privacy function `f :: Vector -> Vector -> I -> I` over the two input matrices' rows simultaneously.
This is parallel composition on the rows of `m` and `n`, so if `f` is `(eps,del)`-private in it's first two arguments,
the fold is `(eps,del)`-private in the input matrices. The input matrices are expected to be measured in the discrete norm.
"""
function parallel_private_fold_rows(f::Function, i, m::AbstractMatrix, n::AbstractMatrix)
   foldl((i,(x,y))->f(x,y,i), [(collect(rm),collect(rn)) for (rm,rn) in zip(eachrow(m), eachrow(n))], init=i)
end


"""
    parallel_private_fold_rows(f::Function, i, m::AbstractMatrix, n::AbstractMatrix)

Fold the privacy function `f :: Vector -> Vector -> I -> I` over the two input matrices' rows simultaneously.
Allows for `f` to mutate the accumulator, returns nothing. 
This is parallel composition on the rows of `m` and `n`, so if `f` is `(eps,del)`-private in it's first two arguments,
the fold is `(eps,del)`-private in the input matrices. The input matrices are expected to be measured in the discrete norm.
"""
function parallel_private_fold_rows!(f::Function, i, m::AbstractMatrix, n::AbstractMatrix)
   for (x,y) in [(collect(rm),collect(rn)) for (rm,rn) in zip(eachrow(m), eachrow(n))] 
      f(x,y,i)
   end
   return nothing
end


"""
    row_to_vec(m::AbstractMatrix) :: Vector

Make the one-row matrix `m` into a vector.
"""
function row_to_vec(m::AbstractMatrix)
   @assert (size(m)[1] == 1) "Tried to make a vector from a matrix that has more than one row"
   Vector(vec(m))
end


"""
    vec_to_row(v::AbstractVector) :: Matrix

Make the vector `v` into a one-row matrix.
"""
function vec_to_row(v::AbstractVector)
   reshape(v, (1, length(v)))
end




###########################################
# Internal use
function internal_expect_const(a)
    a
end

mutable struct Box
    internal_box_content
end

function new_box(m)
    Box(m)
end

function get_box(m)
    m.internal_box_content
end

function map_box!(f,m)
    m.internal_box_content = f(m.internal_box_content)
end


