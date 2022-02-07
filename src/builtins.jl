# A type for norms, used to specify what to clip to.
@data Norm begin
    L1
    L2
    L∞
end

"""
Annotation for functions whose differential privacy we want to infer.

# Examples
A privacy function with argument `x` whose privacy will be inferred and argument `y` of type
Integer whose privacy we're not interested in:
```julia
function foo(x, y::NoData(Integer)) :: Priv()
   x
end
```
"""
Priv() = Any
Priv(T::DataType) = T

"""
Annotation for function arguments whose privacy is of no interest to us.
Their privacy will most likely be set to infinity to allow tighter bounds on other arguments.

# Examples
A privacy function with argument `x` whose privacy will be inferred and argument `y` of type
Integer whose privacy we're not interested in:
```julia
function foo(x, y::NoData(Integer)) :: Priv()
   x
end
```
"""
NoData() = Any
NoData(T::DataType) = T

"""
Annotation for functions that cannot be typechecked. Their arguments will be assigned infinite
sensitivity. Note that it is not allowed to mutate any of the arguments in a function like this,
if you do the typechecking result will be invalid!

# Examples
A function calling an imported qualified name, which is not permissible in non-black-boxes:
```julia
loss(X, y, m::DMModel) :: BlackBox() = Flux.crossentropy(m.model(X), y)
```
"""
BlackBox() = Any
BlackBox(T::DataType) = T

"""
Annotation for variables of a function that are privacy functions themselves. You have to
annotate privacy function function arguments, otherwise typechecking will assume a non-private
function and fail if you insert a privacy function.
"""
PrivacyFunction = Function

"""
   norm_convert!(m::T) :: T

Make a clipped vector/gradient measured using the discrete norm into a vector/gradient measured with the
clipping norm instead. Does not change the value of the argument. It can be used to enable using a gradient
obtained from a black box computation (hence being in discrete-norm land) to be put into e.g. the gaussian
mechanism (which expects the input to be in L2-norm land).
"""
norm_convert!(m) = m


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


"""
    return_copy(g::DMGrads)
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
   return return_copy(gs)
end
```
"""
return_copy(g::DMGrads) :: DMGrads = DMGrads(Zygote.Grads(IdDict(g.grads.grads), g.grads.params))
return_copy(g::DMModel) :: DMModel = DMModel(deepcopy(g.params))
return_copy(g::AbstractVecOrMat) = deepcopy(g)


"""
    scale_gradient!(s::Number, gs::DMGrads) :: Tuple{}

Scale the gradient represented by the Zygote.Grads struct wrapped in the input DMGrads `gs`
by the scalar `s`. Mutates the gradient, returs ().
"""
function scale_gradient!(s :: Number, cg::DMGrads) :: Tuple{}
   for g in cg.grads
      rmul!(g, s)
   end
   return ()
end


"""
    subtract_gradient!(m::DMModel, gs::DMGrads) :: Tuple{}

Subtract the gradient represented by the Zygote.Grads struct wrapped in the input DMGrads `gs`
from the parameters of the model `m`. Mutates the model, returns ().
"""
function subtract_gradient!(m::DMModel, gs::DMGrads) :: Tuple{}
   p = Flux.params(m.model)
   for i in 1:size(p.order.data)[1]
      p[i] .-= gs.grads[p[i]]
   end
   return ()
end





"""
    gaussian_mechanism(s::Real, ϵ::Real, δ::Real, g)

Apply the gaussian mechanism to the input, adding gaussian noise with SD of
`(2 * log(1.25/δ) * s^2) / ϵ^2)`. This introduces
`(ϵ, δ)`-differential privacy to all variables the input depends on with sensitivity
at most `s`. Makes a copy of the input and returns the noised copy.
"""
gaussian_mechanism(s::Real, ϵ::Real, δ::Real, cf) = additive_noise(Normal(0, (2 * log(1.25/0.1) * 2/500^2) / 0.1^2), cf)

"""
    gaussian_mechanism!(s::Real, ϵ::Real, δ::Real, g::DMGrads) :: Tuple{}

Apply the gaussian mechanism to the input gradient, adding gaussian noise with SD of
`(2 * log(1.25/δ) * s^2) / ϵ^2)` to each gradient entry seperately. This introduces
`(ϵ, δ)`-differential privacy to all variables the gradient depends on with sensitivity
at most `s`. Mutates the gradient, returns ().
"""
gaussian_mechanism!(s::Real, ϵ::Real, δ::Real, cf::DMGrads) :: Tuple{} = additive_noise!(Normal(0, (2 * log(1.25/0.1) * 2/500^2) / 0.1^2), cf)



"""
    laplacian_mechanism(s::Real, ϵ::Real, g)

Apply the laplacian mechanism to the input, adding laplacian noise with scaling parameter of
`(s / ϵ)` and location zero to each gradient entry seperately. This introduces
`(ϵ, 0)`-differential privacy to all variables the input depends on with sensitivity
at most `s`. Makes a copy of the input, then noises and returns the copy.
"""
laplacian_mechanism(s::Real, ϵ::Real, cf) = additive_noise(Laplace(0, s / ϵ), cf)

"""
    laplacian_mechanism!(s::Real, ϵ::Real, g::DMGrads) :: Tuple{}

Apply the laplacian mechanism to the input, adding laplacian noise with scaling parameter of
`(s / ϵ)` and location zero to each gradient entry seperately. This introduces
`(ϵ, 0)`-differential privacy to all variables the input depends on with sensitivity
at most `s`. Mutates the input, returns ().
"""
laplacian_mechanism!(s::Real, ϵ::Real, cf :: DMGrads) = additive_noise!(Laplace(0, s / ϵ), cf)


function additive_noise!(dist, cf::DMGrads) :: Tuple{}
   for p in cf.grads.params
      cf.grads[p] += rand(dist, size(p))
   end
   return ()
end
additive_noise(dist, m :: AbstractVector) = m + rand(dist, size(m))
additive_noise(dist, m :: Number) :: Number = m + rand(dist)
function additive_noise(dist, c::DMGrads) :: Tuple{}
   cf = return_copy(c)
   additive_noise!(dist, cf)
   return cf
end


"""
    above_threshold(queries :: Vector{Function}, epsilon :: Real, d, T :: Number) :: Integer
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
   return n
end



"""
    clip!(l::Norm, g::DMGrads) :: Tuple{}

Clip the gradient, i.e. scale by `1/norm(g)` if `norm(g) > 1`. Mutates the gradient, returns ().
"""
function clip!(l::Norm, cg::DMGrads) :: Tuple{}

    p = @match l begin
        L1 => 1
        L2 => 2
        L∞ => Inf
    end

    n = norm(cg.grads.grads, p)

    if n > 1
       scale_gradient!(1/n, cg)
    end

    return ()
end

"""
    clip(l::Norm, g::AbstractVector)

Return a clipped copy of the input vector, i.e. scale by `1/norm(g)` if `norm(g) > 1`.
"""
function clip(l::Norm, cg::AbstractVector)
    p = @match l begin
        L1 => 1
        L2 => 2
        L∞ => Inf
    end

    n = norm(cg, p)

    ccg = deepcopy(cg)

    if n > 1
       ccg .*= 1/n
    end

    return ccg
end


"""
    clip(v::T, upper::T, lower::T) where T <: Number

Clip the number `v`, i.e. return `v` if it is in `[lower,upper]`, return `upper` if `v` is larger than `upper`,
and return `lower` if `v` is smaller than `lower`.
"""
function clip(v::T, upper::T, lower::T) where T <: Number
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


"""
    sample(n::Integer, m::AbstractMatrix, v::AbstractMatrix) :: Tuple

Take a uniform sample (with replacement) of `n` rows of the matrix `m` and corresponding rows of matrix `v`.
"""
function sample(n::Integer, m::AbstractMatrix, v::AbstractMatrix) :: Tuple{Matrix, Matrix}
    r = rand(axes(m,1), n)
    return (m[r,:], v[r,:])
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
# Internal use
function internal_expect_const(a)
    a
end

###########################################
# Demutation testing

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


