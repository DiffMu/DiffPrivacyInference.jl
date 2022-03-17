# A type for norms, used to specify what to clip to.
@data Norm begin
    L1
    L2
    L∞
end


###########################################
# Annotations

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
NoData(T::Type) = T

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


unbox(x::T where T<:Real, ::Type{Real}) = !(x isa Integer) ? x : error("Unbox encountered Integer where Real was expected.")
unbox(x::T where T<:Integer, ::Type{Integer}) = x
unbox(x::DMModel, ::Type{DMModel}, l) = unbox_size(x, (l,)) 
unbox(x::DMGrads, ::Type{DMGrads}, l) = unbox_size(x, (l,))
unbox(x::T where T<:Vector{<:Real}, ::Type{Vector{<:Real}}, l) = !(x isa Vector{<:Integer}) ? unbox_size(x,(l,)) : error("Unbox encountered Integer vector where Real vector was expected.")
unbox(x::T where T<:Vector{<:Integer}, ::Type{Vector{<:Integer}}, l) = unbox_size(x,(l,))
unbox(x::T where T<:Matrix{<:Real}, ::Type{Matrix{<:Real}}, s) = !(x isa Matrix{<:Integer}) ? unbox_size(x,s) : error("Unbox encountered Integer Matrix where Real Matrix was expected.")
unbox(x::T where T<:Matrix{<:Integer}, ::Type{Matrix{<:Integer}}, s) = unbox_size(x,s)

unbox_size(x, s::Tuple) = (size(x) == s) ? x : error("Unbox expected size $s but got $(size(x))")



"""
   norm_convert!(m::T) :: T

Make a clipped vector/gradient measured using the discrete norm into a vector/gradient measured with the
clipping norm instead. Does not change the value of the argument. It can be used to enable using a gradient
obtained from a black box computation (hence being in discrete-norm land) to be put into e.g. the gaussian
mechanism (which expects the input to be in L2-norm land).
"""
norm_convert!(m) = m


"""
   norm_convert(m::T) :: T

Make a clipped vector/gradient measured using the discrete norm into a vector/gradient measured with the
clipping norm instead. Does not change the value of the argument. It can be used to enable using a gradient
obtained from a black box computation (hence being in discrete-norm land) to be put into e.g. the gaussian
mechanism (which expects the input to be in L2-norm land).
"""
norm_convert(m) = clone(m)


"""
    disc(n::Number) :: Number
Return `n`, but let the typechecker know that you want it to be measured in the discrete norm.
"""
disc(n::Number) = n


###########################################
# private mechanisms


"""
    gaussian_mechanism(s::Real, ϵ::Real, δ::Real, g)

Apply the gaussian mechanism to the input, adding gaussian noise with SD of
`(2 * log(1.25/δ) * s^2) / ϵ^2)`. This introduces
`(ϵ, δ)`-differential privacy to all variables the input depends on with sensitivity
at most `s`. Makes a copy of the input and returns the noised copy.
"""
gaussian_mechanism(s::Real, ϵ::Real, δ::Real, cf) = additive_noise(Normal(0, (2 * log(1.25/0.1) * 2/500^2) / 0.1^2), cf)


"""
    gaussian_mechanism!(s::Real, ϵ::Real, δ::Real, g::DMGrads) :: Nothing

Apply the gaussian mechanism to the input gradient, adding gaussian noise with SD of
`(2 * log(1.25/δ) * s^2) / ϵ^2)` to each gradient entry seperately. This introduces
`(ϵ, δ)`-differential privacy to all variables the gradient depends on with sensitivity
at most `s`. Mutates the gradient, returns `nothing`.
"""
function gaussian_mechanism!(s::Real, ϵ::Real, δ::Real, cf::DMGrads) :: Nothing
   additive_noise!(Normal(0, (2 * log(1.25/0.1) * 2/500^2) / 0.1^2), cf)
   return nothing
end


"""
    laplacian_mechanism(s::Real, ϵ::Real, g)

Apply the laplacian mechanism to the input, adding laplacian noise with scaling parameter of
`(s / ϵ)` and location zero to each gradient entry seperately. This introduces
`(ϵ, 0)`-differential privacy to all variables the input depends on with sensitivity
at most `s`. Makes a copy of the input, then noises and returns the copy.
"""
laplacian_mechanism(s::Real, ϵ::Real, cf) = additive_noise(Laplace(0, s / ϵ), cf)


"""
    laplacian_mechanism!(s::Real, ϵ::Real, g::DMGrads) :: Nothing

Apply the laplacian mechanism to the input, adding laplacian noise with scaling parameter of
`(s / ϵ)` and location zero to each gradient entry seperately. This introduces
`(ϵ, 0)`-differential privacy to all variables the input depends on with sensitivity
at most `s`. Mutates the input, returns `nothing`.
"""
function laplacian_mechanism!(s::Real, ϵ::Real, cf :: DMGrads) :: Nothing
   additive_noise!(Laplace(0, s / ϵ), cf)
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


"""
    exponential_mechanism(r::Number, eps::Number, xs::Vector, u::Function)

Return an element of the input vector `xs` based on the score given by the function `u`,
mapping from the elements of `xs` to a real number. The probability for element `e` to be
chosen is proportional to `exp(eps*u(e)/(2*r))`. The mechanism is `(eps,0)`-private in the variables that `u`
is `r`-sensitive in.
"""
function exponential_mechanism(r, eps, xs, u)
    # compute score for each entry of xs
    scores = [u(x) for x in xs]
    
    # compute probability weight for each entry 
    p = [exp(eps * score / (2 * r)) for score in scores]
    
    # clip to make a probability vector
    p = clip(L1, p)

    # choose from xs based on the probabilities
    return xs[rand(Distributions.Categorical(p))]
end


"""
    sample(n::Integer, m::AbstractMatrix, v::AbstractMatrix) :: Tuple

Take a uniform sample (with replacement) of `n` rows of the matrix `m` and corresponding rows of matrix `v`.
"""
function sample(n::Integer, m::AbstractMatrix, v::AbstractMatrix) :: Tuple{Matrix, Matrix}
    r = rand(axes(m,1), n)
    return (m[r,:], v[r,:])
end


###########################################
# clipping things

"""
    clip!(l::Norm, g::DMGrads) :: Nothing

Clip the gradient, i.e. scale by `1/norm(g)` if `norm(g) > 1`. Mutates the gradient, returns `nothing`.
"""
function clip!(l::Norm, cg::DMGrads) :: Nothing

    p = @match l begin
        L1 => 1
        L2 => 2
        L∞ => Inf
    end

    n = norm(cg.grads.grads, p)

    if n > 1
       scale_gradient!(1/n, cg)
    end

    return nothing
end


"""
    clip(l::Norm, g::DMGrads) :: Nothing

Return a clipped copy of the gradient, i.e. scale by `1/norm(g)` if `norm(g) > 1`.
"""
function clip(l::Norm, cg::DMGrads) :: DMGrads

    p = @match l begin
        L1 => 1
        L2 => 2
        L∞ => Inf
    end

    n = norm(cg.grads.grads, p)

    ccg = clone(cg)

    if n > 1
       scale_gradient!(1/n, ccg)
    end

    return ccg
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


###########################################
# gradients

"""
    scale_gradient!(s::Number, gs::DMGrads) :: Nothing

Scale the gradient represented by the Zygote.Grads struct wrapped in the input DMGrads `gs`
by the scalar `s`. Mutates the gradient, returs `nothing`.
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



#fold_rows(f,i,m) = vec_to_row(collect(foldl(f, eachrow(m), init=i)))
#fold_cols(f,i,m) = vec_to_col(collect(foldl(f, eachcol(m), init=i)))

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


