
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

