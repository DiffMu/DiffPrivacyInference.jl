

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
