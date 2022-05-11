
# [Measuring Distance](@id measuring-distance)

The [defintion of differential privacy](https://en.wikipedia.org/wiki/Differential_privacy#Definition_of_%CE%B5-differential_privacy) employs the notion of "two datasets that differ on a single element". It follows that the distance metric on the input space of a differentially private function must be one in which it is possible to measure this notion. On the other hand, the [mechanisms we employ](https://en.wikipedia.org/wiki/Additive_noise_mechanisms) to make a function differentially private expect the output space of said function to be equipped with a different distance metric, namely the one induced by the `L2` norm. Hence, one has to determine the sensitivity of a function with respect to different metrics on input and output space.

## Metric on numbers
We employ two different types for the interesting metric spaces on numbers, i.e. ℝ for the real numbers with the standard (euclidean) metric, and 𝔻 for the real numbers with the discrete metric. That is:
```math
d_\mathbb{R}(x,y) = |x-y|
```
and
```math
d_\mathbb{D}(x,y) = \begin{cases}
      0, & \text{if}\ x=y \\
      1, & \text{otherwise}
    \end{cases}
```
Our typechecker differentiates between these two, using the native julia type `Real` and our custom type [`Data`](@ref). You can convert back and forth between the two using the builtin [`discrete`](@ref)`(n::Real)` and [`undisc`](@ref)`(n::Data)` functions. Note that both of them incur a sensitivity penalty, the former an infinite one.

## Metric on Vectors
We extend the metrics from the previous section on vector types with elements of type ℝ and 𝔻. The `DMGrads` type behaves just like a vector, and the metrics presented here are also applicable there.
### Vectors over ℝ:
   - The (`L1`, ℝ)-metric sums element-wise distances:
```math
    d_{L1,\mathbb{R}}(v,w) = \sum_i d_\mathbb{R}(v_i, w_i)
```
   - The (`L2`, ℝ)-metric sums the squares of element-wise distances and takes the square root (euclidean metric):
```math
    d_{L2,\mathbb{R}}(v,w) = \sqrt{\sum_i d_\mathbb{R}(v_i, w_i)^2}
```
   - The (`LInf`, ℝ)-metric is the maximum of element-wise distances:
```math
    d_{L\infty,\mathbb{R}}(v,w) = \max_i d_\mathbb{R}(v_i, w_i)
```
### Vectors over 𝔻:
   - The (`L1`, 𝔻)-metric is the number of entries in which the vectors differ:
```math
d_{L1,\mathbb{D}}(v,w) = \sum_i d_\mathbb{D}(v_i, w_i)
```
   - The (`L2`, 𝔻)-metric is the square root of (`L1`, 𝔻)-metric:
```math
d_{L2,\mathbb{D}}(v,w) = \sqrt{\sum_i d_\mathbb{D}(v_i, w_i)^2} = \sqrt{d_{L1,\mathbb{D}}(v,w) }
```
   - The (`LInf`, 𝔻)-metric is `0` if and only if the vectors are equal:
```math
d_{L\infty,\mathbb{D}}(v,w) = \max_i d_\mathbb{D}(v_i, w_i)
```
Use the [`MetricVector`](@ref) (or [`MetricGradient`](@ref) if we're talking gradients) function to annotate vector function arguments with the metric you wish to use for them. The function [`norm_convert`](@ref)`(n::Norm, v)` lets you convert between different metrics, which comes with a sensitivity penalty.

## Metric on Matrices
We again extend the metrics from the section on vectors to matrix types with elements of type ℝ and 𝔻, by forming the sum of row-wise distances. That is, for `m,n` being matrices with elements of type τ and `l` being one of `L1,L2,LInf`, we have
```math
d_{\mathbb{M}^\star_l\tau}(m,n) = \sum_j d_{l,\tau}(m_j,n_j)
```
in particular:
```math
d_{\mathbb{M}^\star_{L1}\mathbb{D}}(m,n) = \text{number of matrix entries that differ}
```
```math
d_{\mathbb{M}^\star_{L\infty}\mathbb{D}}(m,n) = \text{number of matrix rows that differ somewhere}
```
So the (`LInf`, 𝔻)-metric on matrices allows us to measure the property required by the definition of differential privacy, as discussed in the introduction: "two datasets that differ on a single element" are precisely two matrices with (`LInf`, 𝔻)-metric of 1.

Use the [`MetricMatrix`](@ref) function to annotate matrix function arguments with the metric you wish to use for them. The function [`norm_convert`](@ref)`(n::Norm, v)` lets you convert between different metrics, which comes with a sensitivity penalty.

## Programming with the metric in mind
The two additive noise mechanisms we support, namely [`laplacian_mechanism`](@ref) and [`gaussian_mechanism`](@ref), both expect the input they are supposed to add noise to to be of a type that uses (`L2`,ℝ)-metric. Their output will then be of a corresponding type measured in (`LInf`,ℝ)-metric. This means you have to take care to convert your container types to the right metric before using these mechanisms. See the [flux-dp code](@ref fluxdp) for example usage.
