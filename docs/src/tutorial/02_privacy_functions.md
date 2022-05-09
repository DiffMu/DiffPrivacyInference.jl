
# [Privacy functions](@id privacy-functions)



## (``\varepsilon``, ``\delta``)-Differential Privacy
For metric spaces ``M,N``, a map ``f:M\rightarrow N`` is [*(``\varepsilon``, ``\delta``)-differentially private*](https://en.wikipedia.org/wiki/Differential_privacy) if for all ``x,y \in M`` with ``d_M(x,y) = 1`` and any set ``S\subseteq N`` we have
```math
Pr[f(x) \in S] \leq e^{\varepsilon} \cdot Pr[f(y) \in S] + \delta
```
Note that `f` being a probablilistic function is necessary for this definition to hold. Intuitively, the output distributions of an (``\varepsilon``, ``\delta``)-differentially private function given neighboring inputs are hard to distinguish.

## Additive noise
It is possible to create an (``\varepsilon``, ``\delta``)-differentially private function from a function with finite sensitivity by [adding noise drawn from a certain distribution](https://en.wikipedia.org/wiki/Additive_noise_mechanisms). We support two such mechanisms.

### Laplacian Mechanism
Let ``D`` be some space equipped with the [discrete metric](@ref measuring-distance). Given a function ``f:D\rightarrow \mathbb{R}^n`` that is``s``-sensitive in ``L2`` norm, for every ``\varepsilon\in(0,1)`` the Laplacian Mechanism
```math
\mathcal{M}_\text{Gauss}(f, \varepsilon)(x) = f(x) + \mathcal{Lap}^n\left(\mu = 0, b = \frac{s}{\varepsilon}\right)
```
yields an (``\varepsilon``, 0)-differentially private function, where ``\mathcal{Lap}^n(\mu, b)`` denotes an ``n``-dimensional random variable drawn from the [Laplace distributioin](https://en.wikipedia.org/wiki/Laplace_distribution).

This mechansim is implemented in the [`laplacian_mechanism`](@ref) builtin function. There is a mutating implementation that does not make a copy of the value to be noised in [`laplacian_mechanism!`](@ref).


### Gaussian Mechanism
Let ``D`` be some space equipped with the [discrete metric](@ref measuring-distance). Given a function ``f:D\rightarrow \mathbb{R}^n`` that is``s``-sensitive in ``L2`` norm, for every ``\delta\in(0,1)`` and ``\varepsilon\in(0,1)`` the Gaussian Mechanism
```math
\mathcal{M}_\text{Gauss}(f, \varepsilon, \delta)(x) = f(x) + \mathcal{N}^n\left(\mu = 0, \sigma^2 = \frac{2 \ln (1.25/\delta) \cdot s^2}{\varepsilon^2}\right)
```
yields an (``\varepsilon``, ``\delta``)-differentially private function, where ``\mathcal{N}^n(\mu, \sigma^2)`` denotes an ``n``-dimensional [normally distributed](https://en.wikipedia.org/wiki/Normal_distribution) random variable.

This mechansim is implemented in the [`gaussian_mechanism`](@ref) builtin function. There is a mutating implementation that does not make a copy of the value to be noised in [`gaussian_mechanism!`](@ref). Here's a function that achieves (0.1, 0.2)-differential privacy for it's integer argument by employing the Gaussian Mechanism:
```julia
julia> typecheck_hs_from_string("
       module Foo
       function foo(x::Integer) :: Priv()
          gaussian_mechanism(1,0.1,0.2,x)
       end
       end")

---------------------------------------------------------------------------
Type:
{
|   (Integer @ (0.1, 0.2)) ->* Real
}

---------------------------------------------------------------------------
```

## Warning: Floating point is dangerous!
The aforementioned definitions of differential privacy (and the related [notion of sensitivity](@ref sensitivity-functions)) are defined on abstracet [metric spaces](https://en.wikipedia.org/wiki/Metric_space). Floating point numbers are an approximation of the real numbers, but in some respects differ fatally in their behaviour, especially when talking about probabilities, or when performing simple arithmetics on numbers of very different scale. Hence, the theoretical results don't really hold for floating point implementations of differentially private functions, as was [spectacularily proven](https://www.microsoft.com/en-us/research/wp-content/uploads/2012/10/lsbs.pdf). Mitigation for the flaws in naive random floating point sampling was provided by a [2021 paper](https://arxiv.org/abs/2107.10138), whose approach we use for our implementation of the additive noise mechanisms. We do not, however, provide sensitivity/privacy guarantees in case of overflow situations or rounding errors. These are [very hard to take into account](https://cs-people.bu.edu/jiawenl/pdf/2020DP-FLPT.pdf) even in manual proofs and present a somewhat open problem.


## Nice properties of privacy functions
There are nice theorems about properties of differentially private functions in the [Privacybook](https://www.cis.upenn.edu/~aaroth/Papers/privacybook.pdf). We are expecially interested in two of them.

### Robustness to Post-Processing
Proposition 2.1 claims that no matter what we do with the output of an (``\varepsilon``, ``\delta``)-differentially private function, it stays (``\varepsilon``, ``\delta``)-differentially private. Our typechecker knows this:
```julia
julia> typecheck_hs_from_string("
       module Foo
       function foo(x::Integer) :: Priv()
          gx = gaussian_mechanism(1,0.1,0.2,x)
          23 * gx + 42
       end
       end")

---------------------------------------------------------------------------
Type:
{
|   (Integer @ (0.1, 0.2)) ->* Real
}

---------------------------------------------------------------------------
```

### Advanced Composition
Theorem 3.1 claims that composing an (``\varepsilon``, ``\delta``)-differentially private function with itself `k` times yields an (``\varepsilon``', k``\delta`` + ``\delta``')-differentially private function for any ``\delta'\in(0,1])``, where ``\varepsilon' = 2\sqrt{2k \ln(\frac{1}{\delta′})}\varepsilon``. This can be expressed using a julia `for`-loop:

```julia
julia> typecheck_hs_from_string("
       module Foo
       function foo(x::Integer) :: Priv()
          y = 0.0
          for i in 1:5
             gx = gaussian_mechanism(1,0.1,0.2,x)
             y = y + 23 * gx + 42
          end
          y
       end
       end")

---------------------------------------------------------------------------
Type:
{
|   - Integer@(0.2⋅√(10.0⋅(0 - ln(s₁₀))), 1 + s₁₀)
|   --------------------------
|    ->* Real
}
where
 - Variable s₁₀ can be chosen with type Real to be within (0,1]. Appeared in the privacy loop in none: line 5

---------------------------------------------------------------------------
Constraints:
constr₁₅ : s₁₀ ≤ 1,
constr₁₆ : 0 < s₁₀
```

## Privacy of expressions
The typechecker will discern between two kinds of expressions by assigning either a [sensitivity](@ref sensitivity-functions) or a privacy to each variable therein. It can infer the privacy of all julia expressions that adhere to the [supported syntax](@ref syntax) and describe a differentially private randomized function. This means that it employs one of the two aforementioned mechanisms or calls a function that does.
