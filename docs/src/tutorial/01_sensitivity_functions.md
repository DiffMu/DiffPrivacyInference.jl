
# [Sensitivity functions](@id sensitivity-functions)

The sensitivity of a function is a property central to [additive noise mechanisms](https://en.wikipedia.org/wiki/Additive_noise_mechanisms) for introducing differential privacy. Our typechecker infers the sensitivity of your julia code in order to provide privacy bounds on applications of these mechanisms. There are, therefore, two kinds of functions: so called [sensitivity functions](ref to types docs), which are regular, deterministic functions with a sensitivity assigned to each argument, and the randomized [privacy functions](@ref types) with a (ϵ, δ)-differential privacy assigned to each argument. You can use the builtin privacy mechanisms to make a sensitivity function differentially private. This tutorial is about function sensitivity, head over to the [respective tutorial](@ref privacy-functions).

## Sensitivity
For metric spaces ``M,N``, a map ``f:M\rightarrow N`` is [*``s``-sensitive*](https://en.wikipedia.org/wiki/Differential_privacy#Sensitivity) if for all ``x,y \in M``
```math
d_N(f(x), f(y)) \leq s \cdot d_M(x,y)
```
We call the smallest ``s`` such that ``f`` is ``s``-sensitive the *sensitivity* of ``f``.

For example, the function
```julia
f(x) = x + x
```
has sensitivity 2.

The definition extends to multi-argument functions, assigning a seperate sensitivity to each argument. A function ``g:M_1\times...\times M_n\rightarrow N`` is ``s``-sensitive in its first argument if for all ``x,y \in M_1``
```math
max_{x_j\in M_j} d_N(g(x,x_2,...,x_n), g(y,x_2,...,x_n)) \leq s \cdot d_{M_1}(x,y)
```

For example, the function
```julia
g(x1,x2) = x1 + f(x2)
```
has sensitivity 1 in its first and sensitivity 2 in its second argument.

## Sensitivity of expressions
The typechecker will discern between two kinds of expressions by assigning either a sensitivity or a privacy to each variable therein. It can infer the sensitivity of all julia expressions that adhere to the [supported syntax](@ref syntax) and that don't contain any of the [builtin privacy mechanisms](@ref builtins) nor calls to other [privacy functions](@ref privacy-functions). Be aware of the [limitations of the type checker regarding floating point implementations](https://diffmu.github.io/DiffPrivacyInference.jl/dev/tutorial/02_privacy_functions/#Warning:-Floating-point-is-dangerous!)!
