
# [Types](@id types)
The privacy analysis result is presented to you as a type together with a collection of [Constraints](@ref). You need to be able to read the types to understand it, so here's how.


## Overview
Here's a list of all possible result types. See the below sections for more elaborate explanations.

| DP type          | Description |
| :--------------- | :---------- |
| `Any`            | Any type, like in julia|
| `Bool`           | Booleans, like in julia |
| `Integer`        | Integers, like in julia |
| `Real`           | Reals, like in julia       |
| `Data`           | Reals, but measured with the discrete metric |
| `τ[s ©]`         | static number of type `τ` with value `s` |
| `τ[s]`           | number of type `τ` where it is unknown whether it's static or not |
| `(τ₁ @ s₁, ...) -> τ`          | sensitivity function mapping types `τ₁,...` to  `τ` with sensitivities `s₁,...`|
| `(τ₁ @ (e₁,d₁), ...) ->* τ`    | privacy function mapping types `τ₁,...` to  `τ` with privacies `(e₁,d₁),...`|
| `BlackBox[τ₁,...]`             | Black box function with julia type signature `[τ₁,...]`|
| `Tuple{τ₁,...}`                | Tuple, like in julia |
| `Matrix<n: N, c: C>[s × t]{τ}` | `s×t`-Matrix with elements of type `τ`, measured in norm `N`, `C`-norm of each row bounded by 1 |
| `Vector<n: N, c: C>[s]{τ}`     | Row vector with `s` elements of type `τ`, measured in norm `N`, its `C`-norm bounded by 1 |
| `DMGrads<n: N, c: C>[s]{τ}`    | `Zygote.jl` gradient with `s` elements of type `τ`, measured in norm `N`, its `C`-norm bounded by 1 |
| `DMContainer<kind: K, n: N, c: C>[s]{τ}` | One of the above three container types (namely `K`) with `s` elements of type `τ`, measured in norm `N`, its `C`-norm bounded by 1 |
| `DMModel{τ}`                   | `Flux.jl` model with parameter type `τ`|
| `τ₁ ∧ τ₂`                      | Infimum type of `τ₁` and `τ₂` w.r.t. subtyping, i.e. the "largest" type `τ` s.t. `τ₁ ⊑ τ` and `τ₂ ⊑ τ` |


## Functions
Function types carry the information you're probably most interested in, namely the inferred sensitivity or differential privacy of the function arguments. There are two sorts of functions, [sensitivity functions](@ref) and [privacy functions](@ref).
### Sensitivity functions
Functions that do not employ any differential privacy mechanisms have this type. It is denoted like this:
```
 (τ₄ @ 0, τ @ s₁) -> Integer[2.0 ©]
```
The part before the `->` is the list of argument types this function admits, together with the inferred [sensitivity](https://en.wikipedia.org/wiki/Differential_privacy#Sensitivity) annotated with the `@` symbol. Hence this tells us the typechecker inferred the function to be `0`-sensitive in its first and `s₁`-sensitivie in it's second input. It outputs the number `2`.

### Privacy functions
Functions that do use one of the [builtin privacy mechanisms](@ref) or use other functions that do are called `privacy functions`. The typechecker can infer their [(ε, δ)-differential privacy](https://en.wikipedia.org/wiki/Differential_privacy) parameters. The result looks like this:
```
{
|   - τ₅[s ©] @ (0, 0)
|
|   - Matrix<n: L2, c: τ₂>[s₃ × s₂]{τ₃₄}
|       @ (s, 0)
|   --------------------------
|    ->* Matrix<n: LInf, c: U>[s₃ × s₂]{Real}
}
```
It was inferred that the input julia code describes a [privacy function](@ref) (denoted by `->*`) that maps some number with value `s` and some `s₃ × s₂`-dimensional matrix with elements of type `τ₃₄` to a `s₃ × s₂`-dimensional matrix with `Real` entries. The inferred privacy of the arguments is `(0,0)` and `(s,0)` respectively.

## Base types
### Numbers
The typechecker can discern between `Integer` and `Real` number types. Julia number types finer than that are not permitted. The typechecker however makes another distinction, namely between static and non-static numbers. A variable with a static number type is one in whose sensitivity/privacy we are not interested and whose value is instead used to express the sensitivity/privacy of other variables. A static real number with variable value `s` is denoted like this:
```
Real[s ©]
```

An example are the `eps` and `del` parameters of the [`gaussian_mechanism`](@ref) function: you are interested in its privacy with respect to the values of these parameters.
```
julia> typecheck_hs_from_string("
       module L
       function f(eps::Static(), del::Static(), x::Matrix) :: Priv()
         gaussian_mechanism(1, eps, d, x)
       end
       end")
---------------------------------------------------------------------------
Type:
{
|   - τ₅[eps ©]@(0, 0)
|   
|   - τ₇[del ©]@(0, 0)
|   
|   - Matrix<n: L2, c: τ₂>[s₄ × s₃]{τ₃₈}
|       @ (eps, del)
|   --------------------------
|    ->* Matrix<n: LInf, c: U>[s₄ × s₃]{Real}
}
(...)
```
The privacy of the `x` argument is expressed in terms of the `eps` and `del` arguments. Note how you can [annotate](@ref) numeric variables if you want them to be static.

### Data
The sensitivity of a function is given with respect to a metric on the input and output spaces of the function. The typechecker supports two metrics on numbers, namely the euclidean metric `d(x,y) = |x-y|` and the discrete metric `d(x,y) = 0 if x==y, 1 otherwise`. If you want to use the latter, annotate your variables with `Data`:`
```
julia> typecheck_hs_from_string("module L
       function f(x::Data)
          disc(100.0) * x
       end
       end")
---------------------------------------------------------------------------
Type:
{
|   (Data @ 1) -> Data
}
```
Note that you have to use the [`disc`](@ref) function to tell the typechecker that the scalar `100.0` should be measured in the discrete metric as well.

See the [documentation on metrics](@ref) for more detailed information on how we measure distance.

## Containers
Our matrix/vector types have some more parameters than native julia matrices. They look like this:
```
Matrix<n: N, c: C>[m × n]{T}
Vector<n: N, c: C>[m]{T}
```
The types know about:
- the metric that is used to measure distance between two instances (`N` is one of `L1, L2, LInf`)
- if their rows are bounded by `1` in some norm (`C` is one of `L1, L2, LInf, U` where `U` means unbounded row norm)
- what dimension they have (`m × n` resp. `n`)
- and what type their entries have (`T`)

You can specify the norm and element type of a matrix or vector using the type functions [`MetricMatrix`](@ref) and [`MetricVector`](@ref). The dimensions and row clip parameter are inferred.

See the [documentation on metrics](@ref) for more detailed information on how we measure distance.

### Special types for `Flux.jl`
For compatibility with [`Flux.jl`](https://fluxml.ai/Flux.jl/stable/), we have two special types:
- `DMModel[m]` is the type of `Flux.jl` models with `m` parameters.
- `DMGrads<n:N, c:C>[m]{T}` is the type of [`Zygote.jl`](https://fluxml.ai/Zygote.jl/stable/) gradients measured in metric `N`, with bounded `C`-norm and `m` parameters of type `T`

See the [example implementation of DP-SGD](@ref) for usage examples of these.

## Subtyping
The subtyping hierarchy builds on the usual julia type hierarchy. That is, we have

```Integer ⊑ Real```

and

```T ⊑ Any```

for all types `T`, as well as
```Tuple{τ₁,...} ⊑ Tuple{τ'₁,...}```
if and only if `τ₁⊑ τ'₁...`. This extends to our static numbers, i.e.
```τ₁[s]  ⊑ τ₂```
```τ₁[s]  ⊑ τ₂[s]```
if and only if `τ₁  ⊑ τ₂`, as well as to our custom container types, i.e.
```DMContainer<kind: K, n: N, c: C>[s]{τ₁} ⊑ DMContainer<kind: K, n: N, c: C>[s]{τ₂}```
if and only if `τ₁  ⊑ τ₂`.

Note that there are no other subtyping relations between our types. In particular, `Real` and `Data` are not in any subtyping relation, and there are no subtyping relations between functions.

