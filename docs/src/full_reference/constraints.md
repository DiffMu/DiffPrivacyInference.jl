
# [Constraints](@id constraints)
The typechecker gives you the result of the privacy analysis of your julia code in form of [Types](@ref types) that usually contains variables of two kinds, namely type variables and number variables. The analysis result holds as long as you choose the values for these variables in a way that does not violate any of the constraints that also belong to the typechecking result. There is a variety of constraints, here's a list:

## Equality and inequality
### `IsEqual`
```
constr : constr  :  τ₁ and  τ must be equal
```
The variables must be equal, i.e. describe the same type (for type variables) or have the same value (for number variables).

### `IsLess` and `IsLessEqual`
```
constr : constr₁  : eps < 1
constr₂ : 0 ≤ eps
```
The (numeric) variable `eps` must be in `[0,1)`.


```
constr : τ ⊑ Real
```
The type variable `τ` must be a [subtype](https://diffmu.github.io/DiffPrivacyInference.jl/dev/full_reference/types/#Subtyping) of `Real`.


### `IsSupremum` and `IsInfimum`
```
constr : constr : Type τ₁ is the supremum of types τ₂ and Integer
constr : Type τ₃ is the infimum of types τ₄ and Real
```
Suprema and infima w.r.t. the [subtyping hierarchy](https://diffmu.github.io/DiffPrivacyInference.jl/dev/full_reference/types/#Subtyping). That is, `τ₁` is the type that is lowest in the subtyping hierarchy such that `τ₂ ⊑ τ₁` and `Integer ⊑ τ₁`

## Const/NonConst
We support [static number types](@ref types), so we need constraints on whether a number type is static or not.

### `MakeConst`
```
If type τ is numeric or a tuple, it can become static
```
All numeric types in `τ` will be set to static once they are known.

### `MakeNonConst`
```
All Numeric types in τ will be set non-static
```
All numeric types in `τ` will be set to non-static once they are known.

### `UnifyWithConstSubtype`
```
constr : constr : Types τ₁ and τ₂ are equal except for static-ness, where the fist is a subtype of the second
```
In case `τ₁ = τ[s ©]` is a [static number](@ref types) for some `s`, we allow [`τ₁ ⊑ τ₂`](https://diffmu.github.io/DiffPrivacyInference.jl/dev/full_reference/types/#Subtyping). Otherwise, it is `τ₁ = τ₂`.

## Choices/Mulitple Dispatch (`IsChoice`)
If the julia type information is not sufficient to resolve multiple dispatch, you end up with constraints instead. Behold the following example, where the function `f` has two methods, but in the call to `f` that happens withing `g`, it is not yet clear which of the methods will be called. Annotating the argument of `g` would have made it possible to resolve the constraint, so it is advisable to add annotations where possible.
```
julia> typecheck_from_string("module L
       f(x::Matrix) = x+x
       f(x::Integer) = 2*x
       g(x) = f(x)
       end")

---------------------------------------------------------------------------
Type:
{
|   (τ₁₃ @ s₈) -> τ₁₄
}

---------------------------------------------------------------------------
Constraints:
constr : Function types 
  {
  |   (τ₁₃ @ s₈) -> τ₁₄
  }
 are required to exist among the following choices:
  - julia signature [Matrix{<:Any}]: 
    {
    |   - Matrix<n: τ₈, c: τ₉>[s₅ × s₄]{τ₅₁}
    |       @ 2.0
    |   --------------------------
    |    -> Matrix<n: τ₈, c: U>[s₅ × s₄]{τ₅₁}
    }
  
  - julia signature [Integer]: 
    {
    |   (Integer @ 2.0) -> Integer
    }
```


## Arithmetic operations (`IsTypeOpResult`)
Arithemtic operations like addition and multiplication have different sensitivities depending on the types of the operand. On the one hand, arithmetics on matrices behaves different from that on numbers, on the other hand we support [static types](@ref types) which behave like constant numbers. For example, the expression `s * x` is infinitely sensitive in both `s` and `x`, but if we assume `s` to be of static type, it is 0-sensitive in `s` and `s`-sensitive in `x`. This results in a constraint if the static-ness of the operands is unknown:
```
constr : Binary operation * on (τ_s @ s₄, τ_x @ s₁) with result type τ₂
```
Scalars `s₄` and `s₁` denote the sensitivities of the operands and will be set once the static-ness of `τ_s` and `τ_x` is determined. The possible operations are `+,-,*,/,mod,==,ceil`. Refer to page 36 of the [duet paper](https://arxiv.org/abs/1909.02481) for reference on the sensitivity of these operations.

## Julia Types
### `IsJuliaEqual`
```
constr : Types τ₁ and τ₂ describe the same julia type
```
As you can read in the documentation on our [types](@ref types), in addition to the supported julia types we use some refinements. For example, our function types contain information about argument and return types (as well as sensitivity/privacy, of course), while the only type julia provides for functions is `Function`. Other examples are static number types, container types that have information about dimension and metric. This constraint requires the julia representation of two types to be indistinguishable, while they might not be equal.

### `IsFunction`
```
Type τ is a k-function
```
`τ` must be some function type of kind `k` where `k` is either `SensitivityK` or `PrivacyK` (not a black box function, though).

## Loops (`IsLoopResult`)
```
constr : Sensitivities (s₃, s₄, s₅) are dependant on whether number of iterations in τ₁:τ₂:τ₃ is static. Loop body has sensitivity s₉
```
If a loop has a static number of iterations, we can give better sensitivity bounds. If the static-ness remains unknown, you end up with a constraint like this. Page 42 of the [duet paper](https://arxiv.org/abs/1909.02481) has detailed rules on how the sensitivities will be resolved in case of static/non-static number of iterations. If you know the number of iterations is static, consider [annotating](@ref annotations) the relevant variables to avoid unresolved constraints of this kind.

## Additive noise mechanisms (`IsAdditiveNoiseResult`)
```
Type τ₁ is the result of an additive noise mechanism executed on τ₂
```
We provide additive noise mechanisms on numbers and matrices, where they result in different differential privacy. As long as the input type is not known, this constraint remains.

## Black Boxes
### `IsBlackBox`
```
constr : Black box function τ is applied to arguments [τ₁,...] 
```
The only things the typechecker knows about [black box functions](@ref black-boxes) is their name and the julia signature of the arguments. This constraint makes sure the signature matches the types of what the function was applied to.

### `IsBlackBoxReturn`
```
constr : Type τ₁ is an argument of a black box, its sensitivity s₁ can be set accordingly
```
With some combination of input and output types of a black box, the typechecker can infer better privacy bounds. See the documentation on [black boxes](@ref black-boxes) for details.

## Container types
### `IsVecOrMat`
```
Type τ must be a vector or matrix
```
### `IsVecLike`
```
Type τ must be a vector, gradient or one-row matrix
```

### `ConversionResult`
```
constr : Converted norm n to norm m on an r-row container, incurring conversion penalty is p
```
Converting between container types measured with different metrics has effect on the sensitivity of functions. See the documentation of [container metrics](@ref measuring-distance) and page 19f of the [duet paper](https://arxiv.org/abs/1909.02481) for details.
