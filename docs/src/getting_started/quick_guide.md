
# Quick Guide

This program performs static analysis of your julia code to automatically infer [sensitivity](https://en.wikipedia.org/wiki/Differential_privacy#Sensitivity)/[(ε, δ)-differential privacy](https://en.wikipedia.org/wiki/Differential_privacy) properties of your functions. 

## Supported `julia` syntax

We cannot check arbitrary `julia` code, instead we restrict to a subset of the language which is suited for analysis. See the documentation section on [supported syntax](@ref syntax) to learn how to write programs that can be checked.


## Interpreting typechecking results

The results of typechecking can be a bit involved, so make sure you have internalized the [definition of differential privacy](https://en.wikipedia.org/wiki/Differential_privacy#Definition_of_%CE%B5-differential_privacy). The analysis result will be presented to you as a [type](@ref types) that contains sensitivity/privacy annotations for yoyur function's arguments, together with a list of [constraints](@ref constraints) on the variables that appear in the type. Head to the respective documentation section to learn how to read those.
Also note that sensitivity/differential privacy is a property of a function between two metric spaces and what metric you use is important. Head to the page on [measuring distance](@ref) for information.


## Usage examples

To infer the sensitivity of a simple function, use [`typecheck_from_string`](@ref):
```julia
julia> typecheck_from_string("
       module Foo
       function foo(x::Matrix{<:Real}, y::Matrix{<:Real})
          2*x - y
       end
       end")
```
The result will be printed in the REPL:
```julia
---------------------------------------------------------------------------
Type:
{
|   - Matrix<n: τ₇, c: τ₈>[s₅ × s₄]{τ₄₆}
|       @ 2.0
|   
|   - Matrix<n: τ₇, c: τ₁₁>[s₅ × s₄]{τ₅₂}
|       @ 1
|   --------------------------
|    -> Matrix<n: τ₇, c: U>[s₅ × s₄]{τ₆₁}
}

---------------------------------------------------------------------------
```
It says the checked code is a function ([`Fun(...)`](@ref types)) of two arguments which is 2-sensitive in its first and 1-sensitive in its second input (indeicated by the `@ 2.0` annotation). The imput types both need to be matrices of matching dimensions (the variables `s₅` and `s₄`) whose elements are of some types (`τ₄₆` and `τ₅₂`). But that is not quite all, as there is more output:
```julia
Constraints:
constr₅₅ : Type τ₆₁ is the supremum of types τ₅₂ and τ₄₆]
```
It is the list of [constraints](@ref) on the type variables that occur in the result type that the typechecker could not resolve. In this case it tells us that the element type of the output matrix, `τ₆₁`, is not just any type, but the supremum of the input matrices' element types `τ₄₆` and `τ₅₂`.


For a full-blown example head to the [example privately training an neural network](@ref fluxdp), where you will find a differentially private implementation of a gradient descent algorithm that is capable of learning to classify handwritten numbers.


