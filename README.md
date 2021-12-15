# Verified Differential Privacy for Julia
[![Project Status: WIP – Initial development is in progress, but there has not yet been a stable, usable release suitable for the public.](https://www.repostatus.org/badges/latest/wip.svg)](https://www.repostatus.org/#wip)
[![Build Status](https://travis-ci.com/DiffMu/DiffPrivacyInference.jl.svg?branch=main)](https://travis-ci.com/DiffMu/DiffPrivacyInference.jl)
[![codecov](https://codecov.io/gh/DiffMu/DiffPrivacyInference.jl/branch/main/graph/badge.svg?token=AFOE37PKNT)](https://codecov.io/gh/DiffMu/DiffPrivacyInference.jl)
[![](https://img.shields.io/badge/docs-dev-blue.svg)](https://DiffMu.github.io/DiffPrivacyInference.jl/dev)

The goal of this project is to create a type checker which can automatically analyze [Julia](https://julialang.org/) programs with respect to [differential privacy](https://en.wikipedia.org/wiki/Differential_privacy) guarantees.
 
This is a work in progress. We attempt to implement a type inference algorithm for Julia code based on the [Duet type system](https://arxiv.org/abs/1909.02481) and the corresponding [haskell implementation](https://github.com/uvm-plaid/duet).

Currently, we can do the following:
- Parse a subset of Julia code into a representation suitable for type checking. We support arithmetics on Real, Integer and Matrix types, conditionals, procedural variable and function declarations, loops over integer ranges, tuples, limited indexing of Vectors and Matrices, and multiple dispatch. We also support a very limited usage of constructs from the [Flux.jl](https://github.com/FluxML/Flux.jl) machine learning framework and provide a way to use certain functions that cannot be typechecked.
- Infer the [sensitivity](https://en.wikipedia.org/wiki/Differential_privacy#Sensitivity) or [(ε, δ)-differential privacy](https://arxiv.org/abs/1203.3453) w.r.t. the inputs of the functions in the parsing results.

Next up is smoothing out the integration into Flux.jl and then implementing and verifying some more standard differentially private mechanisms. Further, we have to provide a convenient user interface and installation process.


## Installation

We have moved most of the typecheker implementation to haskell, callable from the `julia` REPL via an FFI. For now, please head to the repository of the [haskell part of the project](https://github.com/DiffMu/DiffPrivacyInferenceHs) for installation instructions of the current development state. Once the typechecker is in a usable state, we will provide a simple installation procedure using the `julia` package manager.


## Usage examples

To infer the sensitivity of a simple function, use `typecheck_hs_from_string`:

```
julia> typecheck_hs_from_string("function foo(x::Integer, y::Real)
                                    x + 2*y
                                 end")
```
The result will be printed in the REPL:
```
Result: (Fun([([NoFun(Num(Int[--])) @ 1,NoFun(Num(τ_25[--])) @ 2.0] -> NoFun(Num(τ_25[--]))) @ Just [Integer,Real]]),
State:
- watcher: NotChanged
- messages: (hidden)

Meta:
- sens vars: []
- type vars: [τ_25 : BaseNum, τ_8 : *]
- sens subs:   η_1 := 1, η_0 := 1, η_3 := 2.0, η_2 := 0
- type subs:   τ_17 := τ_25[--], τ_11 := τ_25[--], τa_1 := Num(τ_25[--]), τr_2 := Num(τ_25[--]), τ_16 := Int[--], τ_20 := τ_25, τ_9 := Num(τ_25[--]), τ_10 := Num(Real[--]), τa_0 := Num(Int[--]), τr_6 := Num(τ_25[--]), τa_5 := Num(τ_25[--]), τ_15 := Int[--], τ_21 := Real, τ_3 := NoFun(Num(Int[--])), τ_24 := Int, τa_4 := Num(Int[2.0]), τ_14 := Num(Int[--]), τ_22 := Int, τ_19 := τ_25, τ_7 := NoFun(Num(τ_25[--])), τ_13 := Num(Int[--]), τ_18 := τ_25, τ_23 := Int, τ_12 := Real[--]
- fixed TVars: 
- constraints:
   - top:
constr_11 : [final,worst,global,exact,special] IsLessEqual (τ_25,Real)
   - others:
[]

Types:
Left 
)
()
```
That's a lot of informaion, but the most interesting thing is this part:
```
Result: (Fun([([NoFun(Num(Int[--])) @ 1,NoFun(Num(τ_25[--])) @ 2.0] -> NoFun(Num(τ_25[--]))) @ Just [Integer,Real]]),
```
It says the function is 1-sensitive in its first and 2-sensitive in its second input. The fist input needs to be an integer, and the second type is variable but the output type will be the same as that of the second argument. But that is not quite all, the second interesting part is this:
```
- constraints:
   - top:
constr_11 : [final,worst,global,exact,special] IsLessEqual (τ_25,Real)
```
It is the list of constraints on the type variables that occur in the result type that the typechecker could not resolve. In this case it tells us that the type variable `τ_25` can in fact not be any type, but needs to be a subtype of `Real`.


For a full-blown example head to the `test/flux_dp` folder, where you will find a differentially private implementation of a gradient descent algorithm that is capable of learning to classify handwritten numbers.
