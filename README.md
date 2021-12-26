# Verified Differential Privacy for Julia
[![Project Status: WIP – Initial development is in progress, but there has not yet been a stable, usable release suitable for the public.](https://www.repostatus.org/badges/latest/wip.svg)](https://www.repostatus.org/#wip)
[![Build Status](https://travis-ci.com/DiffMu/DiffPrivacyInference.jl.svg?branch=main)](https://travis-ci.com/DiffMu/DiffPrivacyInference.jl)
[![codecov](https://codecov.io/gh/DiffMu/DiffPrivacyInference.jl/branch/main/graph/badge.svg?token=AFOE37PKNT)](https://codecov.io/gh/DiffMu/DiffPrivacyInference.jl)
[![](https://img.shields.io/badge/docs-dev-blue.svg)](https://DiffMu.github.io/DiffPrivacyInference.jl/dev)

The goal of this project is to create a type checker which can automatically analyze [Julia](https://julialang.org/) programs with respect to [differential privacy](https://en.wikipedia.org/wiki/Differential_privacy) guarantees.
 
This is a work in progress. We are implementing a type inference algorithm for Julia code based on the [Duet type system](https://arxiv.org/abs/1909.02481) and the corresponding [haskell implementation](https://github.com/uvm-plaid/duet).

Currently, we can do the following:
- Parse a subset of Julia code into a representation suitable for type checking. We support arithmetics on Real, Integer and Matrix types, conditionals, procedural variable and function declarations, loops over integer ranges, tuples, limited indexing of Vectors and Matrices, and multiple dispatch. We also support a very limited usage of constructs from the [Flux.jl](https://github.com/FluxML/Flux.jl) machine learning framework and provide a way to use certain functions that cannot be typechecked.
- Infer the [sensitivity](https://en.wikipedia.org/wiki/Differential_privacy#Sensitivity) or [(ε, δ)-differential privacy](https://arxiv.org/abs/1203.3453) w.r.t. the inputs of the functions in the parsing results.

Next up is smoothing out the integration into Flux.jl and then implementing and verifying some more standard differentially private mechanisms. Further, we have to provide a convenient user interface and installation process.


## Installation

We have moved most of the typecheker implementation to haskell, callable from the `julia` REPL via an FFI. For now, please head to the repository of the [haskell part of the project](https://github.com/DiffMu/DiffPrivacyInferenceHs) for installation instructions of the current development state. Once the typechecker is in a usable state, we will provide a simple installation procedure using the `julia` package manager.


## How to write checkable code

### Supported `julia` syntax

We cannot check arbitrary `julia` code, partly because we need to do some more work, partly because some constructs available in `julia` would render static analysis impossible. Here's a list of language features we support at the moment:

- Function definitions using `function`, one-line definitions and anonymous functions, as well as function application.
- Multiple dispatch on `Number, Integer, Real, Matrix{T}, Tuple{T}` and our special types (see below). Finer types are not allowed.
- Some arithmetics on numbers, vectors and matrices, as well as indexing matrix rows using `m[i,:]` and vector indexing using `v[i]`
- Type annotations on function variables, like in `f(x::Integer) = x + x`
- Variable and tuple assignments like `x = 1` or `(a,b,c) = t`
- Loops over integer ranges, where the loop head must be of the form `for i in 1:2:n`.
- `if`, `ifelse` and `else` statements where the condition can be an integer or of the form `x == y`.
- `import`, which will just be ignored by the type checker. You can use stuff from imported modules, but only inside black boxes (see below).
- `include` statements. The typechecker will load the included file and check it as well.

### Forbidden things

There are a few things you are not allowed to do (which the typechecker will tell you if you try). Namely:

- Your code has to be valid julia code. If it is not, do not expect the typechecker to always tell you so or produce reasonable results.
- You cannot mutate variables that were declared in an outer scope. For example, the following is illegal:
  ```
  function foo()
     x = 10
     function bar()
        x = 100
        x
      end
      bar()
   end
   ```
- If you want to use a variable, you have to define it first. E.g. the following is valid julia code but illegal:
  ```
  function foo()
     bar() = a
     a = 100
     bar()
  end
  ```
- For now, it is not permitted to reassign variables, hence the following is forbidden:
  ```
  function foo()
     x = 1
     y = x+2
     x = 2
     y
  end
  ```
- Recursion is not supported. Do not yet expect legible error messages if you use it...
- Assignments within assignments (like `x = y = 10`) are forbidden. Why would you, anyways.

### Special Types

We have two special types, `DMModel` for wrapping `Flux.jl` models and `DMGrads` for wrapping `Zygote.jl` gradients. If you want to typecheck code that uses an object like that, you need to wrap it in our types so we can ensure you don't do anything illegal with it. See the type documentation in the REPL and the `flux_dp.jl` example in `test/flux_dp` for usage.

### Special annotations

In general, it is a good idea to annotate all function arguments as it will help the typechecker give you an inference result that is not too pessimistic and has a minimum number of unresolved constraints. There is, however, some special annotations that you should make to get a proper result:

- Our typechecker can infer the sensitivity or the (ε, δ)-differential privacy of function arguments. For every function you write, you have to tell the typechecker whether you expect it to be differentially private by annotating the function head using `function foo(x) :: Priv()`. If you don't annotate, the typechecker will assume that the function is not DP, which might worsen the inferred bounds if it's not true.
- For differentially private functions, you can tell the typechecker which of its arguments are actually interesting. For example, when training a model to some data with some learning rate, you are interested in the privacy of the input data, not the input model. You would then write your function signature like this: `function train(data, model::NoData(), eta::NoData(Real))`. This allows the typecheker to infer tighter bounds by setting the privacy of non-interesting arguments to infinity in certain tradeoff situations.
- Differentially private variables in function bodies have the nice property of [robustness to post-processing](https://en.wikipedia.org/wiki/Differential_privacy#Robustness_to_post-processing).If you want to make use of it, you need to annotate those variables to be robust. This you do upon assignment by saying `g :: Robust() = gaussian_mechanism(s,e,d,gg)`
- If you want to use a function that contains unsupported `julia` syntax, like using qualified names from imported modules, you can make them a *black box* by annotating the function head using `function foo(x) :: BlackBox()`. You can only define a black box on the toplevel scope of what you want to typecheck (not inside a function, e.g.). Also, black boxes cannot have multiple methods. The typechecker will ignore a black box' function body and assign infinite sensitivity to all arguments. _Warning_: We cannot control what you do inside a black box, but the one thing that you really should not do is *mutate the arguments*. If you do that, the typechecking result will be invalid even though the typechecking code terminates without complaints.


## Usage examples

To infer the sensitivity of a simple function, use `typecheck_hs_from_string`:

```

julia> typecheck_hs_from_string("function foo(x::Matrix{Real}, y::Matrix{Real})
                                    2*x - y
                                 end")
```
The result will be printed in the REPL:
```
---------------------------------------------------------------------------
Type:
Fun([([NoFun(Matrix<n: τ_10, c: τ_8>[s_5 × s_4](Num(τ_44[--]))) @ 2.0,NoFun(Matrix<n: τ_10, c: τ_11>[s_5 × s_4](Num(τ_38[--]))) @ 1] -> NoFun(Matrix<n: τ_10, c: U>[s_5 × s_4](Num(τ_40[--])))) @ Just [Matrix{Real},Matrix{Real}]])
---------------------------------------------------------------------------
Constraints:
   - top:
constr_25 : [final,worst,global,exact,special] IsSupremum (τ_44,τ_38) :=: τ_40
   - others:
[]
()
```
It says the checked code is a function (`Fun(...)`) of two arguments which is 2-sensitive in its first and 1-sensitive in its second input (indeicated by the `@ 2.0` annotation). The imput types both need to be matrices of matching dimensions (the variables `s_5` and `s_4`) whose elements are of some numeric type (`Num(...)`). But that is not quite all, as there is more output:
```
- constraints:
   - top:
constr_25 : [final,worst,global,exact,special] IsSupremum (τ_44,τ_38) :=: τ_40
```
It is the list of constraints on the type variables that occur in the result type that the typechecker could not resolve. In this case it tells us that the element type of the output matrix, `τ_40`, is not just any type, but the supremum of the input matrices' element types `τ_44` and `τ_38`.


For a full-blown example head to the [`test/flux_dp`](https://github.com/DiffMu/DiffPrivacyInference.jl/tree/main/test/flux_dp) folder, where you will find a differentially private implementation of a gradient descent algorithm that is capable of learning to classify handwritten numbers.
