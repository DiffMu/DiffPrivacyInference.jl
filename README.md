# Verified Differential Privacy for Julia
[![Project Status: WIP – Initial development is in progress, but there has not yet been a stable, usable release suitable for the public.](https://www.repostatus.org/badges/latest/wip.svg)](https://www.repostatus.org/#wip)
[![Build Status](https://travis-ci.com/DiffMu/DiffPrivacyInference.jl.svg?branch=main)](https://travis-ci.com/DiffMu/DiffPrivacyInference.jl)
[![codecov](https://codecov.io/gh/DiffMu/DiffPrivacyInference.jl/branch/main/graph/badge.svg?token=AFOE37PKNT)](https://codecov.io/gh/DiffMu/DiffPrivacyInference.jl)
[![](https://img.shields.io/badge/docs-dev-blue.svg)](https://DiffMu.github.io/DiffPrivacyInference.jl/dev)

The goal of this project is to create a type checker which can automatically analyze [Julia](https://julialang.org/) programs with respect to [differential privacy](https://en.wikipedia.org/wiki/Differential_privacy) guarantees.
 
This is a work in progress. We intend to implement a type inference algorithm for Julia code based on the [Duet type system](https://arxiv.org/abs/1909.02481) and the corresponding [haskell implementation](https://github.com/uvm-plaid/duet).

Currently, we can do the following:
- Parse a very basic subset of Julia code into a representation suitable for type checking. We support arithmetics on Real and Integer types, conditionals, procedural variable and function declarations and multiple dispatch.
- Infer the [sensitivity](https://en.wikipedia.org/wiki/Differential_privacy#Sensitivity) w.r.t. the inputs of the functions in the parsing results. This is an important first step towards the inference of differential privacy bounds.

Next up is adding support for more Julia language constructs and data types to the parser, so we can handle e.g. vector and matrix operations, loops and conditionals. Further, we will implement and verify some standard differentially private mechanisms and provide a convenient interface.


## Installation

It is advisable, for now, to avoid precompilation and optimization by starting Julia with
```
julia -O0 --compile=min
```

Then install the package with
```julia
] add "https://github.com/DiffMu/DiffPrivacyInference.jl"
```

Start using it with
```julia
julia> using DiffPrivacyInference
```

## Examples

We can parse Julia code from strings and do type inference:
```julia
julia> pretty_print(infer_sensitivity_from_string("
                              f(x::Integer) = 23*x
                    "))
"(Int @(23)) ==> Int"
```
The output tells us that the input expression is a one-argument function mapping an integer to another integer with sensitivity 23.

Currently we can only do function and variable declaration, conditionals, multiple dispatch, and basic arithmetics on real and integer numbers. Here's a more complicated example:
```julia
julia> pretty_print(infer_sensitivity_from_string("
                              function test(x::Integer, y)
                                f(x) = 23*(x + y)
                                z = 1
                                g(x) = z*x
                                z = 42/23
                                if z == 1
                                    return 3
                                else
                                    return f(g(x))
                                end
                              end
                     "))
"(Int @(42.0), tvar.op_arg_23 @(23)) ==> tvar.sup_31"
```
The output tells us that this is a two-argument function which is 42-sensitive in its first argument, which is of type Integer, and 23-sensitive in its second argument, whose type (like the function's return type) could not be inferred.

We can analyse entire files using ```infer_sensitivity_from_file```, also resolving includes. Running the inference algorithm like this will result in the type of the last statement in the file, i.e. of the thing that running all commands in the file would entail.
