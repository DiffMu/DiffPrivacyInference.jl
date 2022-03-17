
# Overview

The goal of this project is to create a type checker which can automatically analyze [Julia](https://julialang.org/) programs with respect to [differential privacy](https://en.wikipedia.org/wiki/Differential_privacy) guarantees.
 
This is a work in progress. We are implementing a type inference algorithm for Julia code based on the [Duet type system](https://arxiv.org/abs/1909.02481) and the corresponding [haskell implementation](https://github.com/uvm-plaid/duet).

On this page, you can find [installation instructions](https://diffmu.github.io/DiffPrivacyInference.jl/dev/getting_started/installation/) as well as a [quick guide](https://diffmu.github.io/DiffPrivacyInference.jl/dev/getting_started/quick_guide/) and examples that should enable you to write your first typecheckable code. The reference documentation is not complete yet, you can however access documentation for out [builtin functions](https://diffmu.github.io/DiffPrivacyInference.jl/dev/full_reference/builtins/).
