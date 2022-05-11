# Verified Differential Privacy for Julia
[![Build Status](https://travis-ci.com/DiffMu/DiffPrivacyInference.jl.svg?branch=main)](https://travis-ci.com/DiffMu/DiffPrivacyInference.jl)
[![](https://img.shields.io/badge/docs-dev-blue.svg)](https://DiffMu.github.io/DiffPrivacyInference.jl/dev)

The goal of this project is to create a type checker which can automatically analyze [Julia](https://julialang.org/) programs with respect to [differential privacy](https://en.wikipedia.org/wiki/Differential_privacy) guarantees.
 
This is a work in progress. We are implementing a type inference algorithm for Julia code based on the [Duet type system](https://arxiv.org/abs/1909.02481) and the corresponding [haskell implementation](https://github.com/uvm-plaid/duet).

Currently, we can do the following:
- Parse a subset of Julia code into a representation suitable for type checking. We support arithmetics on Real, Integer and Matrix types, conditionals, procedural variable and function declarations, loops over integer ranges, tuples, limited indexing of Vectors and Matrices, limited use of mutable data structures, and multiple dispatch. We also support a very limited usage of constructs from the [Flux.jl](https://github.com/FluxML/Flux.jl) machine learning framework and provide a way to still use functions whose privacy guarantees we are not able to infer.
- Infer the [sensitivity](https://en.wikipedia.org/wiki/Differential_privacy#Sensitivity) or [(ε, δ)-differential privacy](https://arxiv.org/abs/1203.3453) w.r.t. the inputs of the functions in the parsing results.

We are currently working on providing more convenient user experience and documentation.

## Installation

We have moved most of the typecheker implementation to haskell, callable from the `julia` REPL via an FFI. For now, please head to the repository of the [haskell part of the project](https://github.com/DiffMu/DiffPrivacyInferenceHs) for installation instructions of the current development state. Once the typechecker is in a usable state, we will provide a simple installation procedure using the `julia` package manager.



## Getting started

For a short guide on how to write typecheckable code as well as example usage, head to the [quick guide](https://diffmu.github.io/DiffPrivacyInference.jl/dev/getting_started/quick_guide/) in our documentation.

