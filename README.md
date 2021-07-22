# Verified Differential Privacy for Julia
[![Project Status: WIP – Initial development is in progress, but there has not yet been a stable, usable release suitable for the public.](https://www.repostatus.org/badges/latest/wip.svg)](https://www.repostatus.org/#wip)
[![Build Status](https://travis-ci.com/DiffMu/DiffPrivacyInference.jl.svg?branch=main)](https://travis-ci.com/DiffMu/DiffPrivacyInference.jl)
[![codecov](https://codecov.io/gh/DiffMu/DiffPrivacyInference.jl/branch/main/graph/badge.svg?token=AFOE37PKNT)](https://codecov.io/gh/DiffMu/DiffPrivacyInference.jl)
[![](https://img.shields.io/badge/docs-dev-blue.svg)](https://DiffMu.github.io/DiffPrivacyInference.jl/dev)

The goal of this project is to create a type checker which can automatically analyze [Julia](https://julialang.org/) programs with respect to [differential privacy](https://en.wikipedia.org/wiki/Differential_privacy) guarantees.
 
This is a work in progress. We intend to implement a type inference algorithm for Julia code based on the [Duet type system](https://arxiv.org/abs/1909.02481) and the corresponding [haskell implementation](https://github.com/uvm-plaid/duet).

Currently, we can do the following:
- Parse a basic subset of Julia code into a representation suitable for type checking. We support arithmetics on Real and Integer types, conditionals, procedural variable and function declarations, loops over integer ranges, tuples, conditionals and multiple dispatch.
- Infer the [sensitivity](https://en.wikipedia.org/wiki/Differential_privacy#Sensitivity) w.r.t. the inputs of the functions in the parsing results. This is an important first step towards the inference of differential privacy bounds.

Next up is adding support for more Julia language constructs and data types to the parser, and improving the inference results. Further, we will implement and verify some standard differentially private mechanisms and provide a convenient interface.


## Installation

We have moved most of the typecheker implementation to haskell, callable from the `julia` REPL via an FFI. For now, please head to the repository of the [haskell part of the project](https://github.com/DiffMu/DiffPrivacyInferenceHs) for installation instructions of the current development state. Once the typechecker is in a usable state, we will provide a simple installation procedure using the `julia` package manager.
