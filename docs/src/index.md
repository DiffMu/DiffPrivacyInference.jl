
# Overview

The goal of this project is to create a type checker which can automatically analyze [Julia](https://julialang.org/) programs with respect to [differential privacy](https://en.wikipedia.org/wiki/Differential_privacy) guarantees.
 
This is a work in progress. We are implementing a type inference algorithm for Julia code based on the [Duet type system](https://arxiv.org/abs/1909.02481) and the corresponding [haskell implementation](https://github.com/uvm-plaid/duet).

On this page, you can find [installation instructions](@ref installation) as well as a [quick guide](@ref quick-guide) and examples that should enable you to write your first typecheckable code. See the [user reference](@ref overview) and the documentation for all [builtin functions](@ref builtins) for more.
