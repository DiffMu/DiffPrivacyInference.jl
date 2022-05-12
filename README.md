[![Build Status](https://travis-ci.com/DiffMu/DiffPrivacyInference.jl.svg?branch=main)](https://travis-ci.com/DiffMu/DiffPrivacyInference.jl)
[![](https://img.shields.io/badge/docs-stable-blue.svg)](https://DiffMu.github.io/DiffPrivacyInference.jl/stable)


**DISCLAIMER**: Even though we analyzed the theoretical framework which we are basing our privacy guarantees on, and extensively tested the implementation, we cannot entirely exclude the possibility of bugs or of privacy risks in a program which our typechecker claims to be safe. Use at your own risk. Feedback and questions are very welcome.

The goal of this project is to create a type checker which can automatically analyze [Julia](https://julialang.org/) programs for [(ε, δ)-differential privacy](https://en.wikipedia.org/wiki/Differential_privacy) guarantees.

This software is capable of inferring the ε and δ parameters of (ε, δ)-differentially private programs written in Julia, as long as they use only [supported syntax](https://diffmu.github.io/DiffPrivacyInference.jl/dev/full_reference/syntax/) and our builtin [primitive privacy mechanisms](https://diffmu.github.io/DiffPrivacyInference.jl/dev/tutorial/02_privacy_functions/). Its main purpose is enabling the implementaion of novel private mechanisms, using primitives whose privacy guarantees are known from literature, without having to make manual proofs about their properties.

We provide a verifiable implementation of [Differentially Private Stochastic Gradient Descent](https://arxiv.org/abs/1607.00133) using the [Flux.jl](https://github.com/FluxML/Flux.jl) machine learning framework. Head to the [tutorial](https://diffmu.github.io/DiffPrivacyInference.jl/dev/tutorial/03_flux_dp/) for a walkthrough, and check out the [code](https://github.com/DiffMu/DiffPrivacyInference.jl/tree/main/example/flux_dp)!

Our type inference algorithm for Julia code is based on the [Duet type system](https://arxiv.org/abs/1909.02481) and the corresponding [Haskell implementation](https://github.com/uvm-plaid/duet). The main part of our analysis is written in Haskell as well, head to [our Haskell repo](https://github.com/DiffMu/DiffPrivacyInferenceHs).

If you have any questions, feel free to get in touch :)

## Installation

To use this package, you will need to have [the Haskell Tool Stack](https://docs.haskellstack.org/en/stable/README/#how-to-install) installed on your system, as the main part of the typechecker is implemented in Haskell. Once this is done, install the Julia package from the REPL:
```julia
] add https://github.com/DiffMu/DiffPrivacyInference.jl
```

To install from source, head to the [installation instructions](https://diffmu.github.io/DiffPrivacyInference.jl/dev/getting_started/installation/) in our documentation.

## Getting started

For a short guide on how to write typecheckable code as well as example usage, head to the [quick guide](https://diffmu.github.io/DiffPrivacyInference.jl/dev/getting_started/quick_guide/) in our documentation.

