
# Overview

The type system is based on [this paper](https://arxiv.org/abs/1909.02481), which presents duet, a language with inference rules for (ε,δ)-privacy guarantees.

Basically, the DiffPrivacyInference.jl typechecker infers the privacy of julia code by applying the rules of duet.
But this cannot be done directly, as the duet language is based on a pure lambda calculus,
without the concept of mutating objects in memory. Yet mutation is an inescapable fact of performant julia code,
which means that in order to do its job, the typechecker has to convert mutating julia code into a pure functional language first.
We call this process "demutation".

But we cannot support typechecking of all possible julia programs. In particular, julia's behaviour of capturing variables from outer scopes in local functions is
very difficult to statically analyze. Because of this, the typechecker also makes sure that some relatively strict scoping rules are followed.

A further difference between duet and julia which has to be bridged is that duet actually consists of two languages (the sensitivity and the privacy language),
mutually containing each other; there are explicit terms for switching from one to the other. In order to remain as close to canonical julia code as possible, we include
a "color"-inference stage in the typechecker, which infers whether statements are meant to be interpreted in the privacy or in the sensitivity fragment of duet.

The typechecking stages are executed in the following order:
 1. [demutation](@ref demutation) & [scope checking](@ref scoping_rules)
 2. color inference
 3. [type inference](@ref types)


