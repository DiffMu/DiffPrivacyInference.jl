
# Overview
## Writing checkable code
Arbitrary julia code is unlikely to be differentially private. Apart from that, there are language constructs that make automatic analysis too difficult. We hence restrict the code you can write and expect us to analyze by introducing a couple of rules:

- [Supported syntax](@ref syntax): We do not allow arbitrary julia code, partly because most of it will not be differentially private, partly because some of it makes inference very hard for us. Basic procedural code using [numbers, matrices, vectors and tuples](@ref types) is permissible, and we provide a number of [builtin functions](@ref builtins) for tasks common in differentially private programs.
- The inference result will be much better the more [type annotations](@ref annotations) you make to your function arguments and return types. Some of them are even necessary for the inference algorithm to understand what you're trying to do.
- As one might still want to use code that does not fulfil the various conditions to make inference possible, we provide a way of specifying [black box functions](@ref black-boxes) whose body will not be parsed by our software. In return, the inference algorithm makes very pessimistic assumptions about their privacy properties, so their use will likely make your results worse.
- We support a [limited way of mutating data structures in-place](@ref demutation) in order to allow for efficient large-scale computation. You can mutate vectors, matrices, gradients and models in-place using our [builtin mutating functions](@ref builtins) (look for functions whose name ends with `!`). The typechecker will do its best to tell you how to do this in a legal way.
- Our [scoping rules](@ref scoping-rules) are more strict than the regular julia ones. This includes the necessity to define all names before they are used (literally further up in the code) and to not overwrite variable names from outer scopes.

## Interpreting the results
The analysis result is presented to you in form of a [type](@ref types) together with a set of [constraints](@ref constraints) on the variables occuring in that type. To understand the result, you will have to be able to read those. There are three articles to help you with that:

- Differential privacy is defined with respect to a metric on the input and output of a function, so it is important to pay attention on how [distance is measured](@ref measuring-distance). The analysis result will contain that information, and you will need to pay close attention to understand what it really says.
- The [type](@ref types) you are presented with contains the privacy parameters that were inferred for your function, as well as argument and return types and information about the aforementioned metrics for which the parameters are valid.
- The [constraints](@ref constraints) on variables occuring in your type must all be satisfied in order for the analysis result to hold. The typechecker tries to solve as many of them as possible, and will succeed with more of them if you [annotate](@ref annotations) more of your code. The remaining ones will be displayed, and you will have to manually check that they can be fulfilled.
