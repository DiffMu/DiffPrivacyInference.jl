
# [Overview](@id overview)
## Writing checkable code
Arbitrary julia code is unlikely to be differentially private. Apart from that, there are language constructs that make automatic analysis too difficult. We hence restrict the code you can write and expect us to analyze by introducing a couple of rules:

- [Supported syntax](@ref syntax): We do not allow arbitrary julia code, partly because most of it will not be differentially private, partly because some of it makes inference very hard for us. Basic functional and procedural code using [numbers, matrices, vectors and tuples](@ref types) is permissible, and we provide a number of [builtin functions](@ref builtins) for tasks common in differentially private programs.
- The inference result will be much better the more [type annotations](@ref annotations) you make to your function arguments and return types. Some of them are even necessary for the inference algorithm to understand what you're trying to do.
- As one might still want to use code that does not fulfil the various conditions to make inference possible, we provide a way of specifying [black box functions](@ref black-boxes) whose body will not be parsed by our software. In return, the inference algorithm makes very pessimistic assumptions about their privacy properties, so their use will likely make your results worse.
- We support a [limited way of mutating data structures in-place](@ref demutation) in order to allow for efficient large-scale computation. You can mutate gradients and models in-place using our [builtin mutating functions](@ref builtins) (look for functions whose name ends with `!`). The typechecker will do its best to tell you how to do this in a legal way.
- Our [scoping rules](@ref scoping-rules) are more strict than the regular julia ones. This includes the necessity to define all names before they are used (literally further up in the code) and to not overwrite variable names from outer scopes.

## Interpreting the results
The analysis result is presented to you in form of a [type](@ref types) together with a set of [constraints](@ref constraints) on the variables occuring in that type. To understand the result, you will have to be able to read those. There are three articles to help you with that:

- Differential privacy is defined with respect to a metric on the input and output of a function, so it is important to pay attention on how [distance is measured](@ref measuring-distance). The analysis result will contain that information, and you will need to pay close attention to understand what it really says.
- The [type](@ref types) you are presented with contains the privacy parameters that were inferred for your function, as well as argument and return types and information about the aforementioned metrics for which the parameters are valid.
- The [constraints](@ref constraints) on variables occuring in your type must all be satisfied in order for the analysis result to hold. The typechecker tries to solve as many of them as possible, and will succeed with more of them if you [annotate](@ref annotations) more of your code. The remaining ones will be displayed, and you will have to manually check that they can be fulfilled.

## Some warnings
There are some things the typechecker cannot do for you. You have to take care of these yourself, so read this carefully!

- The analysis result is only valid for the source code of the module that you checked. What you do outside of that is your own responsibility. In particular, you will want to handle any sensitive data outside of that scope. You will have to make sure that
    - you call the function you inferred to be private in the correct way. The analysis result is only valid for the input types that are presented to you there. If you input any other types, the warranty is voided without you getting any warning whatsoever.
    - you handle your data in a way that does not disclose it. The result of a (properly made) function call to a verified function will ensure differential privacy for your data, but what you do after having made that call is your own responsibility.
- Throughout our checking we assume that what you gave us is valid julia code. Hence, our result is only valid if your code can run without error.
- [There are known vulnerabilities of floating point implementations of differentially private mechanisms.](@ref floats). We did what we could to mitigate some of them, but some are beyond the scope of this project. Be aware of that!
- We do not support recursion, but we cannot detect all cases of it so we won't be able to warn you about them. Don't write recursive code.
- Black box functions can be used to encapsulate unsupported code, but [not everything is allowed inside those](https://diffmu.github.io/DiffPrivacyInference.jl/stable/full_reference/demutation/#mut_type_black_box).
