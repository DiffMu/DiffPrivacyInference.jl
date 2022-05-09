
# [Black Boxes](@id black_boxes)
The code that we can infer sensitivity/privacy properties of is limited to the [supported syntax](@ref). In case the program you want to analyze contains pieces of code that are not supported, you can do so by telling the typechecker to assume that those parts of your code have infinitely bad sensitivity properties. This might sound like it's not very useful, but there are situations in which it actually is.

## Syntax
You need to wrap the non-checkable code in a so called "Black box function", by annotating the function definition using this syntax:
```julia
loss(X, y, m) :: BlackBox() = Flux.crossentropy(m.model(X), y)
```
Note that you can only define black boxes in the outermost scope of your code (not as an inner function, for instance). Further, black boxes cannot have multiple methods.

As the code in the function body is not analyzed, we cannot infer the return type. Upon invocation of a black box function, you hence have to specify the expected return type using the builtin [unbox](@ref). This will produce a runtime assertion on the return type. The annotation must be one of the [supported julia types](@ref), and must match exactly (i.e. if the function returns an `Integer` and you annotated `Real`, you will get an error). This  Here's an example on how to call the previously defined `loss` function:
```julia
function foo(m, x)
   res = unbox(loss(x, x, m), Real)
   res
end
```
This function can be typechecked, even though the executed code uses a function call to `Flux.jl`, which is not allowed other than inside black boxes. This example still ist not very useful, as both arguments have infinite sensitivity -- the typechecker cannot tell what happens with them inside the black box, so it assumes the worst.

For container types like `Matrix`, `Vector` and `DMGrads` you will have to specify the dimension of the output as well, which will also be runtime-asserted. Here's a slightly more involved example:
```julia
function unbounded_gradient(m::DMModel, data, label) :: BlackBox()
   gs = Flux.gradient(Flux.params(model.model)) do
           Flux.crossentropy(m.model(data),label)
        end
   return DMGrads(gs)
end
```
This already does something quite interesting, namely using the `Flux.jl` autodiff facilities to compute a gradient. A typecheckable call to it might look like this:
```julia
function compute_gradient(model, n_params, data, labels)
   gs = unbox(unbounded_gradient(model, data, labels), DMGrads, n_params)
   gs
end
```
But, again, the sensitivity of all arguments except `n_params` will be infinite, so this is not very useful. Behold the following warning before being presented with an example that is, in fact, interesting.

## Warning: do not mutate!
The typechecker completely ignores the code in the body of a black-box function. You can do anything you like in there, except one thing: mutating the arguments or global state. You will not recieve any warnings or errors about this during typechecking, so be careful. If you do, the analysis result will be invalid.

## Warning: do not let references to input arguments through!
There is a second property which is required for correctness of the result, yet which cannot be checked
automatically for black boxes: You have to make sure that the return value of the function does not
contain references to the input arguments, or global variables. See [here](@ref mut_type_black_box) for some details.


## The interesting special case
As you may read in the documentation on [measuring distance](@ref), container types carry information on the metric that is used for the definition of sensitivity. A special property of the `(LInf, 𝔻)`-metric and other discrete metrics on container types is this:
```math
\text{Functions from 𝔻-matrices, -vectors or -gradients to (L∞, 𝔻)-vectors or -gradients are 1-sensitive.}
```

This means if you take care for your black box function to have the correct input and output types, it will be 1-sensitive! A modification of the above code suffices:
```julia
function compute_gradient(model, n_params, data::Vector{<:Data}, labels::Vector{<:Data})
   gs = unbox(unbounded_gradient(model, data, labels), MetricGradient(Data, LInf), n_params)
   gs
end
```
The inferred sensitivity for the `data` and `labels` arguments is 1. Make sure you understand what annotating them in this way means for the interpretation of this result: The sensitivity is is now measured with respect to some *discrete* metric on the input vectors and the `(LInf, 𝔻)`-metric on the output gradient. In particular, these are not your standard euclidean vectors, so make sure this is what you actually want or take care to convert the results properly. See the [flux-dp example](@ref) walkthrough for a more detailed explanation of this particular application.
