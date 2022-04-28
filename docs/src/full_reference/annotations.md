
# Annotations

Our typechecker can infer many things about your code, but is does need you to annotate certain parts to get rid of ambiguities. In general, the inferred bounds will always be better the more precisely you annotate function argument and return types. If you don't, you will most likely end up with a lot of unresolved [constraints](@ref). In addition, there are some custom annotations that you can use to inform the typechecker about your intentions towards certain parts of the code. Not using these will likely end in typechecking errors or catastrophically pessimistic inference results. Here's your options:

## Function kinds
### `Priv()`
We distinguish between functions that provide differential privacy (so called [privacy functions](@ref)), and ones that do not (so called [sensitivity functions](@ref)). The typechecker cannot know whether you expect a function to be differentially private or not, so if you do you'll have to annotate your function definition using the [`Priv()`](@ref) type function. Its argument is the desired return type of the annotated function, no argument means any return type. For example to declare function `f` to be differentially private and returning something of type [`Matrix`](@ref):
```
function f(eps, del, x::Matrix) :: Priv(Matrix)
   gaussian_mechanism(1, eps, del, x)
end
```
The typechecker will proceed assuming `f` is differentially private and infer the privacy parameters. In the example case presented here, the [Gaussian Mechanism](@ref) is used to add noise and provide finite privacy parameters. If you don't use our privacy mechanisms or don't use them properly in a function that you annotated with `Priv()`, you will likely (and correctly) end up with infinite privacy parameters. If you do use one of the privacy mechanisms but do not annotate the surrounding function as private, you will get an error.

### `PrivacyFunction`
If you want to write a higher-order function that takes a privacy function as an argument, you have to annotate that argument accordingly using [`PrivacyFunction`](@ref). For example if we want to write a higher-order function `g` that we want to apply to our previously defined `f` it would need to look like this:
```
function g(f::PrivacyFunction, x::Matrix) :: Priv(Matrix)
   f(0.1, 0.1, x)
end
```

## Static parameters
As you can read in the documentation of our [types](@ref), we allow two kinds of numeric function arguments -- static and variable ones. Static arguments are usueful if you want the inferred sensitivity/privacy guarantee of some of your function's arguments to depend on the values of some other of the function arguments. A simple example with an argument annotated using the [`Static()`](@ref) type function:
```
julia> typecheck_hs_from_string("module L
          function f(x::Integer, y::Integer)
             x * y
          end
       end")
   
   ---------------------------------------------------------------------------
   Type:
   {
   |   (Integer @ ∞, Integer @ ∞) -> Integer
   }
   
   ---------------------------------------------------------------------------



julia> typecheck_hs_from_string("module L
          function f(x::Static(Integer), y::Integer)
             x * y
          end
       end")
   
   ---------------------------------------------------------------------------
   Type:
   {
   |   - Integer[x ©]@0
   |   
   |   - Integer@x
   |   --------------------------
   |    -> Integer
   }
```
In the first example, both arguments have infinite sensitivity, as they are both variable and we cannot bound the distance between `x*y` and `x*y'` if `x` is variable. If we however annotate `x` to be static, the sensitivity in `y` can be expressed as the value of `x`. Note that the `x` argument has sensitivity `0`, as the type `Integer[x ©]` is a singleton type containing only one element, namely an integer number with value `x`. This means you can only input values here that are either actually runtime constants or annotated static themselves. Sensitivity and privacy guarantees for this parameter hence are not valid for all integers, but only for each individual fixed integer. So if the parameter is the data input of your function in whose privacy you are interested, you probably don't want to make it static.

## Black boxes
The typechecker cannot infer sensitivity/privacy guarantees for arbitrary code (see [How to write checkable code](@ref)). We still support using some functions whose body we cannot check via the [black box](@ref) construct. These functions must be defined inside the code that is typechecked, and you can tell the checker that it can't infer things about the body by using a [`BlackBox()`] annotation in the definition. Here's an example of a function calling a function from an imported module, which is not admissible in code that is supposed to be checked:
```
loss(X, y, m::DMModel) :: BlackBox() = Flux.crossentropy(m.model(X), y)
```

## Container types
[Our types](@ref) for matrices, vectors and gradients contain more information than the julia-native types, namely the dimension, which metric is used to measure, and if there is a bound on the row norm. If you want to specify which metric you would like your guarantees to be given in, you can annotate by using the corresponding type functions instead of the native `Matrix{T}` etc. types:
- [`MetricMatrix(T, L::Norm)`](@ref)
- [`MetricVector(T, L::Norm)`](@ref)
- [`MetricGradient(T, L::Norm)`](@ref)
where `L` is one of the norms `L1,L2,LInf` denoting the induced metric. See the documentation on [container metrics](@ref) for more details about metrics.


