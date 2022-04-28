
# [Demutation system](@id demutation)

*Demutation* is the first stage of the typechecker. Its goal is to translate the procedural, impure julia code into pure lambda calculus terms,
while preserving the original computational behaviour. This process is mostly invisible to the user, but it neccessitates various properties
which have to hold for the julia code which is given to the checker - these are described on this page.

Translating a mutating function into a pure one is based on the simple observation that a function of type
```
f : (mut A, B, mut C) -> ()
```
which takes three arguments of types `A`, `B` and `C`, and returns nothing, but mutates its first and third arguments can be given the pure type
```
f' : (A, B, C) -> (A, C)
```
where the mutated arguments are simply part of the return value. The complications which a demutation system has to deal with
is the fact that mutation of the value at a certain memory location will change the value of all references which point to this memory location.
That is, if we call `f(a,b,c)`, and there is another variable `a' = a` which points to the same memory location as `a`, then after the call to `f` both contents
will be mutated, even though only `a` is mentioned explicitly in the call. Such a situation, where multiple references point to the same memory location, is called
*memory aliasing*, and the demutation system mostly deals with it (usually) by making sure that it cannot occur in the first place.

The demutation system is based on a machinery that tracks abstract memory locations, i.e., an abstract notion of which variable is allocated at which memory addresses.

Two concepts which are required to be able to write code which passes demutation are the following:
 1. *Mutation types*, which are automatically inferred, track which functions are mutating and which are pure.
 2. *Move semantics* for most types ensures that no memory aliasing happens.


## Mutation types
Every variable is automatically assigned a mutation type, which tracks whether it is a mutating function or not. These types cannot be changed by assigning a different value to
a variable: When a reassignment happens, it is required that the new value has the same mutation type as the old value.

There are three mutation types:
1. The mutation type `Mutating (args...) -> ()` is for mutating functions. Where `args...` is a list that describes which argument is mutated by the function and which is not.
   I.e., the example function from above has the type `f :: Mutating (mut, pure, mut) -> ()`.
2. The mutation type `Pure` is for pure functions, and for all other pure values, such as numbers, matrices, etc..
3. The mutation type `Blackbox` is for functions which are marked as [black boxes](@ref), and thus have to be treated differently than usual functions.

Please note that currently all function arguments are assumed to be of type `Pure`. It is thus impossible to pass black boxes and mutating functions as arguments to other functions.

### The type `Mutating`
A function is marked as mutating automatically if it is inferred that it mutates its arguments. This is only possible by either calling [mutating builtins](@ref),
or by calling other mutating functions. 

The following rules apply:
 1. Mutating functions cannot have a return value; they must always end with a `return` or `return nothing` statement.
 2. Assigning the result of a mutating function (or builtin) call is forbidden (as it is going to be `nothing` anyways).

#### Examples
The builtin for the gaussian mechanism has the mutation type `gaussian_mechanism! :: Mutating (pure, pure, pure, mut) -> ()`. Thus, we can write the following function:
```julia
#
# the type is:
# g :: Mutating (pure,mut,mut) -> ()
#
function g(a,x,y) :: Priv()
  gaussian_mechanism!(1,0.5,a,x)
  gaussian_mechanism!(1,0.5,a,y)
  return
end 
```
Since `x` is passed in a mutating argument position in the first call, and `y` is passed in a mutating argument position in the second call of the gaussian mechanism,
the function type says that both `x` and `y` are being mutated by `f`. And since `a` is only ever passed in a non-mutating argument position, it is marked as not mutated.
Also, we have to add the `return` statement because `g` is mutating.
 
### The type `Pure`
Any value which is not a function is assigned the type `Pure`. The same holds for functions which are pure, i.e., do not mutate any of their arguments.

For pure functions, there is a technical rule that is enforced by the typechecker - it arises because we need to be able to track memory locations, and doing so across function boundaries is currently not implemented.

The following rule applies:
 1. No reference pass through: The memory locations of arguments passed into the function may not occur in the result value of the function.
 
#### Examples
All simple computations are of type `Pure`, for example:
```
# the type is:
# h0 :: Pure
function h0(a,b)
  x = a * b
  y = a + b
  x - y
end
```

It is possible to mutate local variables, as long as the function arguments are not involved, the function stays pure:
```
# the type is:
# h1 :: Pure
function h1(a,x)
  y = x + x     # here y is a new local variable, mutating it does not change `x`
  gaussian_mechanism!(1,0.5,a,y)
  y             # since the function is pure, we need to have a return value
end
```

The "no reference pass through" rule stated above forbids the identity function:
```
# ERROR: Found a function which passes through a reference given as input.
function id(a)
  a
end
```

Instead, one can create a copy of the input value with `clone()`, so the following is allowed:
```
# the type is:
# id' :: Pure
function id'(a)
  clone(a)
end
```


### The type `Blackbox`


## Move semantics

## Special case: `if` branches

## Special case: `for` loops

```
function fib(n)
  a = 0
  b = 1
  for i in 1:n
    (a,b) = (b, a + b)
  end
  a
end
```

