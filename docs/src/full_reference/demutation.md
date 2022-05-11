
# [Demutation system](@id demutation)

*Demutation* is the first stage of the typechecker. Its goal is to translate the procedural, impure julia code into pure lambda calculus terms,
while preserving the original computational behaviour. This process is mostly invisible to the user, but it neccessitates various properties
which have to hold for the julia code which is given to the checker — these are described on this page.

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


## [Mutation types](@id mutation_type)
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

It is possible to mutate local variables: as long as the function arguments are not involved, the function stays pure:
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

### [The type `Blackbox`](@id mut_type_black_box)
There is a seperate mutation type for [black box functions](@ref black-boxes). This makes sure that the same function name
cannot be given both normal function and black box implementations at the same time.

The implementation of black boxes is not checked in any way. Users must check that the following rules are followed by themselves!

> **Warning**: For the type checking result to be
> valid, you have to make sure yourself that the following two properties hold for every black box:
> 1. *No reference pass through*: Black boxes **must not** return a value which could contain references to either
>    a function argument or a global variable.
> 2. *Pureness*: Black boxes **must not** mutate either arguments or global variables.

#### Example
In the following example, since `h2` is defined as black box, the same name cannot be used when giving
a second implementation.
```
# the type is:
# h2 :: BlackBox
function h2(a :: Integer) :: BlackBox()
  2 * a
end

# ERROR: Global definitions cannot have the same name as black boxes.
function h2()
  2
end
```

## Restrictions dealing with memory aliasing
As described in the introduction, the problems with verifying code that has mutating functions
actually only appear when memory aliasing occurs. That is, when
 1. there are multiple variables which reference the same memory location (memory aliasing), and
 2. one of them is being mutated.
Since we want to allow mutation, we have to make sure that variables whose content is going to be mutated
are never aliased. In other words: There should always be only a single owner of mutable data.
This reflects in two rules which are described in the following sections.

### Move semantics
Assignments like `b = a` where the right hand side (RHS) is simply a variable (or a tuple of variables...)
represent a problem. The solution is to say that in such an assignment the ownership of the
memory location of the RHS is transferred to the variable on the LHS. This means that
afterwards the name `a` becomes invalid and can no longer be used. Instead, the new name `b`
has to be used.

The function `i` in the following example tries to print the value of the variable `a` after its content has been moved to `b`.
(Printing has to be done using a black box.)
```julia
function println_(a) :: BlackBox()
  println(a)
  0
end

function i(a)
  unbox(println_(a), Integer)  # print value of `a`
  b = a                        # after this line, both `a` and `b` point to the same memory,
                               # but the typechecker marks `a` as no longer valid
  unbox(println_(b), Integer)  # print value of `b`
  unbox(println_(a), Integer)  # ERROR: Tried to access the variable a.
                               #        But this variable is not valid anymore,
                               #        because it was assigned to something else.
end
```
The same rules hold for tuple assignments, where either (or both) the LHS and RHS are tuples.

In case one really wants to have multiple variables with the same content, the only way is to use
[`clone`](@ref) to make a (deep-)copy of the content. Obviously, mutating one of the copies will not
change the others.

### Function calls
The following rules need to be followed for a mutating function call to be accepted by the typechecker:
 1. The only term allowed in a mutating argument position is a variable name.
 2. As soon as a variable appears in a mutating argument position, it cannot appear in any of the
    other arguments.
The first rule disallows mutation of anonymous memory, i.e., makes sure that there is always a name attached
to the memory location which is mutated by the function. The second rule is required because functions
assume that all their input variables (or at least those that are being mutated) are not aliased.

### Exceptions
There are a few types for which the strategy of *no aliasing is allowed to occur* makes little sense: vectors and matrices.
With these, we explicitly do want to be able to select data using indices, and this means having multiple references to the
same data. E.g., the following should be (and is) allowed:
```julia
function k(a :: Vector{<:Integer})
  x = a[0]
  y = a[1]
  x + y
end
```
This is possible because of the following:
 1. It is allowed to index into vectors and matrices, but
 2. the content of vectors cannot be mutated.
 
The following is not allowed because of the second rule (note that [`gaussian_mechanism!`](@ref) is mutating in its last argument).
```
function l(a :: Vector{<:DMGrads}) :: Priv()
  x = a[0]
  gaussian_mechanism!(1,0.5,0,x)  # ERROR
end
```

## Special case: `if` branches
Branches in the control flow make tracking of abstract memory locations more difficult.
Instead of keeping track of a single assignment of variable names to memory locations, we
have to keep track of a set of possible memory locations, depending on the execution branch taken.

But what we cannot allow is the mutation of variables which contain multiple possible memory locations.
```julia
function f(a,b,c,x)
  if x
    c = a
  else
    c = b
  end
  gaussian_mechanism!(1,0.5,0,c)
    # ERROR: Encountered a value spanning multiple possible memory locations
    #        where a single location value was expected.
    #
    #        The encountered memory type is [SingleMem a#,SingleMem b#₁]
end
```
The message says that we expected the variable `c` to not have multiple possible locations,
but it was inferred that it could either reference the content of `a` or the content of `b`.

## Special case: `for` loops
Similarly we have to restrict what kind of reassignments are allowed in loops.
The rule is the following:
 1. If a variable, after a single iteration through the loop body, references a different memory location,
    than this memory location has to be a new one that was allocated in the body.

This means that the following implementation of a function computing the n-th fibonacci number
is not allowed:
```julia
function fib(n)
  a = 0
  b = 1
  for i in 1:n               # ERROR: Found a loop body which moves variables around.
    (a,b) = (b, a + b)       #        The following variables are changed and
  end                        #        contain memory locations from before: [b#₂]
  a
end
```
The problem is that the variable `b` is moved into `a`, so this can be solved by using [`clone`](@ref):
```julia
function fib(n)
  a = 0
  b = 1
  for i in 1:n
    (a,b) = (clone(b), a + b)
  end
  a
end
```
