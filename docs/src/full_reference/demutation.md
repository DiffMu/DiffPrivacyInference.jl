
# [Mutation rules](@id demutation)

It is possible to write functions which mutate their arguments.
The typechecker automatically infers whether this is the case
and enforces some rules which are required for a valid privacy analysis.

Mutation is done using mutating [builtins](@ref builtins) (those annotated with a `!`),
or by calling other mutating functions. Mutating builtins exist only for gradients and models.

## Overview
The following is an overview over all rules related to mutation. These rules are explained in more detail below.
 - [Writing functions](@ref mutation_funs)
   1. *return if mutating*
   2. *no reference pass through*
   3. *no self aliasing*
 - [Assigning variables](@ref mutation_vars)
   1. *move semantics*
   2. *indexing exception*
 - [Calling functions](@ref mutation_calls)
   1. *only pure function arguments*
   2. *mutating arguments are variables*
   3. *single occurence of mutated variables*
 - [If branches](@ref mutation_if)
 - [For loops](@ref mutation_for)
 
## [Details: Writing functions](@id mutation_funs)
The typechecker infers a "mutation type" for all functions. There are three mutation types:
1. The mutation type `Mutating (args...) -> ()` is for functions that mutate some of their arguments. Where `args...` is a list that describes which argument is mutated by the function and which is not.
   For example, a function which mutates its first and third argument would have the mutation type `Mutating (mut, pure, mut) -> ()`.
2. The mutation type `Pure` is for functions that do not mutate any of their arguments, and for all other pure values, such as numbers, matrices, etc..
3. The mutation type `Blackbox` is for functions which are marked as [black boxes](@ref), and thus have to be treated differently than usual functions.

### [Rule: *return if mutating*](@id mut_rule_funs_1)
Functions that are mutating have to end with a `return` or `return nothing` statement.
Functions that are pure are not allowed to contain a `return` statement, instead the value of the last statement is used as the return value.

### [Rule: *no reference pass through*](@id mut_rule_funs_2)
For **all** functions the following rule applies: The arguments of the function may not be referenced in the result value of the function. That is,
you can use the function arguments in computations, whose value is then returned. But you may not return the function argument itself without applying any computations to it.
If this is something you actually want to do, you can use the builtin [`clone`](@ref) to create a copy of your object, which you are then allowed to return.

This is checked automatically for pure functions. **For black boxes, as we cannot look inside, this has to be checked by the user!** For mutating functions this rule
is irrelevant, as they do not have a proper return value.

### [Rule: *no self aliasing*](@id mut_rule_funs_3)
For **all** functions the following rule applies: If the result value is a tuple, it may not contain the same variable more than once. That is, it is not allowed
to return the tuple `(a,a,a)` where `a` is some variable in the code. If this is something you want to do, you can use the builtin [`clone`](@ref) to create copies
of `a`: `(clone(a), clone(a), clone(a))`.

This is checked automatically for pure functions. **For black boxes, as we cannot look inside, this has to be checked by the user!** For mutating functions this rule
is irrelevant, as they do not have a proper return value.

### Example (writing a mutating function)
The builtin for the gaussian mechanism has the mutation type `gaussian_mechanism! :: Mutating (pure, pure, pure, mut) -> ()`. Thus, we can write the following function:
```julia
#
# the mutation type is:
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

### Example (writing a pure function)
A simple example of a pure function (note that the return value is given by the last statement):
```julia
# the type is:
# h0 :: Pure
function h0(a,b)
  x = a * b
  y = a + b
  x - y
end
```

It is possible to mutate local variables: as long as the function arguments are not involved, the function stays pure:
```julia
# the type is:
# h1 :: Pure
function h1(a,x)
  y = x + x     # here y is a new local variable, mutating it does not change `x`
  gaussian_mechanism!(1,0.5,a,y)
  y             # since the function is pure, we need to have a return value
end
```

### Example (trying to write the identity function)
The ["no reference pass through" rule](@ref mut_rule_funs_2) stated above forbids the identity function:
```julia
# ERROR: Found a function which passes through a reference given as input.
function id(a)
  a
end
```

Instead, one can create a copy of the input value with `clone()`, so the following is allowed:
```julia
# the type is:
# id' :: Pure
function id'(a)
  clone(a)
end
```

## [Details: Assigning Variables](@id mutation_vars)
The correctness of our tracking of mutations depends on the requirement that *there should always be a single owner of data*.
Since if there were two variables both pointing to the same data in memory, and one of the variables is mutated,
the content of the other variable would change as well. The typechecker ensures that such a situation is not going to occur at runtime.

### Rule: *move semantics*
Assignments like `b = a` where the right hand side (RHS) is simply a variable (or a tuple of variables...)
represent a problem, since after the statement both `a` and `b` would point to the same data.
The solution is to say that such an assignment transfers the ownership of the
memory location of the RHS is to the variable on the LHS. This means that
afterwards the name `a` becomes invalid and can no longer be used. Instead, the new name `b`
has to be used.

### Example
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
[`clone`](@ref) to make a copy of the content. Obviously, mutating one of the copies will not
change the others.

### Rule: *indexing exception*
There are a few types for which the strategy of *there is always a single owner of data* makes little sense: vectors and matrices.
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
 2. the content of vectors or matrices cannot be mutated.
 
The following is not allowed because of the second point (note that [`gaussian_mechanism!`](@ref) is mutating in its last argument).
```julia
function l(a :: Vector{<:DMGrads}) :: Priv()
  x = a[0]
  gaussian_mechanism!(1,0.5,0,x)  # ERROR
end
```


## [Details: Calling functions](@id mutation_calls)
There are some rules which need to be followed when calling functions.

### Rule: *only pure function arguments*
Currently all function arguments are assumed to be of type `Pure` when a function is checked.
It is thus not allowed to pass black boxes and mutating functions as arguments to other functions.

### Rule: *mutating arguments are variables*
The only term allowed in a mutating argument position is a variable name.

This disallows the mutation of anonymous objects, i.e., makes sure that there is always a name attached
to the object which is mutated by a function.

### Rule: *single occurence of mutated variables*
A variable which is given in a mutating argument position cannot appear in any of the
other arguments.

This is required because we need to make sure that the other arguments do not reference the same data
as the mutated variable.

## [Details: `if` branches](@id mutation_if)
Branches in the control flow make tracking of data memory locations more difficult.
In particluar, after an `if` statement, we may not know what data is going to be referenced
by a given variable.

Because of this cannot allow the mutation of variables for which multiple possible memory locations are inferred.
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

## [Details: `for` loops](@id mutation_for)
Similarly we have to restrict what kind of reassignments are allowed in loops.

The rule is the following: If a variable, after a single iteration through the loop body, references a different memory location,
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
