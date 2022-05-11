
# [Scoping rules](@id scoping-rules)

Some features of julia make static analysis more difficult than necessary. In particular,
the behaviour of variables captured in functions. Consider the following:
```julia
function f0()
  x = a
  function f1()
    y = a
    function f2()
      z = a
      function f3()
        x * y * z
      end
    end
  end
end

function g()
  a = a + 1
end

a = 2
f1_ = f0()   # uses `a = 2`
g()          # increments global `a`
f2_ = f1_()  # uses `a = 3`
g()          # increments global `a`
f3_ = f2_()  # uses `a = 4`

println(f3_()) # prints `24` (= 2 * 3 * 4)
```
As can be seen, the object `f3_` captures three different versions of the same global
variable `a` and all of them are used in the computation of `f3_()`. Also, without the comments,
it would be even more difficult to read the code since the state of `a` on which the `f`'s depend
is not modified directly, but by calling yet another function.

As this behaviour is quite difficult to track statically, we introduce some restrictions on how
variables can be created, read and reassigned/mutated. Even though this disallows quite a lot of
code that julia would simply execute, one might argue that it is for the better. Code like above is
difficult to reason about not only for an automatic system, but also for humans. This means that as
an added benefit, our scoping rules prevent surprises related to global state.

The rules are the following (here, "scope" refers only to function scopes)
 1. *initialize first*: A variable needs to be initialized literally earlier in the code, before being used.
 2. *immutable mutation type*: The [mutation type](@ref mutation_type) of a variable cannot be changed.
 3. *single scope variable*: As long as a variable is used only in a single scope, then read/write/mutation is allowed without further restrictions.
 4. *multi scope variable*: If a variable is used in multiple scopes, it is a read-only variable that has to be assigned exactly once, and cannot be reassigned or mutated anywhere else.
 5. *extra function scoping rules*: Extra rules for function definitions:
    - It is not allowed to use the same name with both `function`-keyword, and anonymous lambda definitions of functions.
    - In case of multiple implementations of a function for different types, all implementations have to be directly
      below each other in the code.
    - As an exception, the case of multiple implementations for a function is not disallowed by rule (4), i.e. it is allowed
      even if the function is used (called) in a different scope afterwards.
 
### [Rule: *initialize first*](@id scoping_rule_1)
This is required to make the [second rule](@ref scoping_rule_2) work. It is relevant in the following case:
```julia
a = 1     # The rules says that this has to come *before* the definition of `add_a`

function add_a(x)
  x + a   # Here `a` is used, so it has to be initialized in the code above.
end

add_a(2) # returns `3`
```
Here, since in `add_a` the variable `a` is used, it has to be assigned literally earlier in the code.

This rule exists because we need to know the type of `a` when scope-checking/demutating the function `add_a`,
because it makes a difference whether `a` is of mutation type `Pure` or of mutation type `Blackbox`.


### [Rule: *immutable mutation type*](@id scoping_rule_2)
It is not allowed to change the mutation type of a variable. This makes sure that pure functions,
mutating functions and black boxes do not get mixed up. As a further effect it means that if a mutating
function has multiple implementations, all of them have to have the same mutation signature:
```julia
# mutation type: Mutating (pure, pure, mut) -> ()
function f0(i::Integer, a,x)
  gaussian_mechanism!(a, 0.5, 0, x)
end

# mutation type: Mutating (pure, mut) -> ()
function f1(i::Real, x)
  gaussian_mechanism!(1, 0.5, 0, x)
end
```
This gives the following error:
```julia
# ERROR: 
#  Reassignments which change the mutation type of a variable are not allowed.
#   none:
#       |
#     3 |     function f(i::Integer, a,x) :: Priv()  <- definition of 'f' with mutation type 'Mutating (pure, pure, mut) -> ()'
#     4 |       gaussian_mechanism!(a, 0.5, 0, x)
#     5 |       return
#     6 |     end
#     7 |     
#     8 |     # mutation type: Mutating (pure, mut) -> ()
#     9 |     function f(i::Real, x) :: Priv()  <- attempted reassignment of 'f' with mutation type 'Mutating (pure, mut) -> ()'
#       |
```

### [Rule: *single scope variable*](@id scoping_rule_3)
As the following example shows, working with a variable that
is only used in a single scope is not restricted:
```julia
function test(x,y) :: Priv()
  z = y            # read `y`
  y = 2            # reassign `y`
  x = x + z * y    # reassign `x`, read `y`
  gaussian_mechanism!(0.5,0.5,0.5,x)  # mutate `x`
end
```

### [Rule: *multi scope variable*](@id scoping_rule_4)
If a variable is used in some other scope than the one it is defined in,
it is marked as read-only. The following example is not allowed:
```julia
function test()
  a = 0
  function add_a(x)
    x + a   # Reading `a` in a different scope here
  end
  a = 1     # ERROR: Reassigning a variable which  is being read
            #        in a scope other than the one it is defined
            #        in is not allowed.

  add_a(2)
```
Similarly, you cannot mutate variables in a different scope other than the one
they are defined in:
```julia
function test()
  a = 0
  function f()
    a = 1      # ERROR: Trying to reassign variable `a` from outside
  end
end
```


