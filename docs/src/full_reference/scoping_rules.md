
# [Scoping rules](@id scoping_rules)

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
 1. A variable needs to be initialized literally earlier in the code, before being used.
 2. The [mutation type](@ref mutation_type) of a variable cannot be changed.
 3. As long as a variable is used only in a single scope, then read/write/mutation is allowed without further restrictions.
 4. If a variable is used in multiple scopes, it is a read-only variable that has to be assigned exactly once, and cannot be reassigned or mutated anywhere else.
 5. Extra rules for function definitions:
    - It is not allowed to use the same name with both `function`-keyword, and anonymous lambda definitions of functions.
    - In case of multiple implementations of a function for different types, all implementations have to be directly
      below each other in the code.
    - As an exception, the case of multiple implementations for a function is not disallowed by rule (4), i.e. it is allowed
      even if the function is used (called) in a different scope afterwards.
 





