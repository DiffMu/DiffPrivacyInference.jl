# [Supported julia syntax](@id syntax)

We cannot check arbitrary `julia` code, and most julia code does not result in differentially private functions anyways. Instead we restrict to a subset of the language which is suited for our static analysis. Here's a list of language features we support:

- Function definitions using `function`, one-line definitions and anonymous functions, as well as function application.
- Multiple dispatch on `Integer, Real, Vector{<:T}, Matrix{<:T}, Tuple{<:T}` and our [special types](@ref annotations). Finer types are not allowed.
- Some arithmetics on numbers, vectors and matrices, as well as row access and indexing on matrix using `m[i,:]` and `m[i,j]` and vector indexing using `v[i]`
- Type annotations on function variables, like in `f(x::Integer) = x + x`
- Variable and tuple assignments like `x = 1` or `(a,b,c) = t`
- Loops over integer ranges, where the loop head must be of the form `for i in 1:2:n`.
- `if`, `ifelse` and `else` statements where the condition can be an integer or of the form `x == y`.
- `import`, which will just be ignored by the type checker. You can use stuff from imported modules, but only inside black boxes (see below).
- `include` statements. The typechecker will load the included file and check it as well.
- Functions which mutate (some) of their arguments. Special rules apply, see [Mutating functions](@ref demutation).
- Functions that contain syntax not listed above. You can mark these and they will be checked in a very pessimistic manner. Note that it is still not allowed to do absolutely anything in these, see the documentation of [black boxes](@ref black-boxes).
- Be aware of the [limitations of the typechecker regarding floating point implementations](https://diffmu.github.io/DiffPrivacyInference.jl/dev/tutorial/02_privacy_functions/#Warning:-Floating-point-is-dangerous!)

## Forbidden things

There are a few things you are not allowed to do even though they use supported syntax (which the typechecker will tell you if you try). Namely:

- Your code has to be valid julia code. If it is not, do not expect the typechecker to always tell you so or produce reasonable results.
- You cannot reassign (or mutate) variables that were declared in a different scope. For example, the following is illegal:
  ```
  function foo()
     x = 10
     function bar()
        x = 100
        x
     end
     bar()
  end
  ```
- If you want to use a variable, you have to define it first. E.g. the following is valid julia code but illegal:
  ```
  function foo()
     bar() = a
     a = 100
     bar()
  end
  ```
- As long a reassignment happens in the same scope as where the variable was defined, it is allowed.
  For example the following is valid code:
  ```
  function foo()
     x = 1
     y = x+2
     x = 2
     y
  end
  ```
- For a detailed explanation see [Scoping rules](@ref scoping-rules).
- Recursion is not supported and might lead to nontermination of the typechecker. You were warned.
- Assignments within assignments (like `x = y = 10`) are forbidden. Why would you, anyways.
