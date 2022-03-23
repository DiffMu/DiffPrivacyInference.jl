# DiffPrivacyInferenceHs

This is the backend for [DiffPrivacyInference.jl](https://github.com/DiffMu/DiffPrivacyInference.jl).

## Developer Guide
### Dependencies
This project uses both Julia and Haskell, as such, you need to have both languages installed.
In particular, in order to run/build from source, you need:
 - [Julia](https://julialang.org/), a relatively recent version, e.g. `>= 1.6.1`
 - [Haskell Tool Stack](https://docs.haskellstack.org/en/stable/README/) version `>= 1.6.0`
 - GNU Make

### Building from source
 1. Clone this repository, as well as the [julia frontend](https://github.com/DiffMu/DiffPrivacyInference.jl).
    (They do not have to be cloned into the same directory)
    ```bash
    ~ $ git clone https://github.com/DiffMu/DiffPrivacyInferenceHs
    ~ $ git clone https://github.com/DiffMu/DiffPrivacyInference.jl
    ``` 
 2. Build the haskell project.
    ```bash
    ~/DiffPrivacyInferenceHs $ make install
    ```
    > **NOTE**: The makefile is a small wrapper which calls `stack build`, and then copies the built library
    > `libdiffmu-wrapper` to the location given at the top of the makefile, `LIB_INSTALL_DIR = $${HOME}/.local/lib`.
    > This is the location where the julia frontend expects to find the library, but by updating it
    > in both places (makefile and in `DiffPrivacyInference.jl/src/haskell_interface.jl`) it can be changed.
 3. Register `DiffPrivacyInference.jl` as a local package by navigating into the directory you cloned the julia frontend repo into and launching the julia REPL. There, first activate the package by entering
    ```
    ] activate .
    ```
    Then install all dependencies:
    ```
    ] instantiate
    ```
 4. Still in the julia REPL, load the project with
    ```julia
    julia> using DiffPrivacyInference
    ```
    To parse a string and then typecheck it using the haskell backend, do
    ```julia
    julia> term = string_to_dmterm("function my_identity(a)
                                      return a
                                    end")

    julia> typecheck_hs_from_dmterm(term)
    ```
    To execute all (haskell-)tests, simply run
    ```julia
    julia> test_hs()
    ```
    You may want to use [`Revise.jl`]() so you don't have to restart the REPL everytime you change the code. If you put
    ```
    using Revise
    ```
    in your `~/.julia/config/startup.jl` (or wherever you keep your julia config), you won't have to type it on every REPL restart.



### Project structure
The subfolders are organized as follows:
```
- app  (main entry point into application)
- src  (actual source code)
  \- DiffMu
     |- Prelude    (Common imports from libraries)
     |- Abstract   (Structures/Code useful for building typecheckers,
     |              should not contain references to the actual duet type system)
     |- Core       (Basic definitions of the duet type system, operations on contexts, etc.)
     |- Typecheck  (Implementation of the actual typechecking and subtyping rules)
- ffisrc      (haskell code which is the entrypoint when calling this project from julia)
- csrc        (c code fragment for initializing the haskell runtime)
- test        (place for tests which do NOT need to call julia-callbacks, i.e., currently none)
- test-native (current place for all tests which are called when executing test_hs() in julia)
- docs        (place for documentation)
```

In particular, in `src/DiffMu/Core`, we find:
 - Definitions of all relevant data types, and the main typechecking monad in `Definitions.hs` and `TC.hs`,
   unification is found in `Unification.hs`
 - The symbolic number data type, used for sensitivity and privacy values in `Symbolic.hs`
 - The logging system in `Logging.hs`
 
In `src/DiffMu/Typecheck`, we have:
 - The preprocessing steps in `Preprocess`:
    1. Collection of information about top-level functions (`TopLevel.hs`)
    2. Translating mutating code into non-mutating code (`Demutation.hs`)
    3. Rearranging function definitions (`FLetReorder.hs`)
    4. Renaming function argument names to simulate lexical scoping (`LexicalScoping.hs`)
 - The main typechecking function in `Typecheck.hs`


