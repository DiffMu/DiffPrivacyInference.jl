
# [Project structure](@id project_structure)

## Julia project

## Haskell project
The subfolders of the [haskell part](https://github.com/DiffMu/DiffPrivacyInferenceHs) are organized as follows:
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



