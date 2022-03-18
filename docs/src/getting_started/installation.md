
# Installation

## Using the julia package manager

This is currently not possible. For now, see the next section.

## From source

### Dependencies
This project uses both Julia and Haskell, as such, you need to have both languages installed.
In particular, in order to run/build from source, you need:
 - [Julia](https://julialang.org/), a relatively recent version, e.g. `>= 1.6.1`
 - [Haskell Tool Stack](https://docs.haskellstack.org/en/stable/README/) version `>= 1.6.0`
 - GNU Make

### Getting the source and building
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
    
### Usage
    
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
    
### Tips & Tricks
You may want to use [`Revise.jl`]() so you don't have to restart the REPL everytime you change the code. If you put
```julia
using Revise
```
in your `~/.julia/config/startup.jl` (or wherever you keep your julia config), you won't have to type it on every REPL restart.


