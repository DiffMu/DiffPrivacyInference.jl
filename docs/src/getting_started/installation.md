
# Installation

## Using the julia package manager

The easiest way to install this package is using the julia package manager.

### Prerequisites
Since part of this project is written in Haskell and build with the [haskell tool stack](https://docs.haskellstack.org/en/stable/README/),
you will also need it for installing this package. Fortunately, this is the only thing you need, as managing and installing the rest of the haskell dependencies
is done by stack.

For installing stack best follow the [offical instructions](https://docs.haskellstack.org/en/stable/README/#how-to-install).

### Getting this package

Simply execute the following command in the julia shell:
```julia
] add https://github.com/DiffMu/DiffPrivacyInference.jl
```
This should produce something similar to the following output, while julia installs all required dependencies:
```julia
(my-env) pkg> add https://github.com/DiffMu/DiffPrivacyInference.jl
    Updating git-repo `https://github.com/DiffMu/DiffPrivacyInference.jl`
    Updating registry at `~/.julia/registries/General.toml`
   Resolving package versions...
    Updating `~/my-env/Project.toml`
  [c8299d45] + DiffPrivacyInference v0.1.0 `https://github.com/DiffMu/DiffPrivacyInference.jl#main`
    Updating `~/my-env/Manifest.toml`
  [621f4979] + AbstractFFTs v1.1.0
  ...
  (lots of julia packages here)
  ...
  [3f19e933] + p7zip_jll
    Building DiffPrivacyInference → `~/.julia/scratchspaces/44cfe95a-1eb2-52ea-b672-e2afdf69b78f/ced72be8f47015fe6f6ec85b815ac8d979225462/build.log`
  Progress [>                                        ]  0/1
```
This last step might take a long time, since here the haskell build (including all dependencies) happens.
To get some feedback about progress, you can watch the content of the given `build.log` file (e.g. using `tail path-to-log/build.log`).

When this is done, you can load the DiffPrivacyInference package in your julia shell:
```julia
julia> using DiffPrivacyInference
```

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


