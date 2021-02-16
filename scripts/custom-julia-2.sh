#!/bin/sh

# -O0 --compile=min 
julia --color=yes -e "using Pkg; Pkg.build(verbose=true);"

# run tests
julia -O0 --compile=min --check-bounds=yes --color=yes -e "using Pkg; Pkg.test(coverage=true);"
# coverage
   # 'julia --color=yes -e "if VERSION < v\"0.7.0-DEV.5183\"; cd(Pkg.dir(\"${JL_PKG}\")); else using Pkg; end; Pkg.add(\"Coverage\"); using Coverage; Codecov.submit(process_folder())"'
