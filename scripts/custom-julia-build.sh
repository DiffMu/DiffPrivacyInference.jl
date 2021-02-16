#!/bin/sh

julia --color=yes -e "using Pkg; Pkg.build(verbose=true);"

# run tests
julia -O0 --compile=min --check-bounds=yes --color=yes -e "using Pkg; Pkg.test(coverage=true);"
# coverage
julia -O0 --compile=min --color=yes -e "using Pkg; Pkg.add(\"Coverage\"); using Coverage; Codecov.submit(process_folder())"
