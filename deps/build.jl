
#
# Julia package with external dependencies
#   project template from:
#     https://github.com/felipenoris/JuliaPackageWithRustDep.jl
#


# ENV["CARGO_TARGET_DIR"] = @__DIR__

const haskellprojname = "DiffPrivacyInferenceHs"
const haskelllibname = "diffprivhs"
const juliapackage = "DiffPrivacyInference"

const libname = Sys.iswindows() ? haskelllibname : "lib" * haskelllibname
# Windows .dlls do not have the "lib" prefix

function build_dylib()
    clean()

    release_dir = joinpath(@__DIR__, "release")
    dylib = dylib_filename()
    release_dylib_filepath = joinpath(release_dir, dylib)

    # if we are in CI we do not build the haskell library
    ci_var = get(ENV, "CI", "false")
    if ci_var != "true"
        run(Cmd(`make install LIB_INSTALL_DIR=$release_dir`, dir=joinpath(@__DIR__, haskellprojname)))
        @assert isfile(release_dylib_filepath) "$release_dylib_filepath not found. Build may have failed."
    end

    mv(release_dylib_filepath, joinpath(@__DIR__, dylib))
    rm(release_dir, recursive=true)

    write_deps_file(libname, dylib, juliapackage)
end

function dylib_filename()
    @static if Sys.isapple()
        "$libname.dylib"
    elseif Sys.islinux()
        "$libname.so"
    elseif Sys.iswindows()
        "$libname.dll"
    else
        error("Not supported: $(Sys.KERNEL)")
    end
end

function write_deps_file(libname, libfile, juliapackage)
    script = """
import Libdl

const release_$libname = joinpath(@__DIR__, "$libfile")
const dev_$libname = joinpath(homedir(), ".local/lib/$libfile")
$libname = ""

function check_deps()
    # ignore if we are in CI
    ci_var = get(ENV, "CI", "false")
    if ci_var == "true"
        return
    end

    # else, do check deps
    global release_$libname
    global dev_$libname
    global $libname
    if isfile(dev_$libname)
      $libname = dev_$libname
    elseif isfile(release_$libname)
      $libname = release_$libname
    else
        error("\$release_$libname does not exist, Please re-run Pkg.build(\\"$juliapackage\\"), and restart Julia.\n\nAlternatively, if trying to use a development version, make sure that the dynamic library is installed to \$dev_$libname.")
    end

    if Libdl.dlopen_e($libname) == C_NULL
        error("\$$libname cannot be opened, Please re-run Pkg.build(\\"$juliapackage\\"), and restart Julia.")
    end
end
"""

    open(joinpath(@__DIR__, "deps.jl"), "w") do f
        write(f, script)
    end
end

function clean()
    deps_file = joinpath(@__DIR__, "deps.jl")
    isfile(deps_file) && rm(deps_file)

    release_dir = joinpath(@__DIR__, "release")
    isdir(release_dir) && rm(release_dir, recursive=true)

    dylib_file = joinpath(@__DIR__, dylib_filename())
    isfile(dylib_file) && rm(dylib_file)
end

build_dylib()


