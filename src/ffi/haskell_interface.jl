
using Base.Libc.Libdl


function typecheck_hs_from_dmterm(term::DMTerm)
    str = string(term)

    # load the shared library
    # Note, the library has to be available on a path in $LD_LIBRARY_PATH
    dm = Libdl.dlopen("libdiffmu-wrapper")

    # get function pointers for the relevant functions
    init = Libdl.dlsym(dm, :wrapperInit)
    exit = Libdl.dlsym(dm, :wrapperExit)
    test = Libdl.dlsym(dm, :test)
    typecheckFromDMTerm = Libdl.dlsym(dm, :typecheckFromCString_DMTerm)

    # call the library
    ccall(init, Cvoid, ())
    # ccall(test, Cvoid, ())
    ccall(typecheckFromDMTerm, Cvoid, (Cstring,), str)
    ccall(exit, Cvoid, ())

    # unload the library
    Libdl.dlclose(dm)
end






