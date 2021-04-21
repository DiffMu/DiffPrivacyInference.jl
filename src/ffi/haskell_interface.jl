
using Base.Libc.Libdl


function typecheck_hs(myf)
    # load the shared library
    # Note, the library has to be available on a path in $LD_LIBRARY_PATH
    dm = Libdl.dlopen("libdiffmu-wrapper")

    # get function pointers for the relevant functions
    init = Libdl.dlsym(dm, :wrapperInit)
    exit = Libdl.dlsym(dm, :wrapperExit)
    test = Libdl.dlsym(dm, :test)
    typecheckFromDMTerm = Libdl.dlsym(dm, :typecheckFromDMTerm)

    # call the library
    ccall(init, Cvoid, ())
    # ccall(test, Cvoid, ())
    ccall(typecheckFromDMTerm, Cvoid, (Cstring,), "Please use this")
    ccall(exit, Cvoid, ())

    # unload the library
    Libdl.dlclose(dm)
end






