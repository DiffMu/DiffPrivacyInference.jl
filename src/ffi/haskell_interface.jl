
using Base.Libc.Libdl




function callback_issubtype(ca::Cstring, cb::Cstring) :: UInt8
    a = unsafe_string(ca)
    b = unsafe_string(cb)
    τa = Meta.parse(a)
    τb = Meta.parse(b)
    res0 = (eval(τa) <: eval(τb))

    if res0
        # NOTE: This is a very strange workaround for a bug
        #       where sometimes this callback (even though
        #       computing the correct result) returns a
        #       wrong result.
        #       But strangely enough this does not happen
        #       if a print is happening which depends on
        #       the outcome.
        #       Thus we print here the empty string.
        print("")
        return 1
    else res0
        return 0
    end
end

global_parsetermresult = ""

function callback_parseterm(ci::Cstring) :: Cstring
    input = unsafe_string(ci)
    t = string_to_dmterm(input)
    output = string(t)
    global_parsetermresult = output
    pointer(global_parsetermresult)
end

# const c_callback_issubtype = @cfunction(callback_issubtype, Cuchar, (Cstring, Cstring))


# function typecheck_hs_from_dmterm(term::DMTerm)
#     str = string(term)

#     # load the shared library
#     # Note, the library has to be available on a path in $LD_LIBRARY_PATH
#     dm = Libdl.dlopen(joinpath(homedir(), ".local/lib/libdiffmu-wrapper"))

#     # get function pointers for the relevant functions
#     init = Libdl.dlsym(dm, :wrapperInit)
#     exit = Libdl.dlsym(dm, :wrapperExit)
#     typecheckFromDMTerm = Libdl.dlsym(dm, :typecheckFromCString_DMTerm)

#     # call the library
#     ccall(init, Cvoid, ())

#     c_callback_issubtype = @cfunction(callback_issubtype, Cuchar, (Cstring, Cstring))

#     ccall(typecheckFromDMTerm, Cvoid, (Ptr{Cvoid},Cstring,), c_callback_issubtype, str)
#     ccall(exit, Cvoid, ())

#     # unload the library
#     Libdl.dlclose(dm)

#     return ()
# end

function typecheck_hs_from_string(term)
    ast = Meta.parse("begin $term end")
    ast = rearrange(ast)
    sanitize([ast], LineNumberNode(1, "none"), [])

    # Code from https://stackoverflow.com/questions/45451245/how-to-unparse-a-julia-expression
    B     = IOBuffer();              # will use to 'capture' the s_expr in
    Expr1 = ast                      # the expr we want to generate an s_expr for
    Meta.show_sexpr(B, Expr1);       # push s_expr into buffer B
    seek(B, 0);                      # 'rewind' buffer
    str      = read(B, String);      # get buffer contents as string
    close(B);                        # please to be closink after finished, da?


    # load the shared library
    # Note, the library has to be available on a path in $LD_LIBRARY_PATH
    dm = Libdl.dlopen(joinpath(homedir(), ".local/lib/libdiffmu-wrapper"))

    # get function pointers for the relevant functions
    init = Libdl.dlsym(dm, :wrapperInit)
    exit = Libdl.dlsym(dm, :wrapperExit)
    typecheckFromDMTerm = Libdl.dlsym(dm, :typecheckFromCString_DMTerm)

    # call the library

    # call the library
    ccall(init, Cvoid, ())

    c_callback_issubtype = @cfunction(callback_issubtype, Cuchar, (Cstring, Cstring))

    ccall(typecheckFromDMTerm, Cvoid, (Ptr{Cvoid},Cstring,), c_callback_issubtype, str)
    ccall(exit, Cvoid, ())

    # unload the library
    Libdl.dlclose(dm)

    return ()
end


function test_hs()

    # load the shared library
    # Note, the library has to be available on a path in $LD_LIBRARY_PATH
    dm = Libdl.dlopen(joinpath(homedir(), ".local/lib/libdiffmu-wrapper"))

    # get function pointers for the relevant functions
    init = Libdl.dlsym(dm, :wrapperInit)
    exit = Libdl.dlsym(dm, :wrapperExit)
    runHaskellTests = Libdl.dlsym(dm, :runHaskellTests)

    # call the library
    ccall(init, Cvoid, ())

    c_callback_issubtype = @cfunction(callback_issubtype, Cuchar, (Cstring, Cstring))
    c_callback_parseterm = @cfunction(callback_parseterm, Cstring, (Cstring,))

    ccall(runHaskellTests, Cvoid, (Ptr{Cvoid},Ptr{Cvoid},), c_callback_issubtype, c_callback_parseterm)
    ccall(exit, Cvoid, ())

    # unload the library
    Libdl.dlclose(dm)

    return ()
end



function test_expr_parser(term)
    ast = Meta.parse("begin $term end")
    ast = rearrange(ast)
    sanitize([ast], LineNumberNode(1, "none"), [])

    # Code from https://stackoverflow.com/questions/45451245/how-to-unparse-a-julia-expression
    B     = IOBuffer();              # will use to 'capture' the s_expr in
    Expr1 = ast                      # the expr we want to generate an s_expr for
    Meta.show_sexpr(B, Expr1);       # push s_expr into buffer B
    seek(B, 0);                      # 'rewind' buffer
    str      = read(B, String);      # get buffer contents as string
    close(B);                        # please to be closink after finished, da?


    # load the shared library
    # Note, the library has to be available on a path in $LD_LIBRARY_PATH
    dm = Libdl.dlopen(joinpath(homedir(), ".local/lib/libdiffmu-wrapper"))

    # get function pointers for the relevant functions
    init = Libdl.dlsym(dm, :wrapperInit)
    exit = Libdl.dlsym(dm, :wrapperExit)
    runExprParser = Libdl.dlsym(dm, :runExprParser)

    # call the library
    ccall(init, Cvoid, ())

    ccall(runExprParser, Cvoid, (Cstring,), str)
    ccall(exit, Cvoid, ())

    # unload the library
    Libdl.dlclose(dm)

    return ()
end

