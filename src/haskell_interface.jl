
using Base.Libc.Libdl


# make sure that the haskell dependency library is installed,
# and set libdiffprivhs variable to the path to the library.

const ci_var = get(ENV, "CI", "false")
if ci_var == "false"
  const deps_file = joinpath(dirname(@__FILE__), "..", "deps", "deps.jl")
  if !isfile(deps_file)
      error("DiffPrivacyInference.jl is not installed properly, run Pkg.build(\"DiffPrivacyInference\") and restart Julia.")
  end
  include(deps_file)
end

function __init__()
    if ci_var == "false"
      check_deps()
    end
end


# make Expr matchable
@as_record Expr

function expand_includes(exin)
   @match exin begin
      Expr(:call, :include, args...) => let
         if length(args) != 1
            error("include with mapexpr not supported: $exin")
         end
         if (args[1] == "none")
            error("filename \"none\" is not permitted.")
         end
         inast = Meta.parseall(read(args[1], String), filename = args[1])
         @match inast begin
            Expr(:toplevel, args...) => return expand_includes(Expr(:block, args...))
            _ => error("Unexpected include: $(typeof(inast))")
         end
      end;
      Expr(head, args...) => return Expr(head, map(expand_includes, args)...)
      e => return e
   end
end


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
    else
        return 0
    end
end

global_parsetermresult = ""

function callback_parseterm(ci::Cstring) :: Cstring
    input = unsafe_string(ci)

    ast = Meta.parse("begin $input end")
    ast = expand_includes(ast)

    # NOTE: This is but a way to print the julia expr to a string,
    #       which for some (?) reason is better than string() method.
    #
    # Code from https://stackoverflow.com/questions/45451245/how-to-unparse-a-julia-expression
    B     = IOBuffer();              # will use to 'capture' the s_expr in
    Expr1 = ast                      # the expr we want to generate an s_expr for
    Meta.show_sexpr(B, Expr1);       # push s_expr into buffer B
    seek(B, 0);                      # 'rewind' buffer
    str      = read(B, String);      # get buffer contents as string
    close(B);                        # please to be closink after finished, da?

    output = string(str)
    global_parsetermresult = output
    pointer(global_parsetermresult)
end


"""
typecheck_from_file(file::AbstractString)

Typecheck the file named `file`, calling the haskell bcakend. Includes are resolved and parsed as well.
The typechecking result will be printed to the REPL. It will be the inferred type of the last statement in the file.
"""
function typecheck_from_file(file::AbstractString)
    file_content = read(file, String)
    ast = Meta.parseall(file_content, filename = file)
    println("read file $file")
    typecheck_hs_from_string_wrapper(Expr(:block, ast.args...),file_content,false,false)
end
function typecheck_from_file_detailed(file::AbstractString)
    file_content = read(file, String)
    ast = Meta.parseall(file_content, filename = file)
    println("read file $file")
    typecheck_hs_from_string_wrapper(Expr(:block, ast.args...),file_content,true,false)
end
function typecheck_from_file_debug(file::AbstractString)
    file_content = read(file, String)
    ast = Meta.parseall(file_content, filename = file)
    println("read file $file")
    typecheck_hs_from_string_wrapper(Expr(:block, ast.args...),file_content,true,true)
end
function typecheck_hs_from_string(term::String)
    ast = Meta.parse("begin $term end")
    typecheck_hs_from_string_wrapper(ast,term,false,false)
end
function typecheck_hs_from_string_detailed(term::String)
    ast = Meta.parse("begin $term end")
    typecheck_hs_from_string_wrapper(ast,term,true,false)
end
function typecheck_hs_from_string_debug(term::String)
    ast = Meta.parse("begin $term end")
    typecheck_hs_from_string_wrapper(ast,term,true,true)
end

function typecheck_hs_from_string_wrapper(ast::Expr, rawsource::String, bShowDetailedInfo::Bool, bShowDebugInfo::Bool)
    ast = expand_includes(ast)

    # NOTE: This is but a way to print the julia expr to a string,
    #       which for some (?) reason is better than string() method.
    #
    # Code from https://stackoverflow.com/questions/45451245/how-to-unparse-a-julia-expression
    B     = IOBuffer();              # will use to 'capture' the s_expr in
    Expr1 = ast                      # the expr we want to generate an s_expr for
    Meta.show_sexpr(B, Expr1);       # push s_expr into buffer B
    seek(B, 0);                      # 'rewind' buffer
    str      = read(B, String);      # get buffer contents as string
    close(B);                        # please to be closink after finished, da?


    # load the shared library
    # Note, the library has to be available on a path in $LD_LIBRARY_PATH
    # dm = Libdl.dlopen(joinpath(homedir(), ".local/lib/libdiffmu-wrapper"))
    dm = Libdl.dlopen(libdiffprivhs)

    # get function pointers for the relevant functions
    init = Libdl.dlsym(dm, :wrapperInit)
    exit = Libdl.dlsym(dm, :wrapperExit)
    typecheckFromDMTerm =
        (bShowDebugInfo ?
          Libdl.dlsym(dm, :typecheckFromCString_DMTerm_Debug)
        : (bShowDetailedInfo ?
                Libdl.dlsym(dm, :typecheckFromCString_DMTerm_Detailed)
              : Libdl.dlsym(dm, :typecheckFromCString_DMTerm)))

    # call the library
    ccall(init, Cvoid, ())

    c_callback_issubtype = @cfunction(callback_issubtype, Cuchar, (Cstring, Cstring))

    ccall(typecheckFromDMTerm, Cvoid, (Ptr{Cvoid},Cstring,Cstring,), c_callback_issubtype, str, rawsource)
    ccall(exit, Cvoid, ())

    # unload the library
    Libdl.dlclose(dm)

    return
end


function test_hs()

    # load the shared library
    # Note, the library has to be available on a path in $LD_LIBRARY_PATH
    # dm = Libdl.dlopen(joinpath(homedir(), ".local/lib/libdiffmu-wrapper"))
    dm = Libdl.dlopen(libdiffprivhs)

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

    return
end

function test_single_hs()

    # load the shared library
    # Note, the library has to be available on a path in $LD_LIBRARY_PATH
    # dm = Libdl.dlopen(joinpath(homedir(), ".local/lib/libdiffmu-wrapper"))
    dm = Libdl.dlopen(libdiffprivhs)

    # get function pointers for the relevant functions
    init = Libdl.dlsym(dm, :wrapperInit)
    exit = Libdl.dlsym(dm, :wrapperExit)
    runHaskellTests = Libdl.dlsym(dm, :runSingleHaskellTest)

    # call the library
    ccall(init, Cvoid, ())

    c_callback_issubtype = @cfunction(callback_issubtype, Cuchar, (Cstring, Cstring))
    c_callback_parseterm = @cfunction(callback_parseterm, Cstring, (Cstring,))

    ccall(runHaskellTests, Cvoid, (Ptr{Cvoid},Ptr{Cvoid},), c_callback_issubtype, c_callback_parseterm)
    ccall(exit, Cvoid, ())

    # unload the library
    Libdl.dlclose(dm)

    return
end



function test_expr_parser(term)
    ast = Meta.parse("begin $term end")
    ast = expand_includes(ast)

    # NOTE: This is but a way to print the julia expr to a string,
    #       which for some (?) reason is better than string() method.
    #
    # Code from https://stackoverflow.com/questions/45451245/how-to-unparse-a-julia-expression
    B     = IOBuffer();              # will use to 'capture' the s_expr in
    Expr1 = ast                      # the expr we want to generate an s_expr for
    Meta.show_sexpr(B, Expr1);       # push s_expr into buffer B
    seek(B, 0);                      # 'rewind' buffer
    str      = read(B, String);      # get buffer contents as string
    close(B);                        # please to be closink after finished, da?


    # load the shared library
    # Note, the library has to be available on a path in $LD_LIBRARY_PATH
    # dm = Libdl.dlopen(joinpath(homedir(), ".local/lib/libdiffmu-wrapper"))
    dm = Libdl.dlopen(libdiffprivhs)

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

    return
end

