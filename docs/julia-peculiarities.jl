

################################################
## 1. Naming collision

#########
# Naming collision when mixing global and local variables with the same names
#
# This test FAILS, probably because inside `f`, in the line `y = a + y`,
# in order to mitigate naming collisions, the outer `y` is being "renamed" to something else,
# and the name `y` in this line already is reserved for the `y` in the LHS
# But as it is not yet defined, when evaluating the RHS, we get the error.
# NOTE: This test only fails in the global scope.

# test1_1
# ------------------------
# y = 1
# function f(a)
#     y = a + y
#     y
# end
# f(2)
# ------------------------
# end


#########
# Naming collision when mixing global and local variables with the same names
#
# This test is for comparison, it works.

# test1_2
# ------------------------
# y = 1
# function test2(a)
#     z = a + y
#     z
# end
# f(2)
# ------------------------
# end


##################################################
## 2. Capturing behaviour:

#########
# Capture behaviour of a function variable `f` (TYPE UNKNOWN)
#
# In the case where the supposedly capture-variable is
# set in a scope, where the function type is UNKNOWN
function test2_1()
    function caller(f, x)
        v = 4
        f(x)
    end

    function test(x)
        x + v + 1
    end

    # ERROR: UndefVarError: v not defined
    caller(test, 3)
end

#########
# Capture behaviour of a function variable `f` (TYPE UNKNOWN)
# (same as test2_1, but this time with lambdas instead of functions
#  => we get the same behaviour)
function test2_2()
    caller(f,x) = begin
        v = 4
        f(x) # <=== The function variable `f` cannot capture the `v`
    end

    test(x) = x + v + 1

    # ERROR: UndefVarError: v not defined
    caller(test,3)
end

#########
# Capture behaviour of a function variable `f` (TYPE KNOWN)
#
# In the case where the supposedly capture-variable is
# set in a scope, where the function type is KNOWN
function test2_3()
    g(f,x) = f(x)

    f(x) = x+y

    y = 10

    # NO Error:
    g(f,1)       # <==== `y` is (probably) captured already here, where the type of `f` is known
                 # This means that we also should also capture-apply the context to the
                 # (types of the) arguments of a function call, not only the (type of) the function itself
end


#########
# Capture behaviour of a function variable `f` (KNOWN & UNKNOWN)
#
# When we do both, we simple get the value of the known case
function test2_4()
    caller(f,x) = begin
        v = 0
        f(x) # <=== The function variable `f` cannot capture the `v`
    end

    test(x) = x + v + 1

    v = 1    # <=== But this `v` is being captured

    # NO Error:
    caller(test,1) # result = 2
end

