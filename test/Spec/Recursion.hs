
module Spec.Recursion where

import Spec.Base

-- We do not allow recursion. See #73 for details and descriptions of these tests.

testRecursion pp = do
  describe "Recursion is not allowed." $ do

    let exSimple = " function f()   \n\
            \   function g() \n\
            \     f()        \n\
            \   end          \n\
            \ end            "

    parseEvalFail pp "Simple recursion not allowed." exSimple (ParseError "" Nothing 0 0)

    let exCase1 = "  f = (x) -> 0     \n\
                  \  g = (x) -> f(x)  \n\
                  \  f = (x) -> g(x)  "

    let exCase2 = " function f(x)  \n\
                  \   0            \n\
                  \ end            \n\
                  \ function g(x)  \n\
                  \   f(x)         \n\
                  \ end            \n\
                  \ function f(x)  \n\
                  \   g(x)         \n\
                  \ end            "

    let exCase3 = " f = (x) -> 0   \n\
                  \ function g(x)  \n\
                  \   f(x)         \n\
                  \ end            \n\
                  \ function f(x)  \n\
                  \   g(x)         \n\
                  \ end            "

    let exCase4 = " function f(x)    \n\
                  \   0              \n\
                  \ end              \n\
                  \ function g(x)    \n\
                  \   f(x)           \n\
                  \ end              \n\
                  \ f = (x) -> g(x)  "

    let exCase5 = " function f()     \n\
                  \   0              \n\
                  \ end              \n\
                  \ function f(x)    \n\
                  \   0              \n\
                  \ end              \n\
                  \ function g(x)    \n\
                  \   f(x)           \n\
                  \ end              \n\
                  \ f = x -> g(x)    "

    parseEvalFail pp "Mutual recursion not allowed (case 1)." exCase1 (DemutationVariableAccessTypeError "")
    parseEvalFail pp "Mutual recursion not allowed (case 2)." exCase2 (DemutationVariableAccessTypeError "")
    parseEvalFail pp "Mutual recursion not allowed (case 3)." exCase3 (DemutationVariableAccessTypeError "")
    parseEvalFail pp "Mutual recursion not allowed (case 4)." exCase4 (DemutationVariableAccessTypeError "")
    parseEvalFail pp "Mutual recursion not allowed (case 5)." exCase5 (DemutationVariableAccessTypeError "")
