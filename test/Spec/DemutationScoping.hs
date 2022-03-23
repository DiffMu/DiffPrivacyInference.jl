
module Spec.DemutationScoping where

import Spec.Base


testDemutationScoping pp = do
  describe "Variables can be either mutated, or captured. Not both. (#148)" $ do
    testDScope01 pp
    testDScope02 pp
    testDScope03 pp


testDScope01 pp = do
  let exa = " function test()   \n\
           \   a = 3           \n\
           \   function f(b)   \n\
           \     a             \n\
           \   end             \n\
           \   f(0)             \n\
           \ end               "

      intc c = NoFun(Numeric (Num DMInt (Const (constCoeff c))))
      ty = Fun([([] :->: intc (Fin 3)) :@ Just []])

  parseEval pp "01a works (capturing variables is allowed)" exa (pure ty)

  let exb = " function test()    \n\
            \   function f(x)  \n\
            \     a = x + 1    \n\
            \     a            \n\
            \   end            \n\
            \   function g(x)  \n\
            \     a = x + 2    \n\
            \     a            \n\
            \   end            \n\
            \   f(1) * f(3)    \n\
            \ end              "

      intc c = NoFun(Numeric (Num DMInt (Const (constCoeff c))))
      ty = Fun([([] :->: intc (Fin 8)) :@ Just []])

  parseEval pp "01b works (same named variables in disjunct scopes is allowed)" exb(pure ty)

testDScope02 pp = do
  let exa = " function test()   \n\
           \   a = 3           \n\
           \   function f(b)   \n\
           \     a             \n\
           \   end             \n\
           \   a = 4           \n\
           \   f(0)             \n\
           \ end               "

  parseEvalFail pp "02a fails (capturing variables is not allowed if they are mutated)" exa (DemutationVariableAccessTypeError "")

  let exb = " function test()    \n\
            \   function f(a)    \n\
            \     a = 0          \n\
            \     function g()   \n\
            \       a = 3        \n\
            \       4            \n\
            \     end            \n\
            \     g()            \n\
            \     a              \n\
            \   end              \n\
            \   f(1)             \n\
            \ end                "

  parseEvalFail pp "02b fails (mutating a variable from outer scope (local var) is not allowed)" exb (DemutationVariableAccessTypeError "")


  let exc = " function test()    \n\
            \   function f(a)    \n\
            \     function g()   \n\
            \       a = 3        \n\
            \       4            \n\
            \     end            \n\
            \     g()            \n\
            \     a              \n\
            \   end              \n\
            \   f(1)             \n\
            \ end                "

  parseEvalFail pp "02c fails (mutating a variable from outer scope (fun arg) is not allowed)" exc (DemutationVariableAccessTypeError "")


testDScope03 pp = do
  let ex = " function test()    \n\
           \   a = 2            \n\
           \   function f(a)    \n\
           \     a = 3 + a      \n\
           \     function g()   \n\
           \       4            \n\
           \     end            \n\
           \     g() + a        \n\
           \   end              \n\
           \   f(1) + a         \n\
           \ end                "

      intc c = NoFun(Numeric (Num DMInt (Const (constCoeff c))))
      ty = Fun([([] :->: intc (Fin 10)) :@ Just []])

  parseEval pp "03 works (mutation of function arguments is allowed, even if they are same-named)" ex (pure ty)


