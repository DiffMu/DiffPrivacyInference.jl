
module Spec.Scoping where

import Spec.Base

testScoping pp = do
  describe "Scoping test" $ do
    testScope01 pp
    testScope02 pp
    testScope03 pp
    testScope04 pp
    testScope05 pp
    testScope06 pp


testScope01 pp = do
  let ex = " function test()                \n\
           \   function f(a)                \n\
           \      backup = a * 1            \n\
           \      b = a * 2                 \n\
           \      a = b * 1                  \n\
           \      a = 3 * a               \n\
           \      b = a * b               \n\
           \      result = backup + a + b \n\
           \      result                    \n\
           \   end                          \n\
           \   f(1)                         \n\
           \ end"
           -- backup = 1
           -- b = 1 * 2 = 2
           -- a1 = 2
           -- a2 = 3 * 2 = 6
           -- b1 = 6 * 2 = 12
           -- result = 1 + 6 + 12 = 19

      intc c = NoFun(Numeric (Num (IRNum DMInt) (Const (constCoeff c))))
      ty = Fun([([] :->: intc (Fin 19)) :@ Just []])

  parseEval pp "01 works" ex (pure ty)


testScope02 pp = do
  let ex = " function test()          \n\
           \   function scope(z)      \n\
           \     y = 100              \n\
           \     g(x) = x+y           \n\
           \     y1 = g(z)            \n\
           \     g(z)                 \n\
           \   end                    \n\
           \   scope(3)               \n\
           \ end"

           -- y = 100
           -- g{y}(x) = x + y
           -- y = g{100}(3) = 3 + 100 = 103
           -- g{103}(3) = 3 + 103 = 106

      intc c = NoFun(Numeric (Num (IRNum DMInt) (Const (constCoeff c))))
      ty = Fun([([] :->: intc (Fin 103)) :@ Just []])

  parseEval pp "02 works" ex (pure ty)


testScope03 pp = do
  let ex = " function test()          \n\
           \   function scope(z)      \n\
           \      y = 100             \n\
           \      g() = 0             \n\
           \      g(x) = x*y          \n\
           \      h(x) = g(2)         \n\
           \      y2 = h(1)           \n\
           \      g(z)                \n\
           \   end                    \n\
           \   scope(3)               \n\
           \ end"

           -- h{g}(x) = g(2)
           -- y = 100
           -- g{y}(x) = x*y
           -- y = h{g{100}}(1) = g{100}(2) = 2*100 = 200
           -- g{200}(3) = 3*200 = 600

      intc c = NoFun(Numeric (Num (IRNum DMInt) (Const (constCoeff c))))
      ty = Fun([([] :->: intc (Fin 300)) :@ Just []])

  parseEval pp "03 works" ex (pure ty)


testScope04 pp = do
  let ex_bad = "function test()                \n\
           \    function f(a)                  \n\
           \        function h(b)              \n\
           \            i(b) = 2*b + a         \n\
           \            i(b*5)                 \n\
           \        end                        \n\
           \        function h(b)              \n\
           \            a*11                   \n\
           \        end                        \n\
           \        function g(h,a)            \n\
           \            x = h(a*7)             \n\
           \            y = h(a*7)             \n\
           \            x + y                  \n\
           \        end                        \n\
           \        a = g(h,a)                 \n\
           \        a = g(h,a)                 \n\
           \        a = g(h,a)                 \n\
           \        a                          \n\
           \    end                            \n\
           \    f(13)                          \n\
           \ end"

  let ex = " function test()                   \n\
           \    function f(a)                  \n\
           \        function h(b)              \n\
           \            i(b) = 2*b + a         \n\
           \            i(b*5)                 \n\
           \        end                        \n\
           \        function h(b::Integer)     \n\
           \            a*11                   \n\
           \        end                        \n\
           \        function g(h,a)            \n\
           \            x = h(a*7)             \n\
           \            y = h(a*7)             \n\
           \            x + y                  \n\
           \        end                        \n\
           \        a1 = g(h,a)                \n\
           \        a2 = g(h,a1)               \n\
           \        a3 = g(h,a2)               \n\
           \        a3                         \n\
           \    end                            \n\
           \    f(13)                          \n\
           \ end"


      intc c = NoFun(Numeric (Num (IRNum DMInt) (Const (constCoeff c))))
      ty = Fun([([] :->: intc (Fin 286)) :@ Just []])

  parseEvalFail pp "04 (bad)" ex_bad (DemutationVariableAccessTypeError "")
  parseEvalUnify_customCheck pp "04 (good)" ex (pure ty) (pure $ Right ())

testScope05 pp = do
  let ex1 = "function test()        \n\
           \     y = 1              \n\
           \     function foo4(y)   \n\
           \        g = a -> a + y  \n\
           \     end                \n\
           \     foo4(123)(1)       \n\
           \  end"
      ex2 = "function test2()       \n\
           \     y = 1              \n\
           \     g = a -> a + y     \n\
           \     function foo4(y)   \n\
           \        g               \n\
           \     end                \n\
           \     foo4(123)(1)       \n\
           \  end"

      intc c = NoFun(Numeric (Num (IRNum DMInt) (Const (constCoeff c))))
      ty1 = Fun([([] :->: intc (Fin 124)) :@ Just []])
      ty2 = Fun([([] :->: intc (Fin 2)) :@ Just []])

  parseEval pp "05 (inside)" ex1 (pure ty1)
  parseEval pp "05 (outside)" ex2 (pure ty2)

testScope06 pp = do
  let ex1 = "  function test()            \n\
            \    a = 3                    \n\
            \    b = 5                    \n\
            \    function f(a,b)          \n\
            \      a1 = 7                 \n\
            \      function g(ff)         \n\
            \        (a,b) -> ff(a,b)     \n\
            \      end                    \n\
            \      function h(a,b)        \n\
            \        b1 = 3               \n\
            \        a + b1               \n\
            \      end                    \n\
            \      g(h)(a1,b)             \n\
            \    end                      \n\
            \    y = b + 12               \n\
            \    b2 = 9                   \n\
            \    x = a                    \n\
            \    a2 = 12                  \n\
            \    f(x,y)                   \n\
            \  end                        "

      intc c = NoFun(Numeric (Num (IRNum DMInt) (Const (constCoeff c))))
      ty1 = Fun([([] :->: intc (Fin 10)) :@ Just []])

  parseEval pp "06 works" ex1 (pure ty1)


