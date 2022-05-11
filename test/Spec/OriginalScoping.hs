
module Spec.OriginalScoping where

import Spec.Base

-- Because of #138, our scopes do not allow
-- the reassignment of variables with a value
-- of a different type. In this file we keep the previously
-- written tests, which did this, are kept, but now
-- we expect them to fail because of this new rule.
--
-- 2022-01-04 Because of #144, some of the tests work again
--
-- 2022-01-25 Because of #172, some of the tests not allowed
--            anymore, again
--

testOriginalScoping pp = do
  describe "Scopes do not allow reassignment with different types (#138)" $ do
    testScope01 pp
    testScope02 pp
    testScope03 pp
    testScope04 pp
    testScope05 pp
    testScope06 pp
    testScope07 pp
    testScope08 pp


testScope01 pp = do
  let ex = " function test()               \n\
           \   function f(a)               \n\
           \      backup = a               \n\
           \      b = a * 2                \n\
           \      a = b                    \n\
           \      a = 3 * a                \n\
           \      b = a * b                \n\
           \      result = backup + a + b  \n\
           \      result                   \n\
           \   end                         \n\
           \   f(1)                        \n\
           \ end"
           -- backup = 1
           -- b = 1 * 2 = 2
           -- a = 2
           -- a = 3 * 2 = 6
           -- b = 6 * 2 = 12
           -- result = 1 + 6 + 12 = 19

      intc c = NoFun(Numeric (Num (IRNum DMInt) (Const (constCoeff c))))
      ty = Fun([([] :->: intc (Fin 19)) :@ Just []])

  -- parseEval pp "01 works" ex (pure ty)
  parseEvalFail pp "01 fails" ex (DemutationMovedVariableAccessError "")



testScope02 pp = do
  let ex = " function test()          \n\
           \   function scope(z)      \n\
           \     y = 100              \n\
           \     g(x) = x+y           \n\
           \     y = g(z)             \n\
           \     g(z)                 \n\
           \   end                    \n\
           \   scope(3)               \n\
           \ end"

           -- y = 100
           -- g{y}(x) = x + y
           -- y = g{100}(3) = 3 + 100 = 103
           -- g{103}(3) = 3 + 103 = 106

      intc c = NoFun(Numeric (Num (IRNum DMInt) (Const (constCoeff c))))
      ty = Fun([([] :->: intc (Fin 106)) :@ Just []])

  -- parseEval pp "02 works" ex (pure ty)
  parseEvalFail pp "02 fails" ex (DemutationVariableAccessTypeError "")


testScope03 pp = do
  let ex = " function test()          \n\
           \   function scope(z)      \n\
           \      g() = 0             \n\
           \      h(x) = g(2)         \n\
           \      y = 100             \n\
           \      g(x) = x*y          \n\
           \      y = h(1)            \n\
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
      ty = Fun([([] :->: intc (Fin 600)) :@ Just []])

  -- parseEval pp "03 works" ex (pure ty)
  parseEvalFail pp "03 fails" ex (DemutationVariableAccessTypeError "")


testScope04 pp = do
  let ex_bad = " function test()                   \n\
           \    function f(a)                  \n\
           \        function h(b)              \n\
           \            i(b) = 2*b + a         \n\
           \            i(b*5)                 \n\
           \        end                        \n\
           \        function g(h,a)            \n\
           \            x = h(a*7)             \n\
           \            y = h(a*7)             \n\
           \            x + y                  \n\
           \        end                        \n\
           \        a = g(h,a)                 \n\
           \        a = g(h,a)                 \n\
           \        function h(b)              \n\
           \            a*11                   \n\
           \        end                        \n\
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
           \        function g(h,a)            \n\
           \            x = h(a*7)             \n\
           \            y = h(a*7)             \n\
           \            x + y                  \n\
           \        end                        \n\
           \        a = g(h,a)                 \n\
           \        a = g(h,a)                 \n\
           \        function h(b::Integer)     \n\
           \            a*11                   \n\
           \        end                        \n\
           \        a = g(h,a)                 \n\
           \        a                          \n\
           \    end                            \n\
           \    f(13)                          \n\
           \ end"


      intc c = NoFun(Numeric (Num (IRNum DMInt) (Const (constCoeff c))))
      ty = Fun([([] :->: intc (Fin 138424)) :@ Just []])

  parseEvalFail pp "04 (bad) fails" ex_bad (DemutationVariableAccessTypeError "")
  -- parseEval pp "04 (good)" ex (pure ty)
  parseEvalFail pp "04 (good) fails" ex (DemutationVariableAccessTypeError "")


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
            \      a = 7                  \n\
            \      function g(ff)         \n\
            \        (a,b) -> ff(a,b)     \n\
            \      end                    \n\
            \      function h(a,b)        \n\
            \        b = 3                \n\
            \        a + b                \n\
            \      end                    \n\
            \      g(h)(a,b)              \n\
            \    end                      \n\
            \    y = b + 12               \n\
            \    b = 9                    \n\
            \    x = a                    \n\
            \    a = 23                   \n\
            \    f(x,y)                   \n\
            \  end                        "

      intc c = NoFun(Numeric (Num (IRNum DMInt) (Const (constCoeff c))))
      ty1 = Fun([([] :->: intc (Fin 10)) :@ Just []])

  parseEval pp "06 works" ex1 (pure ty1)


---------------------------------------------------------------------
-- Here are new tests, for testing #138.


testScope07 pp = do
  let ex = " function test7()               \n\
           \   c = 0                        \n\
           \   function apply(f)            \n\
           \     x -> f(x)                  \n\
           \   end                          \n\
           \   c = 1                        \n\
           \   g = apply(x -> x + c)        \n\
           \   c = 4                        \n\
           \   g(1)                         \n\
           \ end                            "

      intc c = NoFun(Numeric (Num (IRNum DMInt) (Const (constCoeff c))))
      ty = Fun([([] :->: intc (Fin 5)) :@ Just []])

  -- parseEval pp "07 works" ex (pure ty)
  parseEvalFail pp "07 fails" ex (DemutationVariableAccessTypeError "")

testScope08 pp = do
  let ex1 = " function test9()           \n\
            \   a = 0                    \n\
            \   function f1()            \n\
            \     x1 = a                 \n\
            \     function f2()          \n\
            \       x2 = a               \n\
            \       function f3()        \n\
            \         x3 = a             \n\
            \         function f4()      \n\
            \           x1 * x2 * x3     \n\
            \         end                \n\
            \       end                  \n\
            \     end                    \n\
            \   end                      \n\
            \   a = 2                    \n\
            \   r1 = f1()                \n\
            \   a = 3                    \n\
            \   r2 = r1()                \n\
            \   a = 4                    \n\
            \   r3 = r2()                \n\
            \   a = 5                    \n\
            \   r4 = r3()                \n\
            \   r4                       \n\
            \ end                        "

      ex2 = " function test9()                         \n\
            \   a = 0                                  \n\
            \   function f1()                          \n\
            \     x1 = a                               \n\
            \     function f2()                        \n\
            \       x2 = a                             \n\
            \       function f3(g)                     \n\
            \         x3 = a                           \n\
            \         x4 = g(9*a)                      \n\
            \         f4 = () -> x1 * x2 * x3 * x4     \n\
            \         f4                               \n\
            \       end                                \n\
            \       f3                                 \n\
            \     end                                  \n\
            \     x1 = a + a                           \n\
            \     f2                                   \n\
            \   end                                    \n\
            \   function g₀(x)                         \n\
            \     x + a                                \n\
            \   end                                    \n\
            \   a = 2                                  \n\
            \   r1 = f1()                              \n\
            \   a = 3                                  \n\
            \   r2 = r1()                              \n\
            \   a = 4                                  \n\
            \   r3 = r2(g₀)                            \n\
            \   a = 5                                  \n\
            \   r4 = r3()                              \n\
            \   r4                                     \n\
            \ end                                      "


      intc c = NoFun(Numeric (Num (IRNum DMInt) (Const (constCoeff c))))
      ty1 = Fun([([] :->: intc (Fin 24)) :@ Just []])
      ty2 = Fun([([] :->: intc (Fin 1920)) :@ Just []])

  -- parseEval pp "08 (version 1) works" ex (pure ty1)
  -- parseEval pp "08 (version 2) works" ex (pure ty2)
  parseEvalFail pp "08 (version 1) fails" ex1 (DemutationMovedVariableAccessError "")
  parseEvalFail pp "08 (version 2) fails" ex2 (DemutationMovedVariableAccessError "")





