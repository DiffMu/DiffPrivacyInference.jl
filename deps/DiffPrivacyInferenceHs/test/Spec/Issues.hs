
module Spec.Issues where

import Spec.Base

testIssues pp = do
  test21 pp
  test25 pp
  test53 pp
  test58 pp
  test59 pp
  test60 pp
  test67 pp
  test116 pp
  test123 pp
  test125 pp
  test127 pp
  test174 pp
  test188 pp
  test272 pp


test21 pp = describe "issue 21 (FLet collection)" $ do
  let ex_1 =
         "  function test()     \n\
         \      f(a) = 1        \n\
         \      x = f(0,0)      \n\
         \      f(a,b) = 2      \n\
         \      x               \n\
         \  end                 "

  -- This one has to fail since #139
  parseEvalFail pp "example variant 1" ex_1 (FLetReorderError "")

  let ex_2 =
         "  function test()     \n\
         \      x = f(0,0)      \n\
         \      f(a) = 1        \n\
         \      f(a,b) = 2      \n\
         \      x               \n\
         \  end                 "

  parseEvalFail pp "example variant 2 (needs to fail)" ex_2 (DemutationDefinitionOrderError "f")


test25 pp = describe "issue 25" $ do
  let ex = " function test() \n\
           \   function a(b) \n\
           \       b + b     \n\
           \   end           \n\
           \   a(1)          \n\
           \ end"

      intc c = NoFun(Numeric (Num (IRNum DMInt) (Const (constCoeff c))))
      ty = Fun([([] :->: intc (Fin 2)) :@ Just []])

  parseEval pp "seems fixed (the example typechecks)" ex (pure ty)


test53 pp = describe "issue 53" $ do
  let ex = "function f(x::Integer) :: Priv() \n"
           <>  "(theta, mu) = (100,x) \n"
           <>  "theta + mu \n"
           <>  "end"
      int = NoFun(Numeric (Num (IRNum DMInt) NonConst))
      ty = Fun([([int :@ (inftyP)] :->*: int) :@ Just [JTInt]])

  parseEval pp "seems fixed (the example typechecks)" ex (pure ty)


test58 pp = describe "issue 58" $ do
  let ex_1 = " function test()                     \n\
                \    function f()                  \n\
                \        a = 3                     \n\
                \        function g(h,z)           \n\
                \            h(z)                  \n\
                \        end                       \n\
                \        function h(b)             \n\
                \            a                     \n\
                \        end                       \n\
                \        c = g(h,a)                \n\
                \        c                         \n\
                \    end                           \n\
                \    f()                           \n\
                \ end"

  let ex_2 = " function test()                     \n\
                \    function f()                  \n\
                \        a = 3                     \n\
                \        function g(h)             \n\
                \            h()                   \n\
                \        end                       \n\
                \        function h()              \n\
                \            a                     \n\
                \        end                       \n\
                \        g(h)                      \n\
                \    end                           \n\
                \    f()                           \n\
                \ end"

           -- computed by julia

      intc c = NoFun(Numeric (Num (IRNum DMInt) (Const (constCoeff c))))
      ty = Fun([([] :->: intc (Fin 3)) :@ Just []])

  parseEval pp "example variant 1" ex_1 (pure ty)
  parseEval pp "example variant 2" ex_2 (pure ty)


test59 pp = describe "issue 59" $ do
  let ex_1 = " function test()                   \n\
             \    function f(a)                  \n\
             \        function g(h)              \n\
             \            h()                    \n\
             \        end                        \n\
             \        function h()               \n\
             \            a                      \n\
             \        end                        \n\
             \        function h()               \n\
             \            a                      \n\
             \        end                        \n\
             \        g(h)                       \n\
             \    end                            \n\
             \    f(3)                           \n\
             \ end                               "

  let ex_1_good
         = " function test()                 \n\
           \    function f(a)                  \n\
           \        function g(h)              \n\
           \            h()                    \n\
           \        end                        \n\
           \        function h()               \n\
           \            a                      \n\
           \        end                        \n\
           \        g(h)                       \n\
           \    end                            \n\
           \    f(3)                           \n\
           \ end                               "

      intc c = NoFun(Numeric (Num (IRNum DMInt) (Const (constCoeff c))))
      ty = Fun([([] :->: intc (Fin 3)) :@ Just []])

  parseEvalFail pp "example variant 1 (bad)" ex_1 (FLetReorderError "")
  parseEval pp "example variant 1 (good)" ex_1_good (pure ty)


  let ex_2 = " function test()                   \n\
             \    function f(a,b)                \n\
             \        function g(h)              \n\
             \            h()                    \n\
             \        end                        \n\
             \        function h()               \n\
             \            b                      \n\
             \        end                        \n\
             \        function h()               \n\
             \            a                      \n\
             \        end                        \n\
             \        g(h)                       \n\
             \    end                            \n\
             \    f(2,3)                         \n\
             \ end                               "

  parseEvalFail pp "example variant 2" ex_2 (FLetReorderError "")



test60 pp = describe "issue 60" $ do
  let ex_1 = " function test()                  \n\
             \    function f(a)                 \n\
             \        function h(b::Integer)    \n\
             \            a                     \n\
             \        end                       \n\
             \        function g(h,a)           \n\
             \            h(a) + h(a)           \n\
             \        end                       \n\
             \        g(h,a)                    \n\
             \    end                           \n\
             \    f(3)                          \n\
             \ end"

      intc c = NoFun(Numeric (Num (IRNum DMInt) (Const (constCoeff c))))
      ty = Fun([([] :->: intc (Fin 6)) :@ Just []])

  parseEval pp "example variant 1" ex_1 (pure ty)


test67 pp = describe "issue 67 (same juliatype choice overwriting)" $ do
  let ex_1 =
         " function test()          \n\
         \     function f(a)        \n\
         \         function h(b)    \n\
         \             2*b+a        \n\
         \         end              \n\
         \         function g(h,a)  \n\
         \             h(a)         \n\
         \         end              \n\
         \         a = g(h,a)       \n\
         \         a = g(h,a)       \n\
         \         function h(b)    \n\
         \             a            \n\
         \         end              \n\
         \         a = g(h,a)       \n\
         \         a                \n\
         \     end                  \n\
         \     f(1)                 \n\
         \ end                      "

  parseEvalFail pp "example variant 1" ex_1 (DemutationVariableAccessTypeError "")


  let ex_2 =
         " function test()      \n\
         \     function h(b)    \n\
         \         2            \n\
         \     end              \n\
         \     function h(b)    \n\
         \         1            \n\
         \     end              \n\
         \     h(0)             \n\
         \ end                  "

  parseEvalFail pp "example variant 2" ex_2 (FLetReorderError "")

  let ex_3 =
         " function test()      \n\
         \     function h(b)    \n\
         \         3            \n\
         \     end              \n\
         \     function h(b)    \n\
         \         2            \n\
         \     end              \n\
         \     function h(b)    \n\
         \         1            \n\
         \     end              \n\
         \     h(0)             \n\
         \ end                  "

  parseEvalFail pp "example variant 3" ex_3 (FLetReorderError "")


test116 pp = describe "issue 116 (constant assignment in loop)" $ do
  let ex_1 = "   function sloop(x::Integer)   \n\
              \             for _ in 1:10      \n\
              \                 x = 100        \n\
              \             end                \n\
              \             x                  \n\
              \         end                    "

      int = NoFun(Numeric (Num (IRNum DMInt) NonConst))
      ty = do pure $ Fun([([int :@ (constCoeff (Fin 0))] :->: int) :@ Just [JTInt]])

  parseEvalUnify pp "gives non-const input and output" ex_1 (ty)

test123 pp = describe "issue 123 (Rewind side effects of quick-path-check in supremum search)" $ do
  let ex_1 = "   function ifelse(x,y::Integer)    \n\
              \             if y == 1             \n\
              \                 clone(x)          \n\
              \             elseif y==2           \n\
              \                 clone(x)          \n\
              \             else                  \n\
              \                 clone(y)          \n\
              \             end                   \n\
              \          end                      "

      intnc = NoFun(Numeric (Num (IRNum DMInt) NonConst))
      ty = Fun([([intnc :@ (constCoeff (Fin 2)) , intnc :@ inftyS] :->: intnc) :@ Just [JTAny, JTInt]])

  parseEvalUnify_customCheck pp "indirect via code succeeds" ex_1 (pure ty) (return (Right ()))

  it "direct construction of constraint succeeds" $ do
    let test :: TC _
        test = do
          a <- newVar
          b <- newVar
          c <- supremum a (Numeric (Num b NonConst))
          return (a, (Numeric (Num b NonConst)))
    let check :: (DMTypeOf NoFunKind, DMTypeOf NoFunKind) -> TC (Either () ())
        check _ = return (Right ())
    (tc $ (sn_EW test >>= check)) `shouldReturn` (Right (Right ()))

test125 pp = describe "issue 125 (Unify in Non-constification)" $ do
  let ex_1 = "   function sloop(x::Integer)   \n\
              \             for i in 1:10      \n\
              \                 x = x+x        \n\
              \             end                \n\
              \             x                  \n\
              \         end                    "

      intc_nc c = NoFun(Numeric (Num (IRNum DMInt) c))
      int = NoFun(Numeric (Num (IRNum DMInt) NonConst))
      ty = do c <- newVar ; pure $ Fun([([intc_nc c :@ (constCoeff (Fin 1024))] :->: int) :@ Just [JTInt]])

  parseEvalUnify pp "example variant 1" ex_1 (ty)


test127 pp = describe "issue 127 (TLet in loop)" $ do
  let ex_1 = "  function sloop(x::Integer, n::Integer)   \n\
              \      for i in 1:2:n                       \n\
              \          (x,z) = (x+n,1)                  \n\
              \      end                                  \n\
              \      x                                    \n\
              \  end                                      "

      -- intc_nc c = NoFun(Numeric (Num (IRNum DMInt) c))
      int = NoFun(Numeric (Num (IRNum DMInt) NonConst))

      ty = do pure $ Fun([([int :@ (constCoeff oneId) , int :@ (inftyS)] :->: int) :@ Just [JTInt,JTInt]])

  parseEval pp "example variant 1" ex_1 ty


test174 pp = describe "issue 174 (count function)" $ do
  let ex_1 = " function countn(f:: Function, d::Matrix) :: Priv() \n\
             \   (dim, _) = size(d)                              \n\
             \   counter = 0                                     \n\
             \   for i in 1:dim                                  \n\
             \     dd = d[i,:]                                   \n\
             \     if f(dd) == 1                                 \n\
             \       counter = counter + 1                       \n\
             \     else                                          \n\
             \       counter = clone(counter)                    \n\
             \     end                                           \n\
             \   end                                             \n\
             \   counter                                         \n\
             \ end "

      -- intc_nc c = NoFun(Numeric (Num (IRNum DMInt) c))
      int = NoFun(Numeric (Num (IRNum DMInt) NonConst))

      ty = do
        τ_31 <- newVar
        τ_10 <- newVar 
        s_8  <- newVar 
        τ_82 <- newVar
        s_23 <- newVar
        τa_26 <- newVar
        s_9 <- newVar
        return $ Fun([([Fun([([NoFun(DMVec τ_31 τ_10 s_8 τ_82) :@ s_23] :->: NoFun(τa_26)) :@ Nothing]) :@ (inftyS,inftyS),NoFun(DMMat τ_31 τ_10 s_9 s_8 τ_82) :@ (inftyS,inftyS)] :->*: int) :@ Just [JTFunction ,JTMatrix JTAny]])


  parseEvalUnify_customCheck pp "typechecks" ex_1 (ty) $
    do 
      c <- getConstraintsByType (Proxy @(IsTypeOpResult DMTypeOp))
      cl <- getConstraintsByType (Proxy @(IsLessEqual (Sensitivity, Sensitivity)))
      cs <- getAllConstraints 
      case (length c, length cl, length cs) of
        (1,1,2) -> return (Right ())
        _     -> return $ Left (show cs)



test188 pp = describe "issue 188 (holes)" $ do
  let ex_1 = "function testScale(_, x::Integer, xs)  \n\
             \    _ = clone(x)              \n\
             \   (dim, _) = size(xs)        \n\
             \   dim + x                    \n\
             \end                           "

  parseEvalUnify pp "holes can be used in assignments and function arguments " ex_1 newVar

test272 pp = describe "issue 272 (self aliasing)" $ do
  let ex_1 = " function make_3tuple(a)          \n\
              \   b = clone(a)                   \n\
              \   (b,b,b)                        \n\
              \ end                              \n\
              \ function bad(x)                  \n\
              \   (a,b,c) = make_3tuple(x)       \n\
              \   internal_mutate!(a)            \n\
              \ end                              "

  parseEvalFail pp "example variant 1 (needs to fail)" ex_1 (DemutationError "")

