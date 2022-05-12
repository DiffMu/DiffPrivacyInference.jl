
module Spec.TypecheckingExamples where

import Spec.Base
import Data.String

import DiffMu.Typecheck.Constraint.CheapConstraints
import DiffMu.Typecheck.Constraint.IsFunctionArgument


testTypecheckingExamples pp = do
  testSens pp
  testAnnotation pp
  testOps pp
  testPriv pp
  testBlackBox pp
  testSLoop pp
  testSample pp
  testConvert pp
  testMMap pp
  testRet pp
  testCount pp
  testAboveThresh pp
  testPrivFunc pp
--   testDPGD pp
  

testSens :: (String -> IO String) -> SpecWith ()
testSens pp = do
  describe "checkSens" $ do

    parseEvalSimple pp"3 + 7 * 9" (pure $ NoFun (Numeric (Num (IRNum DMInt) (Const (constCoeff (Fin 66))))))
    parseEvalSimple pp"2.2 * 3"   (pure $ NoFun (Numeric (Num (IRNum DMReal) (Const (constCoeff (Fin 6.6000004))))))

    let test = "function test(a)\n"
            <> "  clone(a)\n"
            <> "end"
    let ty   = do
          τ <- newTVar ""
          return $ Fun([([TVar τ :@ oneId] :->: TVar τ) :@ Just [JTAny]])
    parseEvalUnify pp "Checks the identity function" test ty 


testAnnotation :: (String -> IO String) -> SpecWith ()
testAnnotation pp = do
  describe "checkAnnotation" $ do
    let one = "function one(x::Integer) :: Real \n\
             \   1 \n\
             \ end"
        two = "function two(x) :: Integer \n\
             \   2.0 \n\
             \ end"
        three = "function three(x :: MetricVector(Data,L1)) :: MetricVector(Data, LInf) \n\
             \   1*x \n\
             \ end"
        oneint = NoFun(Numeric (Num (IRNum DMInt) (Const oneId)))
        ty = Fun([([oneint :@ zeroId] :->: oneint) :@ Just [JTInt]])
    parseEvalUnify pp "good type" one (pure ty)
    parseEvalFail pp "bad type" two (UnsatisfiableConstraint (""))
    parseEvalFail pp "bad norm" three (UnificationError LInf L1)

testOps :: IsString t => (t -> IO String) -> SpecWith ()
testOps pp = describe "Ops" $ do
    let ex_num = "function foo(w::Integer, x::Integer, y::Integer, z::Integer) \n\
                 \ if z == 1 \n\
                 \    z1 = x + x + y - 3 \n\
                 \    5.0 * z1  \n\
                 \  else \n\
                 \     w1 = w + y/2 \n\
                 \     w1 + x \n\
                 \  end \n\
                 \ end"
        ex_mat = "function foo(x::Matrix{<:Integer}, y::Matrix{<:Integer}, z::Matrix{<:Integer}) \n\
                 \ clone(2.0*x + y - z) \n\
                 \ end"
        ex_vec = "function foo(x::Vector{<:Integer}, y::Vector{<:Integer}, z::Vector{<:Integer}) \n\
                 \ clone(2.0*x + y - z) \n\
                 \ end"
        ex_mat_no = "function foo(x::Matrix{<:Integer}, y::Matrix{<:Integer}, z::Matrix{<:Integer}) \n\
                 \ 2.0*x + y - z \n\
                 \ end"
        ex_vec_no = "function foo(x::Vector{<:Integer}, y::Vector{<:Integer}, z::Vector{<:Integer}) \n\
                 \ 2.0*x + y - z \n\
                 \ end"
        int = NoFun(Numeric (Num (IRNum DMInt) NonConst))
        real = NoFun(Numeric (Num (IRNum DMReal) NonConst))
        ty_num = Fun([([int :@ (constCoeff (Fin 1)), int :@ (constCoeff (Fin 11)), int :@ (constCoeff (Fin 5.5)), int :@ inftyS] :->: real) :@ Just [JTInt, JTInt, JTInt, JTInt]])
        ty_mat :: TC DMMain = do
            n <- newVar
            m <- newVar
            let mat1 = NoFun (DMMat L1 U n m (NoFun (Numeric (Num (IRNum DMInt) NonConst))))
            let mat2 = NoFun (DMMat L1 U n m (NoFun (Numeric (Num (IRNum DMReal) NonConst))))
            return (Fun [([mat1 :@ constCoeff (Fin 2), mat1 :@ constCoeff (Fin 1), mat1 :@ constCoeff (Fin 1)] :->: mat2) :@ Just [JTMatrix JTInt, JTMatrix JTInt, JTMatrix JTInt]])
        ty_vec :: TC DMMain = do
            n <- newVar
            let vec1 = NoFun (DMVec L1 U n (NoFun (Numeric (Num (IRNum DMInt) NonConst))))
            let vec2 = NoFun (DMVec L1 U n (NoFun (Numeric (Num (IRNum DMReal) NonConst))))
            return (Fun [([vec1 :@ constCoeff (Fin 2), vec1 :@ constCoeff (Fin 1), vec1 :@ constCoeff (Fin 1)] :->: vec2) :@ Just [JTVector JTInt, JTVector JTInt, JTVector JTInt]])
    parseEval pp "numeric ops sensitivity" ex_num (pure ty_num)
    parseEvalUnify pp "matrix ops sensitivity" ex_mat (ty_mat)
    parseEvalUnify pp "vector ops sensitivity" ex_vec (ty_vec)
    parseEvalUnify pp "matrix ops no copy" ex_mat_no (ty_mat)
    parseEvalUnify pp "vec ops no copy" ex_vec_no (ty_vec)

testPriv pp = describe "privacies" $ do
    let ret = "function f(x :: Integer) :: Priv() \n\
               \ x + x                 \n\
               \ end"
        inv = "function g(x :: MetricGradient(Integer,L2)) :: Priv() \n\
               \ scale_gradient!(0.1, x) \n\
               \ gaussian_mechanism!(0.1, 0.1, 0.1, x)  \n\
               \ scale_gradient!(100, x) \n\
               \ return \n\
               \ end"
        invv = "function g(x :: MetricVector(Integer,L2)) :: Priv() \n\
               \ x = 0.1 * x \n\
               \ gaussian_mechanism!(0.1, 0.1, 0.1, x)  \n\
               \ clone(200 * x) \n\
               \ end"
        lap = "function g(x :: MetricGradient(Integer,L2)) :: Priv() \n\
               \    scale_gradient!(0.1, x) \n\
               \    laplacian_mechanism!(0.1, 0.1, x)  \n\
               \    scale_gradient!(100, x) \n\
               \    return \n\
               \ end"
        int = NoFun(Numeric (Num (IRNum DMInt) NonConst))
        real = Num (IRNum DMReal) NonConst 
        ty_r = Fun([([int :@ (inftyS, inftyS)] :->*: int) :@ Just [JTInt]])
        ty_i :: TC DMMain = do
            c <- newVar
            n <- newVar
            let gradin = NoFun (DMGrads L2 c n (NoFun (Numeric (Num (IRNum DMInt) NonConst))))
            let gradout = NoFun (DMGrads LInf U n (NoFun (Numeric real)))
            return (Fun ([([gradin :@ (constCoeff (Fin 0.1), constCoeff (Fin 0.1))] :->*: gradout) :@ Just [JTMetricGradient JTInt L2]]))
        ty_iv :: TC DMMain = do
            c <- newVar
            n <- newVar
            let gradin = NoFun (DMVec L2 c n (NoFun (Numeric (Num (IRNum DMInt) NonConst))))
            let gradout = NoFun (DMVec LInf U n (NoFun (Numeric real)))
            return (Fun ([([gradin :@ (constCoeff (Fin 0.1), constCoeff (Fin 0.1))] :->*: gradout) :@ Just [JTMetricVector JTInt L2]]))
        ty_l :: TC DMMain = do
            c <- newVar
            n <- newVar
            let gradin = NoFun (DMGrads L2 c n (NoFun (Numeric (Num (IRNum DMInt) NonConst))))
            let gradout = NoFun (DMGrads LInf U n (NoFun (Numeric real)))
            return (Fun ([([gradin :@ (constCoeff (Fin 0.1), constCoeff (Fin 0))] :->*: gradout) :@ Just [JTMetricGradient JTInt L2]]))
    parseEval pp "return" ret (pure ty_r)
    parseEvalUnify pp "robust" inv (ty_i) -- this is issue #157
    parseEvalUnify pp "robust" invv (ty_iv)
    parseEvalUnify pp "laplace" lap (ty_l)


testBlackBox pp = describe "black box" $ do
    let bb = "function bb(x) :: BlackBox() \n\
             \   100 \n\
             \ end   \n\
             \ function j(x::Integer, y) \n\
             \    z = unbox(bb(y), Integer)     \n\
             \    x / z  \n\
             \ end"
        int = NoFun(Numeric (Num (IRNum DMInt) NonConst))
        real = NoFun(Numeric (Num (IRNum DMReal) NonConst))
        ty = Fun([([int :@ inftyS, real :@ inftyS] :->: real) :@ Just [JTInt, JTAny]])
    parseEvalUnify pp "numeric" bb (pure ty)


testSLoop pp = describe "Sensitivity loop" $ do
    let sloop = "function sloop(x::Integer) \n\
                 \   for i in 1:10 \n\
                 \      x = x + x \n\
                 \   end \n\
                 \   x \n\
                 \end"
        mloop = "function sloop(x::Integer) \n\
                 \   for i in 1:10 \n\
                 \      y = 100   \n\
                 \      x = x + x \n\
                 \      y = x * 1 \n\
                 \   end \n\
                 \   x \n\
                 \end"
        vloop = "function sloop(x::Integer, n::Integer) \n\
                 \   for i in 1:2*n \n\
                 \      x = x + 5 \n\
                 \   end \n\
                 \   x \n\
                 \end"
        vloop2 = "function sloop(x::Integer, n::Integer) \n\
                 \   for i in 1:2:n \n\
                 \      x = x + n \n\
                 \   end \n\
                 \   x \n\
                 \end"
        uloop = "function sloop(x::Integer, n::Integer) \n\
                 \   for i in 1:2:n \n\
                 \      x = 2*x + 5 \n\
                 \   end \n\
                 \   x \n\
                 \end"
        intc_nc c = NoFun(Numeric (Num (IRNum DMInt) c))
        int = NoFun(Numeric (Num (IRNum DMInt) NonConst))
        ty_s  = do c <- newVar ; pure $ Fun([([intc_nc c :@ (constCoeff (Fin 1024))] :->: int) :@ Just [JTInt]])
        ty_v  = do c <- newVar ; pure $ Fun([([intc_nc c :@ (constCoeff (Fin 1)), int :@ inftyS] :->: int) :@ Just [JTInt, JTInt]])
        ty_v2 = do c <- newVar ; pure $ Fun([([intc_nc c :@ (constCoeff (Fin 1)), int :@ (inftyS)] :->: int) :@ Just [JTInt, JTInt]])
    parseEvalUnify pp "static" sloop (ty_s)
    parseEvalUnify pp "overwriting" mloop (ty_s)
    parseEvalUnify pp "variable" vloop (ty_v)
    parseEvalUnify pp "variable2" vloop2 (ty_v2)
    parseEvalFail pp "variable (bad)" uloop (UnsatisfiableConstraint "")

testSample pp = describe "Sample" $ do
    let ex = "foo(d::Vector) :: BlackBox() = d \n\
              \function bar(data, b, x::Integer) :: Priv() \n\
              \  D, L = sample(b, data, data) \n\
              \  gs = unbox(foo(D[1,:]), Vector{<:Data}, length(D[1,:])) \n\
              \  gs = clip(L2,gs) \n\
              \  gs = undisc_container(gs) \n\
              \  gs = gaussian_mechanism(2, 0.2, 0.3, gs)  \n\
              \  clone(x * gs) \n\
              \end"
        ty = "Fun([([NoFun(Matrix<n: LInf, c: C>[n × m](NoFun(Num(Data)))) @ (0.4⋅(1 / n)⋅m₃,0.3⋅(1 / n)⋅m₃),NoFun(Num(IR Integer[m₃ ©])) @ (0,0),NoFun(Num(IR Integer)) @ (∞,∞)] ->* NoFun(Vector<n: LInf, c: U>[m](NoFun(Num(IR Real))))) @ Just [Any,Any,Integer]])"
        cs = ""
    parseEvalString_l_customCheck pp "" ex (ty, cs) (pure $ Right ())


testConvert pp = describe "Convert" $ do
    let ex = "function foo(x::MetricMatrix(Data,L2)) \n\
      \    x = norm_convert(L1,x) \n\
      \    x \n\
      \ end"
        ty = "Fun([([NoFun(Matrix<n: L2, c: C>[s₂ × n](NoFun(Num(Data)))) @ √(n)] -> NoFun(Matrix<n: L1, c: C>[s₂ × n](NoFun(Num(Data))))) @ Just [MetricMatrix(Data,L2)]])"
        cs = ""
    parseEvalString_l_customCheck pp "" ex (ty, cs) (pure $ Right ())

-- see #258
-- testExponential pp = describe "Exponential mechanism" $ do
--     let ex = "function foo(x,v)::Priv() \n\
--               \  function bar(y) \n\
--               \    x+y \n\
--               \  end \n\
--               \  exponential_mechanism(2,0.1,v,bar) \n\
--               \end"
--         ty = " Fun([([NoFun(Num(τ_15[--])) @ (0.1,0),NoFun(Vector<n: τ_9, c: τ_10>[s_5](NoFun(Num(τ_16[--])))) @ (∞,∞)] ->* NoFun(Num(τ_16[--]))) @ Just [Any,Any]])"
--         cs = "constr_8 : [final,worst,global,exact,special] IsSupremum (τ_15,τ_16) :=: Real"
--     parseEvalString_l_customCheck pp "" ex (ty, cs) (pure $ Right ())

testAboveThresh pp = describe "Above threshold" $ do
    let ex = "function test(qs, d) :: Priv() \n\
              \  above_threshold(qs, 1, d, 100) \n\
              \ end"
        ty = "Fun([([NoFun(Vector<n: N, c: C>[s₁](Fun([([τ₁ @ 1] -> NoFun(Num(IR Real))) @ Nothing]))) @ (∞,∞),τ₁ @ (1,0)] ->* NoFun(Num(IR Integer))) @ Just [Any,Any]])"
        cs = ""
    parseEvalString_customCheck pp "" ex (ty, cs) (pure $ Right ())

testRet pp = describe "Color" $ do
    let ex =  "function f(x::Integer) :: Priv() \n\
              \    (theta, mu) = (100,x) \n\
              \    theta + mu \n\
              \ end"
        int = NoFun(Numeric (Num (IRNum DMInt) NonConst))
        ty = Fun([([int :@ inftyP] :->*: int) :@ Just [JTInt]])
    parseEval pp "Ret" ex (pure ty)
                 
testCount pp = describe "Count" $ do
  let ex = "test(x) = if x == 100 \n\
             \                  True \n\
             \               else \n\
             \                  False \n\
             \               end \n\
             \f(x) = count(test, x)"
      ty :: TC DMMain = do
            c <- newVar
            n <- newVar
            let vec = NoFun (DMVec L1 c n (NoFun (Numeric (Num DMData NonConst))))
            return (Fun ([([vec :@ oneId] :->: (NoFun (Numeric (Num (IRNum DMInt) NonConst)))) :@ Just [JTAny]]))
  parseEvalUnify pp "" ex ty


testMMap pp = describe "Matrix map" $ do
    let ex = "function foo(m::Vector{<:Integer}, y::Integer) \n\
              \   f(x) = 2*x + y\n\
              \   m = map(f,m) \n\
              \   clone(m) \n\
              \end"
        ex_fail = "function foo(m) \n\
              \   f(x::Integer) = 1 \n\
              \   f(x::Real) = 2 \n\
              \   m = map(f,m) \n\
              \   clone(m) \n\
              \end"
        ty :: TC DMMain = do
            c <- newVar
            n <- newVar
            nr <- newVar
            let gradin = NoFun (DMVec nr c n (NoFun (Numeric (Num (IRNum DMInt) NonConst))))
            let gradout = NoFun (DMVec nr U n (NoFun (Numeric (Num (IRNum DMInt) NonConst))))
            return (Fun ([([gradin :@ (constCoeff (Fin 2)), NoFun (Numeric (Num (IRNum DMInt) NonConst)) :@ n] :->: gradout) :@ Just [JTVector JTInt, JTInt]]))
    parseEvalUnify pp "good" ex ty

  
    let ty2 = do
          c <- newVar
          n <- newVar
          nr <- newVar
          τ₁ <- newVar
          τ₂ <- newVar
          k <- newVar
          let gradin = NoFun (DMContainer k nr c n τ₁)
          let gradout = NoFun (DMContainer k nr U n τ₂)
          return (Fun ([([gradin :@ (constCoeff oneId)] :->: gradout) :@ Just [JTAny]]))

    parseEvalUnify_customCheck pp "dispatch (bad)" ex_fail ty2 $ do
      ctrs <- getConstraintsByType (Proxy @(IsChoice (ChoiceHash, [DMTypeOf FunKind])))
      case length ctrs of
        1 -> pure (Right ())
        _ -> pure (Left $ show ctrs)

testPrivFunc pp = describe "PrivacyFunction annotations" $ do
    let ex_good = "function foo(f :: PrivacyFunction) :: Priv() \n\
                   \  f(100) \n\
                   \ end \n\
                   \function bar(x) :: Priv() \n\
                   \  1 \n\
                   \end \n\
                   \function baz() :: Priv() \n\
                   \   foo(bar)\n\
                   \end"
        ex_bad = "function foo(f) :: Priv() \n\
                   \  f(100) \n\
                   \ end \n\
                   \function bar(x) :: Priv() \n\
                   \  1 \n\
                   \end \n\
                   \function baz() :: Priv() \n\
                   \   foo(bar)\n\
                   \end"
        ex_ugly = "function foo(f :: PrivacyFunction) :: Priv() \n\
                   \  f(100) \n\
                   \ end \n\
                   \function bar(x) \n\
                   \  1 \n\
                   \end \n\
                   \function baz() :: Priv() \n\
                   \   foo(bar)\n\
                   \end"
        ex_uglier = "function foo(f :: PrivacyFunction) \n\
                   \  f(100) \n\
                   \ end \n\
                   \function bar(x) ::Priv() \n\
                   \  1 \n\
                   \end \n\
                   \function baz() :: Priv() \n\
                   \   foo(bar)\n\
                   \end"
        cint =  NoFun (Numeric (Num (IRNum DMInt) (Const (constCoeff (Fin 1)))))
        ty_good = Fun([([] :->*: cint) :@ Just []])
    parseEval pp "proper usage" ex_good (pure ty_good)
    parseEvalFail pp "not annotated" ex_bad (TermColorError PrivacyK (""))
    parseEvalFail pp "wrong input" ex_ugly (NoChoiceFoundError "")
    parseEvalFail pp "not a privacy function" ex_uglier (TermColorError PrivacyK (""))
    


testDPGD pp = describe "DPGD" $ do
  let ex = "import Flux \n\
          \ function unbounded_gradient(model::DMModel, d::Vector, l) :: BlackBox() \n\
          \    gs = Flux.gradient(Flux.params(model.model)) do \n\
          \            loss(d,l,model) \n\
          \         end \n\
          \    return DMGrads(gs) \n\
          \ end \n\
          \ function init_model() :: BlackBox() \n\
          \  DMModel(Flux.Chain( \n\
          \          Flux.Dense(28*28,40, Flux.relu), \n\
          \          Flux.Dense(40, 10), \n\
          \          Flux.softmax)) \n\
          \ end \n\
          \ loss(X, y, model) :: BlackBox() = Flux.crossentropy(model.model(X), y) \n\
          \ function train_dp(data, labels, eps::Static(), del::Static(), eta::Static()) :: Priv() \n\
          \    model = init_model() \n\
          \    (dim, _) = size(data) \n\
          \    for i in 1:dim \n\
          \           d = data[i,:] \n\
          \           l = labels[i,:] \n\
          \           gs = unbox(unbounded_gradient(model, d, l), length(model)) \n\
          \           gsc = undisc_container(clip(L2,gs)) \n\
          \           gsg = gaussian_mechanism(2/dim, eps, del, scale_gradient(1/dim,gsc)) \n\
          \           model = subtract_gradient(model, scale_gradient(eta * dim, gsg)) \n\
          \    end \n\
          \    model \n\
          \ end"

      ty = "Fun([([NoFun(Matrix<n: τ_16, c: τ_17>[s_16 × s_28](Num(Data))) @ (2.0⋅sqrt(2.0⋅(0.0 - ln(s_43))⋅ceil(s_16))⋅s_19,s_20⋅ceil(s_16) + s_43),NoFun(Matrix<n: τ_81, c: τ_82>[s_33 × s_34](Num(Data))) @ (2.0⋅sqrt(2.0⋅(0.0 - ln(s_43))⋅ceil(s_16))⋅s_19,s_20⋅ceil(s_16) + s_43),NoFun(Num(τ_101[s_19])) @ (0,0),NoFun(Num(τ_103[s_20])) @ (0,0),NoFun(Num(τ_129[s_47])) @ (∞,∞)] ->* NoFun(Params[s_44](Num(IR Real[--])))) @ Just [Any,Any,Any,Any,Any]])"

      cs = "constr_16 : [final,worst,global,exact,special] IsLess (s_20,1),\
          \\nconstr_38 : [final,worst,global,exact,special] IsLess (0,s_43),\
          \\nconstr_15 : [final,worst,global,exact,special] IsLess (s_19,1),\
          \\nconstr_17 : [final,worst,global,exact,special] IsLess (0,s_19),\
          \\nconstr_18 : [final,worst,global,exact,special] IsLess (0,s_20),\
          \\nconstr_37 : [final,worst,global,exact,special] IsLessEqual (s_43,1)"
  parseEvalString_customCheck pp "a DP version of basic gradient descent" ex (ty, cs) (pure $ Right ())



