
module Spec.SingleRun where

import Spec.Base

-- testSingleRun p = do
  -- describe "supremum" $ do
  --   it "solves 'max{a,Real} = b' since from Real there is only 1 reflexive path" $ do
  --     let test :: TC _
  --         test = do
  --           a <- newVar
  --           b <- supremum a (IRNum DMReal)
  --           return (a,b)
  --     let check :: (DMTypeOf BaseNumKind, DMTypeOf BaseNumKind) -> TC _
  --         check (TVar a, (IRNum DMReal)) = pure (Right ())
  --         check x                = pure (Left x)
  --     (tcl $ (sn_EW test >>= check)) `shouldReturn` (Right (Right ()))


testSingleRun pp = describe "DPGD" $ do
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
          \ function train_dp(data, labels, eps::Static(), del::Static(), n::Static(), eta::Static()) :: Priv() \n\
          \    model = init_model() \n\
          \    (dim, _) = size(data) \n\
          \    aloss = 0 \n\
          \    for _ in 1:n \n\
          \        for i in 1:dim \n\
          \           d = data[i,:] \n\
          \           l = labels[i,:] \n\
          \           gs = unbounded_gradient(model, d, l) \n\
          \  \n\
          \           gs = undisc_container(clip(L2,gs)) \n\
          \           gs = gaussian_mechanism(2/dim, eps, del, scale_gradient(1/dim,gs)) \n\
          \           model = subtract_gradient(model, scale_gradient(eta * dim, gs)) \n\
          \     #      aloss += loss(d,l,model)/(n*dim) \n\
          \        end \n\
          \    end \n\
          \    model \n\
          \ end"

      ty = "Fun([([NoFun(Matrix<n: τ_30, c: τ_31>[s_23 × s_35](Num(Data))) @ (4.0⋅s_26⋅sqrt(2.0⋅ceil(s_23)⋅(0.0 - ln(s_50)))⋅sqrt(2.0⋅ceil(s_55)⋅(0.0 - ln(s_52))),ceil(s_23)⋅ceil(s_55)⋅s_27 + s_50⋅ceil(s_55) + s_52),NoFun(Matrix<n: τ_85, c: τ_86>[s_40 × s_41](Num(Data))) @ (4.0⋅s_26⋅sqrt(2.0⋅ceil(s_23)⋅(0.0 - ln(s_50)))⋅sqrt(2.0⋅ceil(s_55)⋅(0.0 - ln(s_52))),ceil(s_23)⋅ceil(s_55)⋅s_27 + s_50⋅ceil(s_55) + s_52),NoFun(Num(τ_106[s_26])) @ (0,0),NoFun(Num(τ_108[s_27])) @ (0,0),NoFun(Num(τ_125[s_55])) @ (0,0),NoFun(Num(τ_141[s_57])) @ (∞,∞)] ->* NoFun(Params[s_53](Num(Real[--])))) @ Just [Any,Any,Any,Any,Any,Any]])"

      cs = "constr_21 : [final,worst,global,exact,special] IsLess (0,s_27),\
           \\nconstr_43 : [final,worst,global,exact,special] IsLess (0,s_52),\
           \\nconstr_18 : [final,worst,global,exact,special] IsLess (s_26,1),\
           \\nconstr_40 : [final,worst,global,exact,special] IsLess (0,s_50),\
           \\nconstr_20 : [final,worst,global,exact,special] IsLess (0,s_26),\
           \\nconstr_39 : [final,worst,global,exact,special] IsLessEqual (s_50,1),\
           \\nconstr_42 : [final,worst,global,exact,special] IsLessEqual (s_52,1),\
           \\nconstr_19 : [final,worst,global,exact,special] IsLess (s_27,1)"
  parseEvalString_l_customCheck pp "a DP version of basic gradient descent" ex (ty, cs) (pure $ Right ())


