
module Spec.Rules where

import Spec.Base


testCheck_Rules = do
  describe "rules-privacy-slet" $ do
    it "forwards inner type correctly" $ do
      let term = SLet ((UserTeVar ((UserProcVar $ Symbol "x")))) (Located UnknownLoc (Sng 1.0 (JTReal))) (Located UnknownLoc (Ret (Located UnknownLoc $ Var (((UserTeVar (UserProcVar $ Symbol "x")))))))
      let f = checkPriv def (Located UnknownLoc term)
      -- do
      --       let tres = checkPriv term def
      --       -- let (tres'',_) = runState (extractDelayed def tres) def
      --       -- tres''
      --       tres
      (tc $ sn $ f) `shouldReturn` (Right $ NoFun (Numeric (Num DMReal (Const (oneId)))))


