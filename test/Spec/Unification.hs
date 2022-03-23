
module Spec.Unification where

import Spec.Base


  -- TODO: Use quickcheck
testUnification = do
  describe "unify" $ do
    it "unifies Int = Int" $ do
      (tc $ unify () (DMInt) (DMInt)) `shouldReturn` ((Right DMInt))

    it "creates a constraint when unification is not yet possible (:∧:)" $ do
      let test = do
            a :: DMMain <- newVar
            b :: DMMain <- newVar
            c :: DMMain <- newVar
            d :: DMMain <- newVar
            unify () (a :∧: b) (c :∧: d)
            return (a,b,c,d)
      let check (a,b,c,d) = do
            ctrs <- getConstraintsByType (Proxy @(IsEqual (DMMain,DMMain)))
            case ctrs of
              [(_ , IsEqual (a₂ :∧: b₂, c₂ :∧: d₂))] ->
                let res = and[ a == a₂,
                               b == b₂,
                               c == c₂,
                               d == d₂ ]
                in return (Right res)
              ctrs -> return (Left ())
      (tc $ (sn test >>= check)) `shouldReturn` (Right (Right True))


