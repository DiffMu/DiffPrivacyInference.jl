
module Spec.Supremum where

import Spec.Base


testSupremum = do
  describe "supremum" $ do
    let testsup (a :: DMTypeOf k) b c = do
          it ("computes sup{" <> show a <> ", " <> show b <> "} = " <> show c) $ do
            (tc $ sn_EW $ supremum a b) `shouldReturn` (c)

    let testsupl (a :: DMTypeOf k) b c = do
          it ("computes sup{" <> show a <> ", " <> show b <> "} = " <> show c) $ do
            (tcl $ sn_EW $ supremum a b) `shouldReturn` (c)

    let twoId = oneId ⋆! oneId

    testsup ((IRNum DMInt)) ((IRNum DMInt)) (Right $ (IRNum DMInt))
    testsup ((IRNum DMReal)) ((IRNum DMReal)) (Right $ (IRNum DMReal))

    testsup (Num (IRNum DMInt) NonConst) (Num (IRNum DMInt) NonConst)  (Right $ Num (IRNum DMInt) NonConst)
    testsup (Num (IRNum DMInt) NonConst) (Num (IRNum DMReal) NonConst) (Right $ Num (IRNum DMReal) NonConst)

    testsup (Num (IRNum DMInt) (Const twoId)) (Num (IRNum DMInt) (Const twoId)) (Right $ Num (IRNum DMInt) (Const twoId)) -- (Right $ Const (twoId)))
    testsup (Num (IRNum DMInt) (Const (twoId))) (Num (IRNum DMInt) (Const oneId)) (Right $ Num (IRNum DMInt) NonConst)

    testsup (NoFun (Numeric (Num (IRNum DMInt) NonConst)))
            (Fun [([NoFun (Numeric (Num (IRNum DMInt) NonConst)) :@ oneId] :->: (NoFun (Numeric (Num (IRNum DMInt) NonConst)))) :@ Nothing])
            (Left ((UnsatisfiableConstraint "[test]")))


  describe "infimum" $ do
    let testinf (a :: DMTypeOf k) b c = do
          it ("computes inf{" <> show a <> ", " <> show b <> "} = " <> show c) $ do
            (tc $ sn_EW $ infimum a b) `shouldReturn` (c)

    let testinfl (a :: DMTypeOf k) b c = do
          it ("computes inf{" <> show a <> ", " <> show b <> "} = " <> show c) $ do
            (tcl $ sn_EW $ infimum a b) `shouldReturn` (c)

    let twoId = oneId ⋆! oneId

    testinf ((IRNum DMInt)) ((IRNum DMInt)) (Right $ (IRNum DMInt))
    testinfl ((IRNum DMReal)) ((IRNum DMReal)) (Right $ (IRNum DMReal))
    testinf ((IRNum DMInt)) ((IRNum DMReal)) (Right $ (IRNum DMInt))

    testinf (Num (IRNum DMInt) (Const twoId)) (Num (IRNum DMInt) (Const twoId)) (Right $ Num (IRNum DMInt) (Const twoId)) -- (Right $ Const (twoId)))
    testinf (Num (IRNum DMInt) (Const (twoId))) (Num (IRNum DMInt) (Const oneId)) (Left $ (UnsatisfiableConstraint ""))



  describe "advanced supremum" $ do
    it "breaks down Num wrapped sups" $ do
      let term :: TC _
          term = do
            a <- newVar
            b <- newVar
            c <- supremum (Numeric a) (Numeric b)
            return (a,b,c)
          eval (a,b,c) = do
            p0 <- getConstraintsByType (Proxy @(IsSupremum ((DMTypeOf NoFunKind, DMTypeOf NoFunKind) :=: DMTypeOf NoFunKind)))
            p1 <- getConstraintsByType (Proxy @(IsSupremum ((DMTypeOf NumKind, DMTypeOf NumKind) :=: DMTypeOf NumKind)))
            case (p0,p1) of
              -- what should happen is that the same variables (a and b) that were created
              -- above are here inside of the constraint.
              -- We do not know their order, and the sup-result should be a new variable
              -- which is neither a nor b
              ([],[(_ , (IsSupremum ((a', b') :=: c')))])
                | or [and [a == a', b == b', c' /= a', c' /= b']
                     ,and [a == b', b == a', c' /= a', c' /= b']] -> pure $ Right ()
              xs                                                  -> pure $ Left (show xs)
      (tc $ (sn_EW term >>= eval)) `shouldReturn` (Right (Right ()))

    it "solves 'max{a,b} = Int', since there can be nothing smaller than Int" $ do
      let test :: TC _
          test = do
            a <- newVar
            b <- newVar
            c <- supremum a b
            unify () c (IRNum DMInt)
            return (a,b)
      let check :: (DMTypeOf BaseNumKind, DMTypeOf BaseNumKind) -> TC _
          check ((IRNum DMInt), (IRNum DMInt)) = pure (Right ())
          check x              = pure (Left x)
      (tc $ (sn_EW test >>= check)) `shouldReturn` (Right (Right ()))



    -- it "solves 'max{a,Real} = b' since from Real there is only 1 reflexive path." $ do
    --   let test :: TC _
    --       test = do
    --         a <- newVar
    --         b <- supremum a (IRNum DMReal)
    --         return (a,b)
    --   let check :: (DMTypeOf BaseNumKind, DMTypeOf BaseNumKind) -> TC _
    --       check (TVar a, (IRNum DMReal)) = pure (Right ())
    --       check x                = pure (Left x)
    --   (tc $ (sn_EW test >>= check)) `shouldReturn` (Right (Right ()))

    it "does not solve 'max{a,Real} = b' because of current implementation details (issue #133)" $ do
      let test :: TC _
          test = do
            a <- newVar
            b <- supremum a (IRNum DMReal)
            return (a,b)
      let check :: (DMTypeOf BaseNumKind, DMTypeOf BaseNumKind) -> TC _
          check (TVar a, TVar b) = pure (Right ())
          check x                = pure (Left x)
      (tc $ (sn_EW test >>= check)) `shouldReturn` (Right (Right ()))

    it "fails on 'max{a,Real} = Int', since there can be no path Real -> Int" $ do
      let test :: TC _
          test = do
            a <- newVar
            b <- supremum a (IRNum DMReal)
            unify () b (IRNum DMInt)
            return ()
      (tc $ (sn_EW test)) `shouldReturn` (Left ((UnsatisfiableConstraint "test")))

  describe "supremum (with unknown variables)" $ do
    it "does NOT solve 'max{a,Int} = b'" $ do
      let test :: TC _
          test = do
            a <- newVar
            b <- supremum a (IRNum DMInt)
            return (a,b)
      let check (TVar a, TVar b) | a /= b = pure (Right ())
          check x                         = pure (Left x)
      (tc $ (sn_EW test >>= check)) `shouldReturn` (Right (Right ()))

    it "does NOT solve 'max{a,b} = Real'" $ do
      let test :: TC _
          test = do
            a <- newVar
            b <- newVar
            c <- supremum a b
            unify () c (DMReal)
            return (a,b)
      let check (TVar a, TVar b) | a /= b = pure (Right ())
          check x                         = pure (Left x)
      (tc $ (sn_EW test >>= check)) `shouldReturn` (Right (Right ()))

  describe "supremum - special case solving" $ do
    it "solves 'max{a,a} = b'" $ do
      let test :: TC _
          test = do
            a :: DMMain <- newVar
            b <- supremum a a
            return (a,b)
      let check (TVar a, TVar b) | a == b = pure (Right ())
          check x                         = pure (Left x)
      (tc $ (sn test >>= check)) `shouldReturn` (Right (Right ()))
{-  see issue #247
    it "solves 'max{a,Int} = b' since Int is bottom element" $ do
      let test :: TC _
          test = do
            a <- newVar
            b <- supremum a (IRNum DMInt)
            return (a,b)
      let check (TVar a, TVar b) | a == b = pure (Right ())
          check x                         = pure (Left x)
      (tc $ (sn test >>= check)) `shouldReturn` (Right (Right ()))
-}
    it "solves 'max{a,Real} = a' since input and output are the same" $ do
      let test :: TC _
          test = do
            a <- newVar
            b <- supremum a (IRNum DMReal)
            unify () a b
            return a
      (tc $ (sn test)) `shouldReturn` (Right ((IRNum DMReal)))

