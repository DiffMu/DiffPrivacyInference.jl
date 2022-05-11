
module Spec.Subtyping where

import Spec.Base
import DiffMu.Typecheck.Constraint.IsJuliaEqual

(⊑!) :: forall k t. (SingI k, Typeable k, MonadDMTC t) => DMTypeOf k -> DMTypeOf k -> t ()
(⊑!) a b = addConstraintNoMessage (Solvable (IsLessEqual (a,b))) >> pure ()


testSubtyping = do
  let testsub x (a :: DMTypeOf k) b c = do
        it ("computes " <> show a <> " ≤ " <> show b <> " as [" <> show c <> "]") $ do
          (tcb x $ do
              sn_EW ((a ≤! b) ())
              res <- (getUnsolvedConstraintMarkNormal [SolveExact])
              return (fmap (\_ -> ()) res)
            )
            `shouldReturn` (c)

  describe "generic subtyping" $ do
    it "does not resolve 'a ≤ b'." $ do
      let test0 = do
            (a :: DMTypeOf BaseNumKind) <- newVar
            b <- newVar
            a ⊑! b
            return (a,b)
      let correct (TVar a,TVar b) | a /= b = pure (Right ())
          correct x                        = pure (Left x)
      (tc $ (sn_EW test0 >>= correct)) `shouldReturn` (Right (Right ()))


  describe "subtyping of BaseNumKind/NumKind" $ do
    testsub False (IRNum DMInt) (IRNum DMReal) (Right Nothing)
    testsub False (IRNum DMReal) (IRNum DMInt) (Left (UnsatisfiableConstraint "[test]"))

  describe "subtyping of tuples" $ do
    let nci1 = (Numeric (Num (IRNum DMInt) (Const oneId)))
        nci2 = (Numeric (Num (IRNum DMInt) (Const (constCoeff (Fin 2)))))
        nnr  = Numeric (Num (IRNum DMReal) NonConst)

    testsub False (NoFun nci1) (NoFun nnr) (Right Nothing)
    testsub False (DMTup [nci1,nci2]) (DMTup [nci1,nnr]) (Right Nothing)
    testsub False (DMTup [nci1,nci2]) (DMTup [nci2,nnr]) (Left ((UnsatisfiableConstraint "[test]")))
    testsub False (DMTup [nnr,nci2]) (DMTup [nci2,nnr]) (Left ((UnsatisfiableConstraint "[test]")))
    testsub False (DMTup [nnr,nci2]) (nnr) (Left ((UnsatisfiableConstraint "[test]")))


testSubtyping_MaxMinCases = do
  describe "subtyping (paths with max/min cases)" $ do
    it "resolves 'a ≤ Int'." $ do
      let test0 = do
            a <- newVar
            a ⊑! (IRNum DMInt)
            return (a)
      (tc $ (sn_EW test0)) `shouldReturn` (Right (IRNum DMInt))

    it "resolves 'Real ≤ a'." $ do
      let test0 = do
            a <- newVar
            (IRNum DMReal) ⊑! a
            return (a)
      (tc $ (sn_EW test0)) `shouldReturn` (Right (IRNum DMReal))

    it "does NOT resolve 'Int ≤ a'." $ do
      let test0 = do
            a <- newVar
            (DMInt) ⊑! a
            return a
      let isTVar (TVar x) = pure (Right ())
          isTVar a        = pure (Left a)
      (tc $ (sn_EW test0) >>= isTVar) `shouldReturn` (Right (Right ()))

    it "does NOT resolve 'a ≤ Real'." $ do
      let test0 = do
            a <- newVar
            a ⊑! (DMReal)
            return a
      let isTVar (TVar x) = pure (Right ())
          isTVar a        = pure (Left a)
      (tc $ (sn_EW test0) >>= isTVar) `shouldReturn` (Right (Right ()))

    it "resolves 'a ≤ Int[2]' inside NoFun" $ do
      let ty = NoFun (Numeric (Num (IRNum DMInt) (Const (constCoeff (Fin 2)))))
      let test0 = do
            a <- newVar
            a ⊑! ty
            return a
      (tc $ sn_EW test0) `shouldReturn` (Right ty)

    it "partially resolves 'a ≤ (Int[2],Real[--])'" $ do
      let ty1 = (Numeric (Num (IRNum DMInt) (Const (constCoeff (Fin 2)))))
          ty2 = (Numeric (Num (IRNum DMReal) NonConst))
          ty = DMTup [ty1 , ty2]
      let test0 = do
            a <- newVar
            a ⊑! ty
            return a
      let correct :: (DMType) -> TC _
          correct ((DMTup [Numeric (Num (IRNum DMInt) (Const s)), Numeric (Num (IRNum (TVar _)) (TVar _))])) = pure $ Right s
          correct r                                                     = do
            ctrs <- getAllConstraints
            pure $ Left $ "value: " <> showPretty r <> "\n" <> "ctrs: \n" <> showPretty ctrs 
      (tc $ sn_EW test0 >>= correct) `shouldReturn` (Right (Right (constCoeff (Fin 2))))

    it "partially resolves 'a[--] ≤ b' inside NoFun" $ do
      let test0 = do
            a <- newVar
            b <- newVar
            let a'  = NoFun (Numeric (Num a NonConst))

            a' ⊑! b
            return (a', b)
      let correct :: (DMMain,DMMain) -> TC (Either (DMMain,DMMain) ())
          correct (NoFun (Numeric (Num a NonConst)), NoFun (Numeric (Num b NonConst))) | (a /= b) = pure $ Right ()
          correct (x,y)                                                                   = pure $ Left (x,y)
      (tc $ sn_EW test0 >>= correct) `shouldReturn` (Right (Right ()))


testSubtyping_Cycles = do
  describe "subtyping (contracting cycles - only subtyping constraints)" $ do
    it "contracts a two-variable cycle" $ do
      let test0 = do
            (a :: DMMain) <- newVar
            b <- newVar
            a ⊑! b
            b ⊑! a
            return (a,b)
      (tc $ (sn test0 >>= (\(a,b) -> return (a == b)))) `shouldReturn` (Right True)
{- see issue #247
    it "contracts a cycle that has top in it" $ do
      let test01 = do
            (a :: DMTypeOf BaseNumKind) <- newVar
            b <- newVar
            c <- newVar
            d <- newVar
            e <- newVar
            a <- supremum (IRNum DMReal) e -- use supremum here bc the constraint Real <= a would be resolved by a special case
            a ⊑! b
            b ⊑! c
            c ⊑! d
            return (a,b)
      (tc $ (sn test01 >>= (\(a,b) -> return (and [(a == (IRNum DMReal)), (a == b)])))) `shouldReturn` (Right True)

    it "contracts a cycle that has bottom in it" $ do
      let test02 = do
            a <- newVar
            b <- newVar
            c <- newVar
            e <- newVar
            d <- infimum (IRNum DMInt) e -- use inf here bc the constraint d <= Int would be resolved by a special case
            a ⊑! b
            b ⊑! c
            c ⊑! d
            return (a,b)
      (tc $ (sn test02 >>= (\(a,b) -> return (and [(a == (IRNum DMInt)), (a == b)])))) `shouldReturn` (Right True)
-}
    it "contracts a larger cycle with more stuff" $ do
      let test1 = do
            -- the interesting variables a ≤ b
            (a :: DMMain) <- newVar
            b <- newVar
            a ⊑! b

            -- the additional variables b ≤ x ≤ y ≤ a
            x <- newVar
            y <- newVar
            b ⊑! x
            x ⊑! y
            y ⊑! a

            -- some more uninteresting things
            z <- newVar
            s <- newVar
            t <- newVar
            z ⊑! x
            s ⊑! t
            a ⊑! t

            -- we block y and z and a and b to not activate diamond contraction
            (yb :: DMMain) <- newVar
            (zb :: DMMain) <- newVar
            (ab :: DMMain) <- newVar
            (bb :: DMMain) <- newVar
            addConstraintNoMessage (Solvable (IsJuliaEqual (y, yb)))
            addConstraintNoMessage (Solvable (IsJuliaEqual (z, zb)))
            addConstraintNoMessage (Solvable (IsJuliaEqual (a, ab)))
            addConstraintNoMessage (Solvable (IsJuliaEqual (b, bb)))

            -- we are interested in how `a` and `b` turn out
            return (a,b)
      let checkres (a,b) = a == b
      (tc $ (sn test1 >>= (return . checkres))) `shouldReturn` (Right True)

    it "contracts a larger cycle that also has sup/inf constraints" $ do
      let test2 = do
            -- the interesting variables a ≤ b
            (a :: DMMain) <- newVar
            b <- newVar
            a ⊑! b

            -- the additional variables b ≤ x ≤ z ≤ y ≤ a
            (x :: DMMain) <- supremum a b
            (y :: DMMain) <- infimum a x
            z <- newVar
            x ⊑! z
            z ⊑! y

            -- we block y and z and a and b to not activate diamond contraction
            (yb :: DMMain) <- newVar
            (zb :: DMMain) <- newVar
            (ab :: DMMain) <- newVar
            (bb :: DMMain) <- newVar
            addConstraintNoMessage (Solvable (IsJuliaEqual (y, yb)))
            addConstraintNoMessage (Solvable (IsJuliaEqual (z, zb)))
            addConstraintNoMessage (Solvable (IsJuliaEqual (a, ab)))
            addConstraintNoMessage (Solvable (IsJuliaEqual (b, bb)))

            -- we are interested in how `a` and `b` turn out
            return (a,b)
      let checkres (a,b) = a == b
      (tc $ (sn test2 >>= (return . checkres))) `shouldReturn` (Right True)

    it "does not contract a constraint that is not in a cycle" $ do
      let test3 = do
            -- the interesting variables a ≤ b
            (a :: DMMain) <- newVar
            b <- newVar
            a ⊑! b

            -- the additional variables b ≤ x ≤ z and y ≤ a
            (x :: DMMain) <- supremum a b
            (y :: DMMain) <- infimum a x
            z <- newVar
            x ⊑! z

            -- we block y and z and a and b to not activate diamond contraction
            (yb :: DMMain) <- newVar
            (zb :: DMMain) <- newVar
            (ab :: DMMain) <- newVar
            (bb :: DMMain) <- newVar
            addConstraintNoMessage (Solvable (IsJuliaEqual (y, yb)))
            addConstraintNoMessage (Solvable (IsJuliaEqual (z, zb)))
            addConstraintNoMessage (Solvable (IsJuliaEqual (a, ab)))
            addConstraintNoMessage (Solvable (IsJuliaEqual (b, bb)))

            -- we are interested in how `a` and `b` turn out
            return (a,b)
      let checkres (a,b) = not (a == b)
      (tc $ (sn test3 >>= (return . checkres))) `shouldReturn` (Right True)




testSubtyping_ContractEdge = do
  describe "subtyping (contracting edges (degenerate diamonds) - only subtyping constraints)" $ do
    it "contracts a single edge" $ do
      let test0 = do
            (a :: DMMain) <- newVar
            b <- newVar
            a ⊑! b
            return (a,b)
      (tc $ (sn test0 >>= (\(a,b) -> return (a == b)))) `shouldReturn` (Right True)

    it "does contract edge if left variable is only bounded from below and right from above" $ do
      let test1 = do
            -- the interesting variables a ≤ b
            (a :: DMMain) <- newVar
            b <- newVar
            a ⊑! b

            -- the additional variables x ≤ a ≤ b ≤ y
            x <- newVar
            y <- newVar
            x ⊑! a
            b ⊑! y

            -- we are interested in how `a` and `b` turn out
            return (a,b)
      let checkres (a,b) = a == b
      (tc $ (sn test1 >>= (return . checkres))) `shouldReturn` (Right True)

    it "does NOT contract edge if left variable is bounded from above, and right is fixed" $ do
      let test1 = do
            -- main
            (a :: DMMain) <- newVar
            b <- newVar
            a ⊑! b

            -------
            -- blocking constraints
            -- a bounded from above
            x <- newVar
            a ⊑! x

            -- b is fixed
            (y :: DMMain) <- newVar
            addConstraintNoMessage (Solvable (IsJuliaEqual (y, b)))

            -- 2022-04-11
            -- we actually have to make x fixed as well, because else we get a unification from (a <= x)
            -- and after that also of (a <= b)
            addConstraintNoMessage (Solvable (IsJuliaEqual (y, x)))


            return (a,b)
      (tc $ (sn test1 >>= (\(a,b) -> return (a == b)))) `shouldReturn` (Right False)

    it "does NOT contract edge if right variable is bounded from below, and left is fixed" $ do
      let test1 = do
            -- main
            (a :: DMMain) <- newVar
            b <- newVar
            a ⊑! b
            -- blocking constraints
            -- b bounded from below
            y <- newVar
            y ⊑! b

            -- a is fixed
            (x :: DMMain) <- newVar
            addConstraintNoMessage (Solvable (IsJuliaEqual (x, a)))


            -- 2022-04-19
            -- we actually have to make y fixed as well, because else we get a unification from (y <= b)
            -- and after that also of (a <= b)
            addConstraintNoMessage (Solvable (IsJuliaEqual (x, y)))

            return (a,b)
      (tc $ (sn test1 >>= (\(a,b) -> return (a == b)))) `shouldReturn` (Right False)

    it "does NOT contract edge if variables additionally appears in a non subtyping constraint " $ do
      let test1 = do
            -- main
            (a :: DMMain) <- newVar
            b <- newVar
            a ⊑! b
            -- blocking constraint
            (ba :: DMMain) <- newVar
            addConstraintNoMessage (Solvable (IsJuliaEqual (ba, a)))

            (bb :: DMMain) <- newVar
            addConstraintNoMessage (Solvable (IsJuliaEqual (bb, b)))

            return (a,b)
      (tc $ (sn test1 >>= (\(a,b) -> return (a == b)))) `shouldReturn` (Right False)

    it "does ONLY contract those edges which are allowed to be contracted" $ do
      let test1 = do
            -- the interesting variables a ≤ b
            (a :: DMMain) <- newVar
            b <- newVar
            a ⊑! b

            -- the additional variables x ≤ a ≤ b ≤ y
            x <- newVar
            y <- newVar
            x ⊑! a
            b ⊑! y

            -- blocking constraints for x and y
            (y' :: DMMain) <- newVar
            (x' :: DMMain) <- newVar
            addConstraintNoMessage (Solvable (IsJuliaEqual (x, x')))
            addConstraintNoMessage (Solvable (IsJuliaEqual (y, y')))

            -- we are interested in how `a`, `b`, `x`, `y` turn out
            return (x,a,b,y)
      let checkres (x,a,b,y) = ( a == b
                               , x /= y)
      (tc $ (sn test1 >>= (return . checkres))) `shouldReturn` (Right (True , True))

  describe "subtyping (contracting diamonds - subtyping and sup/inf constraints)" $ do
    it "does contract diamond given by sup/inf" $ do
      let test1 :: TC (DMMain,DMMain,DMMain,DMMain)
          test1 = do
            -- the interesting variables a ≤ b
            (a :: DMMain) <- newVar
            (b :: DMMain) <- newVar
            (c :: DMMain) <- supremum a b
            (d :: DMMain) <- infimum a b

            return (d,a,b,c)
      let checkres (d,a,b,c) = (a == c, b == c, a == d, b == d)
      (tc $ (sn test1 >>= (return . checkres))) `shouldReturn` (Right (True,True,True,True))

    it "does contract diamond even if lower/upper end are bound from below/above" $ do
      let int = NoFun (Numeric (Num (IRNum DMInt) NonConst))
          real = NoFun (Numeric (Num (IRNum DMReal) NonConst))
      let test1 :: TC (DMMain,DMMain,DMMain,DMMain)
          test1 = do
            -- the interesting variables
            (a :: DMMain) <- newVar
            (b :: DMMain) <- newVar
            (c :: DMMain) <- newVar
            (d :: DMMain) <- newVar

            (a ≤! c) ()
            (b ≤! c) ()

            (d ≤! a) ()
            (d ≤! b) ()

            -- the additional constraints
            (int ≤! d) ()
            (c ≤! real) ()

            return (d,a,b,c)
      let checkres (d,a,b,c) = (a == c, b == c, a == d, b == d, isGood a)
            where isGood (NoFun (Numeric (Num (IRNum (TVar x)) NonConst))) = True
                  isGood _ = False
      (tc $ (sn test1 >>= (return . checkres))) `shouldReturn` (Right (True,True,True,True,True))

    it "does NOT contract diamond if inner vertices end are bound from outside" $ do
      let int = NoFun (Numeric (Num (IRNum DMInt) NonConst))
          real = NoFun (Numeric (Num (IRNum DMReal) NonConst))
      let test1 :: TC (DMMain,DMMain,DMMain,DMMain)
          test1 = do
            -- the interesting variables
            (a :: DMMain) <- newVar
            (b :: DMMain) <- newVar
            (c :: DMMain) <- newVar
            (d :: DMMain) <- newVar

            (a ≤! c) ()
            (b ≤! c) ()

            (d ≤! a) ()
            (d ≤! b) ()


            -- the additional constraints on `a` and `b`
            x :: DMMain <- newVar
            addConstraintNoMessage (Solvable (IsNonConst (a, x))) 
            addConstraintNoMessage (Solvable (IsNonConst (b, x))) 

            return (d,a,b,c)
      let checkres (d,a,b,c) | let f = [a,b,c,d]
                                   ix = [0,1,2,3]
                               in and [(f !! i /= f !! j) | i <- ix, j <- ix, i /= j] = Right ()
          checkres x = Left x
      (tcl $ (sn test1 >>= (return . checkres))) `shouldReturn` (Right (Right ()))

    it "does NOT contract diamond if any vertices appear in other constraints" $ do
      let int = NoFun (Numeric (Num (IRNum DMInt) NonConst))
          real = NoFun (Numeric (Num (IRNum DMReal) NonConst))
      let test1 :: TC (DMMain,DMMain,DMMain,DMMain)
          test1 = do
            -- the interesting variables
            (a :: DMMain) <- newVar
            (b :: DMMain) <- newVar
            (c :: DMMain) <- newVar
            (d :: DMMain) <- newVar

            (a ≤! c)()
            (b ≤! c)()

            (d ≤! a)()
            (d ≤! b)()

            -- the additional constraint
            addConstraintNoMessage (Solvable (IsJuliaEqual (a, int)))
            addConstraintNoMessage (Solvable (IsJuliaEqual (b, int)))

            return (d,a,b,c)
      let checkres (d,a,b,c) = let f = [a,b,c,d]
                                   ix = [0,1,2,3]
                               in [(f !! i /= f !! j) | i <- ix, j <- ix, i /= j]
      (tc $ (sn test1 >>= (return . checkres))) `shouldReturn` (Right (take 12 $ repeat True))



