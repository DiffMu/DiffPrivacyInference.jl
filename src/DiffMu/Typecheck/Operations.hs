
{- |
Description: Code for handling arithmetic operations, i.e. determining their sensitivity w.r.t.
             whether the involved types are const or non-const numbers or matrices.
-}
module DiffMu.Typecheck.Operations where

import DiffMu.Prelude
import DiffMu.Abstract
import DiffMu.Abstract.Data.Error
import DiffMu.Core.Definitions
import DiffMu.Core.Logging
import DiffMu.Core.TC
import DiffMu.Core.Symbolic
import DiffMu.Core.Unification
import DiffMu.Typecheck.Subtyping
import DiffMu.Typecheck.Constraint.Definitions
import DiffMu.Typecheck.Constraint.CheapConstraints

import Debug.Trace



-- Given a kind of a type op (`DMTypeOp_Some`), and a number of given arguments,
-- we create an `IsTypeOpResult` constraint, and return the contained types/sensitivities.
-- the constraint constains sensitivities that are scalars for the operand contexts and will
-- be determined once enough about the operand types is known.
makeTypeOp :: (IsT MonadDMTC t) => DMTypeOp_Some -> Int -> DMPersistentMessage t -> t ((DMType) , [(DMType,SVar)])
makeTypeOp (IsUnary op) 1 msg =
  do s1 <- newSVar "s"
     τ1 <-  TVar <$> newTVar "τ"
     res <- TVar <$> newTVar "τ"
     addConstraint (Solvable (IsTypeOpResult (Unary op (τ1 :@ s1) res))) msg
     return (res , [(τ1, s1)])
makeTypeOp (IsBinary op) 2 msg =
  do s1 <- newSVar "s"
     s2 <- newSVar "s"
     τ1 <-  TVar <$> newTVar "τ"
     τ2 <-  TVar <$> newTVar "τ"
     res <- TVar <$> newTVar "τ"
     addConstraint (Solvable (IsTypeOpResult (Binary op (τ1:@s1, τ2:@s2) res))) msg
     return (res , [(τ1,s1),(τ2,s2)])
makeTypeOp op lengthArgs msg = throwUnlocatedError (WrongNumberOfArgsOp op (lengthArgs))

-- We can solve a unary typeop constraint.
solveUnary :: forall t e. IsT MonadDMTC t => DMTypeOps_Unary -> DMType -> t (Maybe (Sensitivity, DMType))
solveUnary op τ = traceM ("solving ceil " <> show τ) >> f op τ
  where
    ret :: Sensitivity -> t (DMType) -> t (Maybe (Sensitivity, DMType))
    ret s τ = do
      τ' <- τ
      return (Just (s, τ'))

    f :: DMTypeOps_Unary -> DMType -> t (Maybe (Sensitivity, DMType))
    f DMOpCeil (Numeric (Num (IRNum DMInt) (Const s1))) = ret zeroId (return (Numeric (Num (IRNum DMInt) (Const s1))))
    f DMOpCeil (Numeric (Num (IRNum DMReal) (Const s1))) = ret zeroId (return (Numeric (Num (IRNum DMInt) (Const (ceil s1)))))
    f DMOpCeil (Numeric (Num t2 NonConst)) = ret oneId (return (Numeric (Num (IRNum DMInt) NonConst)))
    f DMOpCeil _             = return Nothing




-- We can solve a binary typeop constraint.
solveBinary :: forall t. IsT MonadDMTC t => IxSymbol -> DMTypeOps_Binary -> (DMType, DMType) -> t (Maybe (Sensitivity , Sensitivity, DMType))
solveBinary name op (τ1, τ2) = f op τ1 τ2
  where
    ret :: Sensitivity -> Sensitivity -> t (DMType) -> t (Maybe (Sensitivity, Sensitivity, DMType))
    ret s1 s2 τ = do
      τ' <- τ
      return (Just (s1, s2, τ'))


    makeNoFunNumeric :: forall t. IsT MonadDMTC t =>  DMMain -> t (DMTypeOf NumKind)
    makeNoFunNumeric t = case t of
        NoFun (Numeric v) -> return v
        _ -> do
              v <- newVar
              unifyFromName name t (NoFun (Numeric v))
              return v
      
    matchType :: SymbolOf NoFunKind -> DMType -> t (Maybe (Sensitivity, Sensitivity, DMType))
    matchType a m = case m of
        (Numeric (Num (IRNum _) _)) -> do
           tv <- newVar
           cv <- newVar
           unifyFromName name (TVar a) (Numeric (Num (IRNum tv) cv))
           return Nothing
        (Numeric (Num DMData _)) -> do
           cv <- newVar
           unifyFromName name (TVar a) (Numeric (Num DMData cv))
           return Nothing
        (Numeric _) -> do
           v <- newVar
           unifyFromName name (TVar a) (Numeric v)
           return Nothing
        (DMVec n cl r t) -> do
           makeNoFunNumeric t
           clv <- newVar
           τ <- newVar
           unifyFromName name (TVar a) (DMVec n clv r τ)
           return Nothing
        (DMMat n cl r c t) -> do
           makeNoFunNumeric t
           clv <- newVar
           τ <- newVar
           unifyFromName name (TVar a) (DMMat n clv r c τ)
           return Nothing
        _ -> return Nothing

    applyOp op (k1, n1, c1, t1) (k2, n2, c2, t2) = do
           unifyFromName name k1 k2
           unifyFromName name n1 n2
           unifyFromName name c1 c2
           tt1 <- makeNoFunNumeric t1
           tt2 <- makeNoFunNumeric t2
           s <- solveBinary name op (Numeric tt1, Numeric tt2)
           case s of
              Nothing -> return Nothing
              Just (s1, s2, τ) -> return (Just (s1, s2, (DMContainer k1 n1 U c1 (NoFun τ))))

    numSup t1 t2 = supremumFromName name t1 t2
              
        
    -- all possible type signatures for arithmetic operations, and the resulting sensitivities and result types
    f :: DMTypeOps_Binary -> (DMType) -> (DMType) -> t (Maybe (Sensitivity , Sensitivity, DMType))
    f DMOpAdd (Numeric (Num t1 (Const s1))) (Numeric (Num t2 (Const s2))) = ret zeroId zeroId ((Numeric <$> (Num <$> (numSup t1 t2) <*> (Const <$> (s1 ⋆ s2)))))
    f DMOpAdd (Numeric (Num t1 (Const s1))) (Numeric (Num t2 NonConst)) = ret zeroId oneId  (Numeric <$> (Num <$> numSup t1 t2 <*> pure NonConst))
    f DMOpAdd (Numeric (Num t1 NonConst)) (Numeric (Num t2 (Const s2))) = ret oneId  zeroId (Numeric <$> (Num <$> numSup t1 t2 <*> pure NonConst))
    f DMOpAdd (Numeric (Num t1 NonConst)) (Numeric (Num t2 NonConst)) = ret oneId  oneId  (Numeric <$> (Num <$> numSup t1 t2 <*> pure NonConst))
    f DMOpAdd (DMContainer k1 n1 cl1 c1 t1) (DMContainer k2 n2 cl2 c2 t2) = applyOp DMOpAdd (k1, n1, c1, t1) (k2, n2, c2, t2)
    f DMOpAdd t (TVar a)                            = matchType a t
    f DMOpAdd (TVar a) t                            = matchType a t


    -- always return non-const so we can't get negative const
    f DMOpSub (Numeric (Num t1 (Const s1))) (Numeric (Num t2 (Const s2))) = ret zeroId zeroId (Numeric <$> (Num <$> (numSup t1 t2) <*> pure NonConst))
    f DMOpSub (Numeric (Num t1 (Const s1))) (Numeric (Num t2 NonConst)) = ret zeroId oneId (Numeric <$> (Num <$> numSup t1 t2 <*> pure NonConst))
    f DMOpSub (Numeric (Num t1 NonConst)) (Numeric (Num t2 (Const s2))) = ret oneId zeroId (Numeric <$> (Num <$> numSup t1 t2 <*> pure NonConst))
    f DMOpSub (Numeric (Num t1 NonConst)) (Numeric (Num t2 NonConst)) = ret oneId oneId (Numeric <$> (Num <$> numSup t1 t2 <*> pure NonConst))
    f DMOpSub (DMContainer k1 n1 cl1 c1 t1) (DMContainer k2 n2 cl2 c2 t2) = applyOp DMOpSub (k1, n1, c1, t1) (k2, n2, c2, t2)
    f DMOpSub t (TVar a)                            = matchType a t
    f DMOpSub (TVar a) t                            = matchType a t



    f DMOpMul (Numeric (Num t1 (Const s1))) (Numeric (Num t2 (Const s2))) = ret zeroId zeroId ((Numeric <$> (Num <$> (numSup t1 t2) <*> (Const <$> (s1 ⋅ s2)))))
    f DMOpMul (Numeric (Num t1 (Const s1))) (Numeric (Num t2 NonConst))   = ret zeroId s1 (Numeric <$> (Num <$> numSup t1 t2 <*> pure NonConst))
    f DMOpMul (Numeric (Num t1 NonConst)) (Numeric (Num t2 (Const s2)))   = ret s2 zeroId (Numeric <$> (Num <$> numSup t1 t2 <*> pure NonConst))
    f DMOpMul (Numeric (Num (IRNum t1) NonConst)) (Numeric (Num (IRNum t2) NonConst)) = ret inftyS inftyS (Numeric <$> (Num <$> (numSup (IRNum t1) (IRNum t2)) <*> pure NonConst))
    f DMOpMul (Numeric (Num DMData NonConst)) (Numeric (Num DMData NonConst))         = ret oneId oneId (return (Numeric (Num DMData NonConst)))

    f DMOpMul (Numeric τs) (DMMat n cl r c t) = do
                                                  tt <- makeNoFunNumeric t
                                                  s <- solveBinary name op (Numeric τs, Numeric tt)
                                                  case s of
                                                     Nothing -> return Nothing
                                                     Just (s1, s2, τ) -> return (Just (r ⋅! c ⋅! s1, s2, (DMMat n U r c (NoFun τ))))
    f DMOpMul (Numeric τs) (DMVec n cl r t)   = do
                                                  tt <- makeNoFunNumeric t
                                                  s <- solveBinary name op (Numeric τs, Numeric tt)
                                                  case s of
                                                     Nothing -> return Nothing
                                                     Just (s1, s2, τ) -> return (Just (r ⋅! s1, s2, (DMVec n U r (NoFun τ))))



    -- TODO notZero constraints for divisor?
    f DMOpDiv (Numeric (Num (IRNum _) (Const s1))) (Numeric (Num (IRNum _) (Const s2))) = ret zeroId zeroId (return (Numeric (Num (IRNum DMReal) (Const (divide s1 s2)))))
    f DMOpDiv (Numeric (Num (IRNum _) (Const s1))) (Numeric (Num (IRNum _) NonConst))   = ret zeroId (constCoeff Infty) (return (Numeric (Num (IRNum DMReal) NonConst)))
    f DMOpDiv (Numeric (Num (IRNum _) NonConst))   (Numeric (Num (IRNum _) (Const s2))) = ret (divide oneId s2) zeroId (return (Numeric (Num (IRNum DMReal) NonConst)))
    f DMOpDiv (Numeric (Num (IRNum _) NonConst))   (Numeric (Num (IRNum _) NonConst))   = ret inftyS inftyS (return (Numeric (Num (IRNum DMReal) NonConst)))
    f DMOpDiv (Numeric (Num DMData (Const s1))) (Numeric (Num DMData (Const s2))) = ret zeroId zeroId (return (Numeric (Num DMData (Const (divide s1 s2)))))
    f DMOpDiv (Numeric (Num DMData (Const s1))) (Numeric (Num DMData NonConst))   = ret zeroId oneId (return (Numeric (Num DMData NonConst)))
    f DMOpDiv (Numeric (Num DMData NonConst))   (Numeric (Num DMData (Const s2))) = ret (divide oneId s2) zeroId (return (Numeric (Num DMData NonConst)))
    f DMOpDiv (Numeric (Num DMData NonConst))   (Numeric (Num DMData NonConst))   = ret oneId oneId (return (Numeric (Num DMData NonConst)))
    f DMOpDiv (Numeric t) (TVar a)                            = matchType a (Numeric t)
    f DMOpDiv (TVar a) (Numeric t)                            = matchType a (Numeric t)



    f DMOpMod (Numeric (Num t1 NonConst)) (Numeric (Num t2 (Const s2))) = ret s2 zeroId (Numeric <$> (Num <$> numSup t1 t2 <*> pure NonConst))
    f DMOpMod (Numeric (Num t1 NonConst)) (Numeric (Num t2 NonConst))   = ret (constCoeff Infty) (constCoeff Infty) (Numeric <$> (Num <$> numSup t1 t2 <*> pure NonConst))
    f DMOpMod (Numeric t) (TVar a)                            = matchType a (Numeric t)
    f DMOpMod (TVar a) (Numeric t)                            = matchType a (Numeric t)



    -- order matters here, Real is special!
    f DMOpEq (Numeric (Num t1 (Const s1))) (Numeric (Num (IRNum DMReal) NonConst)) = ret zeroId inftyS (pure $ DMBool)
    f DMOpEq (Numeric (Num (IRNum DMReal) NonConst)) (Numeric (Num t2 (Const s2))) = ret inftyS zeroId (pure $ DMBool)
    f DMOpEq (Numeric (Num (IRNum DMReal) NonConst)) (Numeric (Num (IRNum DMReal) NonConst)) = ret inftyS inftyS (pure $ DMBool)
    f DMOpEq (Numeric (Num _ (Const _))) (Numeric (Num _ (Const _))) = ret zeroId zeroId (pure $ DMBool)
    f DMOpEq (Numeric (Num _ (Const _))) (Numeric (Num _ NonConst))  = ret zeroId oneId  (pure $ DMBool)
    f DMOpEq (Numeric (Num _ NonConst)) (Numeric (Num _ (Const _)))  = ret oneId  zeroId (pure $ DMBool)
    f DMOpEq (Numeric (Num _ NonConst)) (Numeric (Num _ NonConst))   = ret oneId  oneId  (pure $ DMBool)
    f DMOpEq (DMContainer k1 n1 cl1 c1 (NoFun t1)) (DMContainer k2 n2 cl2 c2 (NoFun t2)) = solveBinary name DMOpEq (t1, t2)

    f _ _ _                            = return Nothing


----------------------------------------
-- Solving unary constraints (exactly)
solveop :: (IsT MonadDMTC t) => IxSymbol -> IsTypeOpResult DMTypeOp -> t ()
solveop name (IsTypeOpResult (Unary op (τa :@ s) τr)) = do
  solveres <- solveUnary op τa
  case solveres of
    Nothing -> return ()
    Just (val_s, val_τr) -> do
      addSub (s := val_s)

      -- if the return type already is non-const, that's bc we non-constified some types
      -- earlier to perssimistically resolve constraints we could not have otherwise.
      -- unification would lead to an error then so we do subtyping in that case
      -- see issue #124
      case τr of
          (Numeric (Num _ NonConst)) -> addConstraintFromName name (Solvable (IsLessEqual (val_τr ,τr))) >> return val_τr
          _ -> unifyFromName name τr val_τr
      dischargeConstraint @MonadDMTC name

----------------------------------------
-- Solving binary constraints (exactly)
-- if we know the result type is a number all operands need to be numbers as well.
solveop name (IsTypeOpResult (Binary op ((TVar τa1) :@ _, _) (Numeric τr))) = do
    t1 <- newVar
    unifyFromName name (TVar τa1) (Numeric t1)
    return ()
solveop name (IsTypeOpResult (Binary op (_, (TVar τa2) :@ _) (Numeric τr))) = do
    t2 <- newVar
    unifyFromName name (TVar τa2) (Numeric t2)
    return ()
solveop name (IsTypeOpResult (Binary op (τa1 :@ s1 , τa2 :@ s2) τr)) = do
  solveres <- solveBinary name op (τa1, τa2)
  case solveres of
    Nothing -> return ()
    Just (val_s1, val_s2, val_τr) -> do
      -- NOTE: We do have to do unification here, instead of creating substitutions
      --       (which we theoretically could, since the LHS is a svar), because
      --       it might be that the variables on the LHS already have been substituted
      --       with something elsewhere. Thus we would have two subs for the same var
      --       in the sub context.
      unifyFromName name (svar s1) val_s1
      unifyFromName name (svar s2) val_s2

      -- if the return type already is non-const, that's bc we non-constified some types
      -- earlier to perssimistically resolve constraints we could not have otherwise.
      -- unification would lead to an error if we inferred a const return type do we unify
      -- the number types instead
      -- see issue #124
      case (τr, val_τr) of
          (Numeric (Num tr NonConst), Numeric (Num tr_val (Const _))) -> unifyFromName name tr tr_val >> return τr
          _ -> unifyFromName name τr val_τr
      dischargeConstraint @MonadDMTC name

-- An instance which says that the `IsTypeOpResult DMTypeOp` constraint is solvable
-- in the `MonadDMTC` class of monads.
instance Solve MonadDMTC (IsTypeOpResult) DMTypeOp where

  -- If we are solving exact, then we simply call `solveop`
  solve_ Dict SolveExact name constr = solveop name constr

  -- If we are "losing generality" / "assuming worst case", then we make all operands in the op into `NonConst`s.
  solve_ Dict SolveAssumeWorst name (IsTypeOpResult op) = return () -- makeNonConstTypeOp name op >> return ()
  solve_ Dict _ name (IsTypeOpResult op)                = return ()



opAdd x y = Op (IsBinary DMOpAdd) [x,y]
opSub x y = Op (IsBinary DMOpSub) [x,y]
opMul x y = Op (IsBinary DMOpMul) [x,y]
opCeil x = Op (IsUnary DMOpCeil) [x]
opDiv x y = Op (IsBinary DMOpDiv) [x,y]

