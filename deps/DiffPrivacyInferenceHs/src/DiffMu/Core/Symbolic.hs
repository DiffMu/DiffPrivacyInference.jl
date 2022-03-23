{-# LANGUAGE TemplateHaskell #-}

module DiffMu.Core.Symbolic where

import DiffMu.Prelude
-- import DiffMu.Prelude.MonadicAlgebra
import DiffMu.Abstract
import qualified Prelude as P

import Data.Singletons.TH
import Data.HashMap.Strict as H
import DiffMu.Prelude.MonadicAlgebra (Normalize)

data SymVal =
  Infty | Fin Float -- a| Ln (SymTerm t)
  deriving (Generic, Eq)
instance Show SymVal where
  show Infty = "∞"
  show (Fin f) = show f
    -- let a = numerator f
    --     b = denominator f
    -- in if b == 1 then show a
    --              else show @Float (fromRational f)

instance Ord SymVal where
  _ <= Infty = True
  Fin a <= Fin b = a <= b
  Infty <= Fin _ = False

instance Hashable SymVal

instance Monad t => CheckNeutral t SymVal where
  checkNeutral a = return (a == Fin 0)

data SensKind = MainSensKind
  deriving (Eq)

genSingletons [''SensKind]

-- data SymTerm = SymTerm SymVal
--   deriving (Generic, Show)
-- addition
instance Monad t => SemigroupM t (SymVal) where
  (⋆) Infty _            = pure Infty
  (⋆) _ Infty            = pure Infty
  (⋆) (Fin a) (Fin b)    = pure $ Fin (a P.+ b)


instance Monad t => MonoidM t (SymVal) where
  neutral = pure $ Fin 0

instance Monad t => CMonoidM t (SymVal)

-- instance Group SymVal where
--   neg Infty = MinusInfty

-- multiplication
-- special thing: 0 * Infty = 0 (see paper page 38)
instance Monad t => SemiringM t (SymVal) where
  one = pure $ Fin 1
  (⋅) (Fin 0) _          = pure $ (Fin 0)
  (⋅) _ (Fin 0)          = pure $ (Fin 0)
  (⋅) Infty      _       = pure $ Infty
  (⋅)      _  Infty      = pure $ Infty
  (⋅) (Fin a) (Fin b)    = pure $ Fin (a P.* b)

-- instance SingI SensKind where

-- SymTerm are polynomials for describing sensitivities
-- apart from regular variables (HonestVar) they can have
-- non-polynomial expressions inside that we also treat
-- like variables with special rules.
data SymVar (k :: SensKind) =
  HonestVar (SymbolOf k)
  | Ln (SymTerm MainSensKind)
  | Exp (SymTerm MainSensKind, SymTerm MainSensKind)
  | Ceil (SymTerm MainSensKind)
  | Sqrt (SymTerm MainSensKind)
  | Max [SymTerm MainSensKind]
  | Minus (SymTerm MainSensKind, SymTerm MainSensKind)
  | Div (SymTerm MainSensKind)
  | TruncateSym (SymTerm MainSensKind) (SymTerm MainSensKind) -- Truncate a b = [ a ]^b
  | TruncateDoubleSym (SymTerm MainSensKind, SymTerm MainSensKind) (SymTerm MainSensKind) -- Truncate (a0, a1) b = [ a0 , a1 ]^b
  deriving (Generic, Eq)

ln s = injectVarId (Ln s)
exp b e = injectVarId (Exp (b, e))
ceil s = injectVarId (Ceil s)
sqrt s = injectVarId (Sqrt s)
maxS s = injectVarId (Max s)
minus s t = injectVarId (Minus (s, t))
divide s t = s ⋅! injectVarId (Div t)


-- tryComputeSym :: NormalizationType -> SymVar k -> SymVar k
-- tryComputeSym nt x = case f x of
--                     Just val -> undefined --Id val
--                     Nothing -> x

tryComputeSym :: NormalizationType -> SymVar k -> SymVar k
tryComputeSym nt x = x
  -- case f x of
  --                   Just val -> undefined --Id val
  --                   Nothing -> x

normalizationSubstitution :: NormalizationType -> SymVar k -> SymTerm k
normalizationSubstitution nt x = case f x of
                    Just val -> coerce val --Id val
                    Nothing -> injectVarId (coerce x)
  where
    extractVal :: SymTerm MainSensKind -> Maybe SymVal
    extractVal (SingleKinded (LinCom (MonCom h))) =
      let h' = H.toList h
      in case h' of
        []                               -> Just (Fin 0)
        [(exp,coeff)] | exp == neutralId -> Just coeff
        _                                -> Nothing

    dmMinus :: SymVal -> SymVal -> SymVal
    dmMinus Infty Infty     = undefined
    dmMinus Infty b         = undefined
    dmMinus a Infty         = undefined
    dmMinus (Fin a) (Fin b) = Fin (a P.- b)

    dmSqrt :: SymVal -> SymVal
    dmSqrt Infty = Infty
    dmSqrt (Fin a) = Fin (P.sqrt a)

    dmCeil :: SymVal -> SymVal
    dmCeil Infty = Infty
    dmCeil (Fin a) = Fin (P.fromIntegral (P.ceiling a))

    dmExp :: SymVal -> SymVal -> SymVal
    dmExp a Infty = Infty
    dmExp Infty a = Infty
    dmExp (Fin a) (Fin b) = Fin (a P.** b)

    dmLog :: SymVal -> SymVal
    dmLog Infty = Infty
    dmLog (Fin a) = Fin (P.log a)

    dmDiv :: SymVal -> Maybe SymVal
    dmDiv Infty = Nothing
    dmDiv (Fin 1) = Just (Fin 1)
    dmDiv (Fin a) = Just (Fin (1 P./ a))

    f :: SymVar k -> Maybe (SymTerm MainSensKind)
    f (HonestVar _)  = Nothing
    -- f (Id t)         = Nothing
    f (Ln a)         = constCoeff <$> (dmLog <$> extractVal a)
    f (Exp (a,b))    = case extractVal a of
      Just (Fin 1) -> pure (a)
      _            -> constCoeff <$> (dmExp <$> extractVal a <*> extractVal b)
    f (Ceil a)       = constCoeff <$> (dmCeil <$> extractVal a)
    f (Sqrt a)       = constCoeff <$> (dmSqrt <$> extractVal a)
    f (Max [])       = Nothing
    f (Max (a:as))   = case all (== a) as of
        False -> constCoeff <$> (maximum <$> mapM extractVal (a:as))
        True  -> Just a
    f (Minus (a, b)) = case extractVal b of
        (Just (Fin 0))  -> pure a
        _               -> constCoeff <$> (dmMinus <$> extractVal a <*> extractVal b)
    -- NOTE: Without the check for b=0, we get an easier definition, but then it only computes
    --       minus terms where both operands are known. And thus terms like
    --         `a_0 - 0.0`
    --       cannot be solved.
    --
    -- f (Minus (a, b)) = constCoeff <$> (dmMinus <$> extractVal a <*> extractVal b)

    f (Div b) = constCoeff <$> (join (dmDiv <$> extractVal b))
    f (TruncateSym a b) = case nt of
      ExactNormalization -> case extractVal a of
                              (Just (Fin 0)) -> Just (constCoeff (Fin 0))
                              (Just a) -> Just b
                              Nothing -> Nothing
      SimplifyingNormalization -> Just b
    f (TruncateDoubleSym (a0, a1) b) = case nt of
      ExactNormalization -> case (extractVal a0, extractVal a1) of
                              (Just (Fin 0), Just (Fin 0)) -> Just (constCoeff (Fin 0))
                              (Just _, Just _)       -> Just b
                              _                      -> Nothing
      SimplifyingNormalization -> Just b


    -- dmTruncateSym :: SymVal -> SymTerm MainSensKind -> SymVal
    -- dmTruncateSym (Fin 0) b = (Fin 0)

instance Show (SymVar k) where
  show (HonestVar v) = show v
  -- show (Id te) = "id(" <> show te <> ")"
  show (Ln te) = "ln(" <> show te <> ")"
  show (Exp (b, e)) = show b <> "^(" <> show e <> ")"
  show (Ceil te) = "ceil(" <> show te <> ")"
  show (Sqrt te) = "sqrt(" <> show te <> ")"
  show (Max te) = "max(" <> show te <> ")"
  show (Minus (t1, t2)) = "(" <> show t1 <> " - " <> show t2 <> ")"
  show (Div t2) = "(1 / " <> show t2 <> ")"
  show (TruncateSym a b) = "⌉" <> show a <> "⌈" <> "{" <> show b <> "}"
  show (TruncateDoubleSym a b) = "⌉" <> show a <> "⌈" <> "{" <> show b <> "}"

instance Hashable (SymVar k)


instance Show SensKind where
  show MainSensKind = "S"


type SymTerm :: SensKind -> *
type SymTerm = CPolyM SymVal Int (SymVar MainSensKind)

instance CheckContains (SymVar MainSensKind) (SymbolOf MainSensKind) where
  -- checkContains (Id _) = Nothing
  checkContains (Ln _) = Nothing
  checkContains (Exp _) = Nothing
  checkContains (Ceil _) = Nothing
  checkContains (Sqrt _) = Nothing
  checkContains (Max _) = Nothing
  checkContains (Minus _) = Nothing
  checkContains (Div _) = Nothing
  checkContains (HonestVar v) = Just v
  checkContains (TruncateSym _ _) = Nothing
  checkContains (TruncateDoubleSym _ _) = Nothing


-- WARNING: This is not implemented, we should actually check for zero here!
instance Monad m => CheckNeutral m (SymTerm k) where
  checkNeutral a = pure False


svar :: SymbolOf MainSensKind -> (SymTerm MainSensKind)
svar a = injectVarId (HonestVar a)


instance (SemigroupM m a, SemigroupM m b) => SemigroupM m (a,b) where
  (⋆) (a1,a2) (b1,b2) = (,) <$> (a1 ⋆ b1) <*> (a2 ⋆ b2)

instance (MonoidM m a, MonoidM m b) => MonoidM m (a,b) where
  neutral = (,) <$> neutral <*> neutral

instance (CheckNeutral m a, CheckNeutral m b) => CheckNeutral m (a,b) where
  checkNeutral (a,b) = do
    x <- checkNeutral a
    y <- checkNeutral b
    return (and [x,y])



--
-- substitute inside of variables
--
instance (Substitute SymVar (CPolyM SymVal Int (SymVar MainSensKind)) (SymVar k2)) where
  substitute σ (HonestVar v) = pure (HonestVar v)
  -- substitute σ (Id v)        = tryComputeSym ExactNormalization <$> Id <$> substitute σ v
  substitute σ (Ln a)        = tryComputeSym ExactNormalization <$> Ln <$> substitute σ a
  substitute σ (Exp (b,e))   = tryComputeSym ExactNormalization <$> ((\b e -> Exp (b,e)) <$> substitute σ b <*> substitute σ e)
  substitute σ (Ceil a)      = tryComputeSym ExactNormalization <$> Ceil <$> substitute σ a
  substitute σ (Sqrt a)      = tryComputeSym ExactNormalization <$> Sqrt <$> substitute σ a
  substitute σ (Max as)      = tryComputeSym ExactNormalization <$> Max <$> mapM (substitute σ) as
  substitute σ (Minus (a,b)) = tryComputeSym ExactNormalization <$> ((\a b -> Minus (a,b)) <$> substitute σ a <*> substitute σ b)
  substitute σ (Div a)       = tryComputeSym ExactNormalization <$> Div <$> substitute σ a
  substitute σ (TruncateSym a b) =
     tryComputeSym ExactNormalization <$> (TruncateSym <$> substitute σ a <*> substitute σ b)
  substitute σ (TruncateDoubleSym (a0, a1) b) =
     tryComputeSym ExactNormalization <$> ((\a0 a1 b -> TruncateDoubleSym (a0 , a1) b) <$> substitute σ a0 <*> substitute σ a1 <*> substitute σ b)

--
-- We have an extra normalization which creates substitution for larger variables.
--
normalizeSensSpecial :: NormalizationType -> (CPolyM SymVal Int (SymVar MainSensKind) MainSensKind) -> (CPolyM SymVal Int (SymVar MainSensKind) MainSensKind)
normalizeSensSpecial nt s = runIdentity $ substitute (pure . normalizationSubstitution nt) s
-- nt (SingleKinded (LinCom (MonCom m))) = SingleKinded (LinCom (MonCom (f m)))
--   where
--     f :: HashMap (MonCom Int (SymVar 'MainSensKind)) SymVal -> HashMap (MonCom Int (SymVar 'MainSensKind)) SymVal
--     f = H.mapKeys (\(MonCom hmap) -> MonCom $ H.mapKeys (tryComputeSym nt) hmap)



