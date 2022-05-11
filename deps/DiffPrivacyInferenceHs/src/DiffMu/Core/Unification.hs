
{-# LANGUAGE UndecidableInstances #-}

{- |
Description: Unification of `DMType`s.
-}
module DiffMu.Core.Unification where

import DiffMu.Prelude
import DiffMu.Abstract
import DiffMu.Core.Definitions
import DiffMu.Typecheck.Constraint.Definitions
import DiffMu.Core.TC
import DiffMu.Core.Logging

import DiffMu.Core.Symbolic

import Data.HashMap.Strict as H
import Control.Monad.Trans.Except (throwE)

default (Text)

-------------------------------------------------------------------
--

instance ShowPretty (IsLessEqual (Sensitivity, Sensitivity)) where
    showPretty (IsLessEqual (a,b)) = showPretty a <> " ≤ " <> showPretty b
        
(==!) :: (MessageLike t msg, MonadConstraint isT t, Solve isT IsEqual (a,a), (HasNormalize isT a), Show (a), ShowPretty (a), Eq a, Typeable a, IsT isT t, ContentConstraintOnSolvable t (a,a), ConstraintOnSolvable t (IsEqual (a,a))) => a -> a -> msg -> t ()
(==!) a b msg = addConstraint (Solvable (IsEqual (a,b))) msg >> pure ()


class HasUnificationError t e a where
  unificationError' :: (MessageLike t msg, Show a) => Proxy t -> a -> a -> msg -> e t

-------------------------------------------------------------------------------
-- Message wrappers
-------------------------------------------------------------------------------


newtype WrapMessageINC e a = WrapMessageINC a

instance Show a => Show (WrapMessageINC e a) where show (WrapMessageINC a) = show a
instance ShowPretty a => ShowPretty (WrapMessageINC e a) where showPretty (WrapMessageINC a) = showPretty a
instance ShowLocated a => ShowLocated (WrapMessageINC e a) where showLocated (WrapMessageINC a) = showLocated a


instance (MonadInternalError m, MonadLog m, Normalize (INCResT e m) a) => Normalize m (WrapMessageINC e a) where
  normalize e (WrapMessageINC x) = do
    let n :: INCResT e m a
        n = normalize e x
    n' <- runExceptT (runINCResT n)
    case n' of
      Left sr -> case sr of
        Wait' -> return (WrapMessageINC x)
        Fail' e' -> internalError ("While normalizing inside INCRes got a fail")
      Right a -> return (WrapMessageINC a)


newtype WrapMessageINCRev e a = WrapMessageINCRev a

instance Show a => Show (WrapMessageINCRev e a) where show (WrapMessageINCRev a) = show a
instance ShowPretty a => ShowPretty (WrapMessageINCRev e a) where showPretty (WrapMessageINCRev a) = showPretty a
instance ShowLocated a => ShowLocated (WrapMessageINCRev e a) where showLocated (WrapMessageINCRev a) = showLocated a

instance (Show (e (INCResT e m)), MonadInternalError m, MonadLog m, Normalize m a) => Normalize (INCResT e m) (WrapMessageINCRev e a) where
  normalize e (WrapMessageINCRev x) =
    let y = normalize @m e x
    in INCResT (ExceptT (fmap (Right . WrapMessageINCRev) y))



-------------------------------------------------------------------------------
-- INC functionality needed for unification
-------------------------------------------------------------------------------
--
-- | The reason for the implementation using incremental computation is
--   that unification does not always succeed:
--   When terms such as `(v :∧: w)` are unified,  usually we cannot do anything,
--   but have to wait for `v` or `w` to be known in more detail.
--

removeINCResT :: (MonadInternalError t) => INCResT e t a -> t (Maybe a)
removeINCResT n = do
    n' <- runExceptT (runINCResT n)
    case n' of
      Left sr -> case sr of
        Wait' -> pure Nothing
        Fail' e' -> internalError ("While normalizing inside INCRes got a fail")
      Right a -> return (Just a)

liftINC :: Functor m => m a -> INCResT e m a
liftINC a = INCResT (ExceptT (fmap Right a))

data StoppingReason e t = Wait' | Fail' (e t)

newtype INCResT e m a = INCResT {runINCResT :: ExceptT (StoppingReason e (INCResT e m)) m a}
  deriving (Functor, Applicative, Monad, MonadError (StoppingReason e (INCResT e m)))

instance IsNaturalError e => IsNaturalError (StoppingReason e) where
  functionalLift α (Wait') = Wait'
  functionalLift α (Fail' e) = Fail' (functionalLift α e)

instance (MonadInternalError t, MonadDMError e t) => MonadDMError (StoppingReason e) (INCResT e t) where
  isCritical (Wait') = return False
  isCritical (Fail' e) = liftINC $ isCritical (functionalLift removeINCResT e)
  persistentError e = liftINC $ persistentError (functionalLift removeINCResT e)
  catchAndPersist action handler = undefined
  enterNonPersisting = liftINC enterNonPersisting
  exitNonPersisting = liftINC exitNonPersisting

instance (MonadInternalError m, MonadLog m) => MonadLog (INCResT e m) where
  log             = liftINC . log 
  debug           = liftINC . debug
  info            = liftINC . info
  warn            = liftINC . warn
  logForce        = liftINC . logForce
  withLogLocation = \a b -> b


instance MonadDMTC t => HasUnificationError t (WithContext DMException) a where
  unificationError' _ a b name = WithContext (UnificationError a b) (DMPersistentMessage name)

instance MonadDMTC t => HasUnificationError (INCResT (WithContext DMException) t) (StoppingReason (WithContext DMException)) a where
  unificationError' _ a b name = Fail' $ WithContext (UnificationError a b) (DMPersistentMessage name)




-------------------------------------------------------------------------------
-- The actual unification
-------------------------------------------------------------------------------


--------------------
-- generic

normalizeᵢ :: Normalize t a => a -> INCResT e t a
normalizeᵢ a = liftINC (normalizeExact a)

class MonadError (e t) t => Unifyᵢ e t a where
  unifyᵢ_Msg :: MessageLike t msg => msg -> a -> a -> t a

unifyᵢMsg :: (Unifyᵢ (StoppingReason e) (INCResT e t) a, Normalize (t) a, MessageLike (INCResT e t) msg) => msg -> a -> a -> (INCResT e t a)
unifyᵢMsg name a b = (chainM2 (unifyᵢ_Msg name) (normalizeᵢ a) (normalizeᵢ b))

unifyᵢ :: (Unifyᵢ (StoppingReason e) (INCResT e t) a, Normalize (t) a) => a -> a -> (INCResT e t a)
unifyᵢ = unifyᵢMsg ()


--------------------
-- instances

instance (MonadDMTC t) => Unifyᵢ (StoppingReason e) (INCResT e t) Sensitivity where
  unifyᵢ_Msg name a b = liftINC $ unify (WrapMessageINC @e name) a b

instance (Monad t, Unifyᵢ e t a, Unifyᵢ e t b) => Unifyᵢ e t (a,b) where
  unifyᵢ_Msg name (a1,b1) (a2,b2) = (,) <$> (unifyᵢ_Msg name a1 a2) <*> (unifyᵢ_Msg name b1 b2)

instance (Unifyᵢ e isT a, Unifyᵢ e isT b) => Unifyᵢ e isT (a :@ b) where
  unifyᵢ_Msg name (a₁ :@ e₁) (a₂ :@ e₂) = (:@) <$> unifyᵢ_Msg name a₁ a₂ <*> unifyᵢ_Msg name e₁ e₂

instance (HasUnificationError t e [a], MonadLog t, MonadDMError (e) t, Show a, Unifyᵢ e t a) => Unifyᵢ e t [a] where
-- instance (MonadLog t, Show a, Unifyᵢ e t a) => Unifyᵢ e t [a] where
  unifyᵢ_Msg name xs ys | length xs == length ys = mapM (uncurry (unifyᵢ_Msg name)) (zip xs ys)
  unifyᵢ_Msg name xs ys = throwError (unificationError' (Proxy @t) xs ys name)

instance (HasUnificationError t e (Maybe a), MonadLog t, MonadDMError e t, Show a, Unifyᵢ e t a) => Unifyᵢ e t (Maybe a) where
-- instance (MonadLog t, Show a, Unifyᵢ e t a) => Unifyᵢ e t (Maybe a) where
  unifyᵢ_Msg name Nothing Nothing = pure Nothing
  unifyᵢ_Msg name (Just a) (Just b) = Just <$> unifyᵢ_Msg name a b
  unifyᵢ_Msg name t s = throwError (unificationError' (Proxy @t) t s name)


instance (MonadDMTC t, Typeable k) => Unifyᵢ (StoppingReason (WithContext DMException)) (INCResT (WithContext DMException) t) (DMTypeOf k) where
  unifyᵢ_Msg name DMAny DMAny                   = pure DMAny
  unifyᵢ_Msg name DMReal DMReal                 = pure DMReal
  unifyᵢ_Msg name DMBool DMBool                 = pure DMBool
  unifyᵢ_Msg name DMInt DMInt                   = pure DMInt
  unifyᵢ_Msg name DMData DMData                 = pure DMData
  unifyᵢ_Msg name (IRNum t) (IRNum s)           = IRNum <$> unifyᵢMsg name t s
  unifyᵢ_Msg name (Numeric t) (Numeric s)       = Numeric <$> unifyᵢMsg name t s
  unifyᵢ_Msg name (NonConst) (NonConst)         = pure NonConst
  unifyᵢ_Msg name (Const η₁) (Const η₂)         = Const <$> liftINC (unify (WrapMessageINC @(WithContext DMException) name) η₁ η₂)
  unifyᵢ_Msg name (Num a0 c0) (Num a1 c1)       = Num <$> unifyᵢMsg name a0 a1 <*> unifyᵢMsg name c0 c1
  unifyᵢ_Msg name (as :->: a) (bs :->: b)       = (:->:) <$> unifyᵢMsg name as bs <*> unifyᵢMsg name a b
  unifyᵢ_Msg name (as :->*: a) (bs :->*: b)     = (:->*:) <$> unifyᵢMsg name as bs <*> unifyᵢMsg name a b
  unifyᵢ_Msg name (DMTup as) (DMTup bs)         = DMTup <$> unifyᵢMsg name as bs
  unifyᵢ_Msg name (TVar x) (TVar y) | x == y    = pure $ TVar x
  unifyᵢ_Msg name (TVar x) t                    = liftINC (addSub (x := t)) >> pure t
  unifyᵢ_Msg name t (TVar x)                    = liftINC (addSub (x := t)) >> pure t
  unifyᵢ_Msg name L1 L1                         = pure L1
  unifyᵢ_Msg name L2 L2                         = pure L2
  unifyᵢ_Msg name LInf LInf                     = pure LInf
  unifyᵢ_Msg name U U                           = pure U
  unifyᵢ_Msg name Vector Vector                 = pure Vector
  unifyᵢ_Msg name Gradient Gradient             = pure Gradient
  unifyᵢ_Msg name (Matrix r1) (Matrix r2)       = Matrix <$> unifyᵢMsg name r1 r2
  unifyᵢ_Msg name (Clip k) (Clip s)             = Clip <$> unifyᵢMsg name k s
  unifyᵢ_Msg name (DMContainer k1 nrm1 clp1 n1 τ1) (DMContainer k2 nrm2 clp2 n2 τ2) =
      DMContainer <$> unifyᵢMsg name k1 k2 <*> unifyᵢMsg name nrm1 nrm2 <*> unifyᵢMsg name clp1 clp2 <*> unifyᵢMsg name n1 n2 <*> unifyᵢMsg name τ1 τ2
  unifyᵢ_Msg name (DMModel m1) (DMModel m2) =
      DMModel <$> unifyᵢMsg name m1 m2
  unifyᵢ_Msg name (NoFun a) (v :∧: w)              = do
    res0 <- unifyᵢMsg name (NoFun a) v
    res1 <- unifyᵢMsg name res0 w
    return res1
  unifyᵢ_Msg name (v :∧: w) (NoFun b)              = do
    res0 <- unifyᵢMsg name (NoFun b) v
    res1 <- unifyᵢMsg name res0 w
    return res1
  unifyᵢ_Msg name (NoFun x) (NoFun y)              = NoFun <$> unifyᵢMsg name x y
  unifyᵢ_Msg name (Fun xs) (Fun ys)                = Fun <$> unifyᵢMsg name xs ys
  unifyᵢ_Msg name (Fun _) (v :∧: w)                = throwError Wait'
  unifyᵢ_Msg name (v :∧: w) (Fun _)                = throwError Wait'
  unifyᵢ_Msg name (_ :∧: _) (v :∧: w)              = throwError Wait'
  unifyᵢ_Msg name t s                              = do
    let msg2 = case getUnificationFailingHint @(INCResT ((WithContext DMException)) t) ((t,s)) of
                   Just hint -> DMPersistentMessage (hint :\\: name)
                   Nothing -> DMPersistentMessage name
    throwError (Fail' $ WithContext (UnificationError t s) (msg2))


--------------------------------------------
-- Additional failing message if a probably cause of the error is known
--
getUnificationFailingHint :: forall t k. (Typeable k, Monad t) => ((DMTypeOf k, DMTypeOf k)) -> Maybe (DMPersistentMessage t)
getUnificationFailingHint ((a,b))=
  let
      -- case0 = testEquality (typeRep @k) (typeRep @MainKind)
      -- case1 = testEquality (typeRep @k) (typeRep @FunKind)
      -- case2 = testEquality (typeRep @k) (typeRep @NoFunKind)
      -- case3 = testEquality (typeRep @k) (typeRep @NumKind)
      case4 = testEquality (typeRep @k) (typeRep @BaseNumKind)
      -- case5 = testEquality (typeRep @k) (typeRep @ClipKind)
      case6 = testEquality (typeRep @k) (typeRep @NormKind)
      -- case7 = testEquality (typeRep @k) (typeRep @ConstnessKind)
  -- in case (case0,case1,case2,case3,case4,case5,case6,case7) of
  in case case4 of
        Just Refl -> let hasIR (IRNum a) = True
                         hasIR _ = False
                     in case (hasIR a || hasIR b) && (DMData ∈ [a,b]) of
                       True -> Just $ DMPersistentMessage $ "You might want to use one of the following conversion functions:\n" <>
                                                            "`disc :: [Real :@ ∞] -> Data`\n" <>
                                                            "`undisc :: [Data :@ ∞] -> Real`\n" <>
                                                            "`undisc_container :: [MetricMatrix(Data,*) :@ 2] -> MetricMatrix(Real,l)` if your matrix rows" <>
                                                            " all have row `l`-norm `<=1` (use `clip` for this)\n"
                       False -> Nothing
        Nothing -> case case6 of
                    Just Refl -> Just $ DMPersistentMessage $ "You might want to use the `norm_convert` function.\n"
                    Nothing -> Nothing



instance MonadDMError (WithContext DMException) t => Unify (WithContext DMException) t () where
  unify_ _ _ _ = return ()

instance MonadDMTC t => Unify (WithContext DMException) t JuliaType where
  unify_ name a b | a == b = pure a
  unify_ name t s = throwUnlocatedError (UnificationError t s)

instance MonadDMTC t => Unify (StoppingReason (WithContext DMException)) (INCResT (WithContext DMException) t) JuliaType where
  unify_ name a b | a == b = pure a
  unify_ name t s = throwError (Fail' (WithContext (UnificationError t s) (DMPersistentMessage name)))

instance MonadDMTC t => Unifyᵢ (StoppingReason (WithContext DMException)) (INCResT (WithContext DMException) t) JuliaType where
  unifyᵢ_Msg name a b | a == b = pure a
  unifyᵢ_Msg name t s = throwError (Fail' (WithContext (UnificationError t s) (DMPersistentMessage name))) -- throwUnlocatedError (UnificationError t s)


instance MonadDMTC t => Unify (WithContext DMException) t (Annotation e) where
  -- NOTE: we can use the unify_ (with underscore) function here,
  -- because we do not have to normalize the just normalized arguments
  unify_ name (SensitivityAnnotation s) (SensitivityAnnotation t) = SensitivityAnnotation <$> unify_ name s t
  unify_ name (PrivacyAnnotation s) (PrivacyAnnotation t) = PrivacyAnnotation <$> unify_ name s t


instance MonadDMTC t => Unify (WithContext DMException) t (WithRelev e) where
  unify_ name (WithRelev i e) (WithRelev j f)  = WithRelev (i <> j) <$> unify_ name e f

-- Unification of DMTypes (of any kind k) is given by:
instance (Typeable k, MonadDMTC t) => Unify (WithContext DMException) t (DMTypeOf k) where
  unify_ name a b = do
    withLogLocation "Unification" $ debug ("Unifying " <> showPretty a <> " ==! "<> showPretty b)
    res <- runExceptT $ runINCResT $ unifyᵢ_Msg @(StoppingReason (WithContext DMException)) (WrapMessageINCRev @(WithContext DMException) name) a b
    case res of
      Left (Wait')   -> do
        withLogLocation "Unification" $ debug ("Got wait in unify on " <> showPretty a <> " ==! "<> showPretty b)
        liftTC ((a ==! b) (WrapMessageRevId name))
        return a
      Left (Fail' (WithContext err (DMPersistentMessage msg))) -> throwError (WithContext err (DMPersistentMessage (WrapMessageINC @(WithContext DMException) msg)))
      Right a -> return a

-- Above we implictly use unification of terms of the type (a :@ b).
-- These are unified entry-wise:
instance (Unify e isT a, Unify e isT b) => Unify e isT (a :@ b) where
  unify_ name (a₁ :@ e₁) (a₂ :@ e₂) = (:@) <$> unify_ name a₁ a₂ <*> unify_ name e₁ e₂

-- Similarly, lists of terms are unified elements wise,
-- but they only match if they are of the same lenght:
instance (HasUnificationError t e [a], MonadDMError e t, Show a, Unify e t a, MonadLog t) => Unify e t [a] where
  unify_ name xs ys | length xs == length ys = mapM (uncurry (unify_ name)) (zip xs ys)
  unify_ name xs ys = throwError (unificationError' (Proxy @t) xs ys name)

-- Using the unification instance, we implement solving of the `IsEqual` constraint for DMTypes.
instance (Typeable k) => Solve MonadDMTC IsEqual (DMTypeOf k, DMTypeOf k) where
  solve_ Dict _ name (IsEqual (a,b)) = do
    res <- runExceptT $ runINCResT $ unifyᵢ_Msg @(StoppingReason (WithContext DMException)) (name) a b
    case res of
      Left (Wait')   -> return ()
      Left (Fail' (WithContext err (DMPersistentMessage msg))) -> throwError (WithContext err (DMPersistentMessage (WrapMessageINC @(WithContext DMException) msg)))
      Right a -> dischargeConstraint name


instance Solve MonadDMTC IsLessEqual (Sensitivity, Sensitivity) where
  solve_ Dict _ name (IsLessEqual (s1, s2)) = solveLessEqualSensitivity s1 s2
    where
      getVal :: Sensitivity -> Maybe SymVal
      getVal a@(SingleKinded (LinCom (MonCom as))) = case H.toList as of
         [(MonCom aterm, av)] -> case H.toList aterm of
                                      [] -> (Just av)
                                      _ -> Nothing
         [] -> (Just zeroId)
         _ -> Nothing
      solveLessEqualSensitivity :: IsT MonadDMTC t => Sensitivity -> Sensitivity -> t ()
      solveLessEqualSensitivity a b | a == b = dischargeConstraint name
      solveLessEqualSensitivity a b = case getVal a of
         Just av -> case getVal b of
                         Just bv -> case av == Infty of
                                         True -> (b ==! constCoeff Infty) (name) >> dischargeConstraint name
                                         False -> case (av <= bv) of
                                                       True -> dischargeConstraint name
                                                       False -> failConstraint name
                         Nothing -> return ()
         Nothing -> return ()

-------------------------------------------------------------------
-- Monadic monoid structure on dmtypes
--

-- monoid structure using infimum

instance (IsT MonadDMTC t) => SemigroupM (t) (DMTypeOf MainKind) where
  (⋆) x y = return (x :∧: y)

instance (IsT MonadDMTC t) => MonoidM (t) (DMTypeOf MainKind) where
  neutral = newVar

-- An optimized check for whether a given DMType is a neutral does not create new typevariables,
-- but simply checks if the given DMType is one.
instance (SingI k, Typeable k, IsT MonadDMTC t) => (CheckNeutral (t) (DMTypeOf k)) where
  checkNeutral (TVar x) = return True
  checkNeutral (_) = return False

