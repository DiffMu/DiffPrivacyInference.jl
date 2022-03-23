
{-# LANGUAGE UndecidableInstances #-}

module DiffMu.Core.Context where

import DiffMu.Prelude
import DiffMu.Abstract
import DiffMu.Core.Logging
import DiffMu.Core.Definitions
import DiffMu.Core.TC
import DiffMu.Core.Unification
import DiffMu.Core.Symbolic

import qualified Data.HashMap.Strict as H

import Debug.Trace

default (Text)

-------------------------------------------------------------------
-- Operations on contexts / On the current context in the monad.
--

-- A helper function which scale any type context with a given sensitivity `η`.
scale :: Sensitivity -> TypeCtxSP -> TypeCtxSP
scale η (Left γ) = Left (f <$> γ)
  where f (WithRelev i (τ :@ SensitivityAnnotation x)) = WithRelev i (τ :@ SensitivityAnnotation (η ⋅! x))
scale η (Right γ) = Right (f <$> γ)
  where f (WithRelev i (τ :@ PrivacyAnnotation (ε,δ))) = WithRelev i (τ :@ PrivacyAnnotation (η ⋅! ε, η ⋅! δ))

-- Scales the current type context living in our typechecking-state monad by a given `η`.
mscale :: MonadDMTC t => Sensitivity -> t ()
mscale η = types %= scale η

-- A helper function which sets all annotations in any type context to infinity.
setInf :: TypeCtxSP -> TypeCtxSP
setInf (Left γ) = Left (f <$> γ)
  where f :: WithRelev SensitivityK -> WithRelev SensitivityK
        f (WithRelev i (τ :@ SensitivityAnnotation _)) = WithRelev i (τ :@ SensitivityAnnotation inftyS)
setInf (Right γ) = Right (f <$> γ)
  where f :: WithRelev PrivacyK -> WithRelev PrivacyK
        f (WithRelev i (τ :@ PrivacyAnnotation _)) = WithRelev i (τ :@ PrivacyAnnotation inftyP)

-- sets all ennotations in the current context to infinity.
msetInf :: MonadDMTC t => t ()
msetInf = types %= setInf


zeroWithRelevation :: (MonadDMTC t, Default e) => t e
zeroWithRelevation = return def

instance Default Sensitivity where
  def = constCoeff (Fin 0)

instance Default Privacy where
  def = (def,def)


instance (CMonoidM t a, CMonoidM t b) => CMonoidM t (a,b)

-- truncate_impl :: forall f e. (CMonoidM Identity f, CMonoidM Identity e, Eq e) => f -> TypeCtx e -> TypeCtx f
truncate_impl :: forall f e. (DMExtra e, DMExtra f) => Annotation f -> TypeCtx e -> TypeCtx f
truncate_impl η γ = truncate_annotation <$> γ
   where
      --truncate_annotation :: (WithRelev e) -> (WithRelev f)
      --truncate_annotation (WithRelev i (τ :@ _)) = WithRelev i (τ :@ η)
       truncate_annotation (WithRelev i (τ :@ annotation)) =
         (case annotation == zeroId of
             True -> WithRelev i (τ :@ zeroId)
             _    -> WithRelev i (τ :@ η))

truncate_SS :: Sensitivity -> TypeCtx SensitivityK -> TypeCtx SensitivityK
truncate_SS eta gamma = f <$> gamma 
  where
    f (WithRelev i (tau :@ (SensitivityAnnotation ann))) =
       WithRelev i (tau :@ (SensitivityAnnotation (injectVarId $ TruncateSym ann eta)))

truncate_PS :: Sensitivity -> TypeCtx PrivacyK -> TypeCtx SensitivityK
truncate_PS eta gamma = f <$> gamma 
  where
    f (WithRelev i (tau :@ (PrivacyAnnotation p))) =
       WithRelev i (tau :@ (SensitivityAnnotation (injectVarId $ TruncateDoubleSym p eta)))

truncate_SP :: Privacy -> TypeCtx SensitivityK -> TypeCtx PrivacyK
truncate_SP (eps,del) gamma = f <$> gamma
  where
    f (WithRelev i (tau :@ (SensitivityAnnotation ann))) =
       WithRelev i (tau :@ (PrivacyAnnotation (injectVarId $ TruncateSym ann eps, injectVarId $ TruncateSym ann del)))

truncate_PP :: Privacy -> TypeCtx PrivacyK -> TypeCtx PrivacyK
truncate_PP (pnew0, pnew1) gamma = f <$> gamma 
  where
    f (WithRelev i (tau :@ (PrivacyAnnotation (pold)))) =
       WithRelev i (tau :@ (PrivacyAnnotation (injectVarId $ TruncateDoubleSym pold pnew0, injectVarId $ TruncateDoubleSym pold pnew1)))

truncateS :: Sensitivity -> TypeCtxSP -> TypeCtxSP
truncateS η (Left γ) = Left (truncate_SS η γ)
truncateS η (Right γ) = Left (truncate_PS η γ)
-- truncateS η (Left γ) = Left (truncate_impl (SensitivityAnnotation η) γ)
-- truncateS η (Right γ) = Left (truncate_impl (SensitivityAnnotation η) γ)

truncateP :: Privacy -> TypeCtxSP -> TypeCtxSP
truncateP η (Left γ) = Right (truncate_SP η γ)
truncateP η (Right γ) = Right (truncate_PP η γ)
-- truncateP η (Left γ) = Right (truncate_impl (PrivacyAnnotation η) γ)
-- truncateP η (Right γ) = Right (truncate_impl (PrivacyAnnotation η) γ)

-- Truncates the current type context living in our typechecking-state monad by a given Sensitivity `η`.
mtruncateS :: MonadDMTC t => Sensitivity -> t ()
mtruncateS η = types %= truncateS η

-- Truncates the current type context living in our typechecking-state monad by a given Privacy `η`.
mtruncateP :: MonadDMTC t => Privacy -> t ()
mtruncateP η = types %= truncateP η

instance (MonadLog t, MonadError (LocatedDMException t) t, SemigroupM t a, SemigroupM t b, Show a, Show b) => SemigroupM t (Either a b) where
  (⋆) (Left a) (Left b) = Left <$> (a ⋆ b)
  (⋆) (Right a) (Right b) = Right <$> (a ⋆ b)
  (⋆) ea eb =  throwUnlocatedError (ImpossibleError ("Could not match left and right. (Probably a sensitivity / privacy context mismatch between " <> show ea <> " and " <> show eb))
--  (⋆) _ _ = internalError "Could not match left and right. (Probably a sensitivity / privacy context mismatch.)"
-- instance (MonoidM t a, MonoidM t b) => MonoidM t (Either a b) where

resetToDefault :: (Default a, Default b) => Either a b -> Either a b
resetToDefault (Left a) = Left def
resetToDefault (Right b) = Right def

-- Given a list of computations in a MonadDMTC monad, it executes all computations
-- on the same input type context, and sums the resulting type contexts.
-- All additional data (constraints, substitutions, metavariable contexts) are passed sequentially.
msum :: (IsT MonadDMTC t) => TypeCtxSP -> [t a] -> t [a]
-- msum :: (Show e, IsT MonadDMTC t, MonoidM (t) e, CheckNeutral (t) e) => [t a] -> t [a]
-- msum :: [t a] -> t [a]
msum emptyΣ ms = do
  initΣ <- use types
  f initΣ ms (emptyΣ)

    where
      -- f :: (Show e, IsT MonadDMTC t, MonoidM (t) e, CheckNeutral (t) e) => TypeCtxSP -> [t a] -> TypeCtxSP -> t [a]
      f :: (IsT MonadDMTC t) => TypeCtxSP -> [t a] -> TypeCtxSP -> t [a]
      f initΣ [] accΣ = types .= accΣ >> return []
      f initΣ (m:ms) accΣ = do
        types .= initΣ
        a <- m
        mΣ <- use types
        m_acc_Σ <- mΣ ⋆ accΣ
        as <- f initΣ ms (m_acc_Σ)
        return (a : as)

msumP = msum (Right def)
msumS = msum (Left def)

msumTup :: (IsT MonadDMTC t) => (t a, t b) -> t (a,b)
msumTup (ma, mb) = do
  tΣ <- use types
  types .= tΣ
  a <- ma
  aΣ <- use types

  types .= tΣ
  b <- mb
  bΣ <- use types

  resΣ <- (aΣ ⋆ bΣ)
  types .= resΣ

  return (a , b)


msum3Tup :: (IsT MonadDMTC t) => (t a, t b, t c) -> t (a,b,c)
msum3Tup (ma, mb, mc) = do
  tΣ <- use types
  types .= tΣ
  a <- ma
  aΣ <- use types

  types .= tΣ
  b <- mb
  bΣ <- use types

  types .= tΣ
  c <- mc
  cΣ <- use types

  m_acc_Σ <- (aΣ ⋆ bΣ)
  resΣ <- (m_acc_Σ ⋆ cΣ)
  types .= resΣ

  return (a, b, c)


msum4Tup :: (IsT MonadDMTC t) => (t a, t b, t c, t d) -> t (a,b,c,d)
msum4Tup (ma, mb, mc, md) = do
  tΣ <- use types
  types .= tΣ
  a <- ma
  aΣ <- use types

  types .= tΣ
  b <- mb
  bΣ <- use types

  types .= tΣ
  c <- mc
  cΣ <- use types

  types .= tΣ
  d <- md
  dΣ <- use types

  m_acc_Σ <- (aΣ ⋆ bΣ)
  m_acc_Σ' <- (m_acc_Σ ⋆ cΣ)
  resΣ <- (m_acc_Σ' ⋆ dΣ)
  types .= resΣ

  return (a, b, c, d)



setVarS :: MonadDMTC t => TeVar -> WithRelev SensitivityK -> t ()
setVarS k v = types %=~ setValueM k (Left v :: Either (WithRelev SensitivityK) (WithRelev PrivacyK))

setVarP :: MonadDMTC t => TeVar -> WithRelev PrivacyK -> t ()
setVarP k v = types %=~ setValueM k (Right v :: Either (WithRelev SensitivityK) (WithRelev PrivacyK))





-- add constraints that make sure all current context entries have sensitivity <= s.
restrictAll :: MessageLike TC msg => Sensitivity -> msg -> TC ()
restrictAll s msg = let
   addC :: Sensitivity -> TC ()
   addC sv = do
      -- make constraints that say sv <= s and sv is the sensitivity of τ
      addConstraint (Solvable (IsLessEqual (sv, s))) msg
      return ()
   in do
      γ <- use types
      case γ of
         Right _ -> throwUnlocatedError (ImpossibleError "restrictAll called on privacy context.")
         Left (Ctx (MonCom h)) -> mapM (\(WithRelev _ (_ :@ SensitivityAnnotation sv)) -> addC sv) h -- restrict sensitivities of all γ entries
      return ()

-- add constraints that make sure all interesting context entries have sensitivity <= s.
restrictInteresting :: MessageLike TC msg => Sensitivity -> msg -> TC ()
restrictInteresting s msg = let
   addC :: (TeVar, WithRelev SensitivityK) -> TC ()
   addC (v, WithRelev rel (_ :@ SensitivityAnnotation sv)) = do
      case rel of
         IsRelevant -> do
            -- make constraints that say sv <= s and sv is the sensitivity of τ
            addConstraint (Solvable (IsLessEqual (sv, s))) ("Restricting the variable: " :<>: v :\\: msg)
            return ()
         _ -> return ()
   in do
      γ <- use types
      case γ of
         Right _ -> throwUnlocatedError (ImpossibleError "restrictAll called on privacy context.")
         Left (Ctx (MonCom h)) -> mapM addC (H.toList h) -- restrict sensitivities of all γ entries
      return ()

-- Look up the types and sensitivities/privacies of the variables in `xτs` from the current context.
-- If a variable is not present in Σ (this means it was not used in the lambda body),
-- create a new type/typevar according to type hint given in `xτs` and give it zero annotation.
-- The result is the signature of the lambda the checking of whose body returned the current context.
getArgList :: forall t e. (MonadDMTC t, DMExtra e) => [Asgmt JuliaType] -> t [DMTypeOf MainKind :@ Annotation e]
getArgList xτs = do
  (γ :: TypeCtxSP) <- use types

  let f :: Asgmt JuliaType -> t (DMTypeOf MainKind :@ Annotation e)
      f (x :- τ) = do
            val <- getValueM x γ
            case val of
              -- If the symbol was in the context γ, then we get its type and sensitivity
              Just τr -> do
                (WithRelev _ τx) <- cast τr
                return τx
              -- else just return a variable with 0 annotation, as this means it was not used in the body.
              Nothing -> do
                τv <- newVar
                return (τv :@ zeroId) -- scale with 0

  xτs' <- mapM f xτs

  let xsWithName = [x | (x :- _) <- xτs]
  -- We have to remove all symbols x from the context
  let deleteWithRelev :: [TypeCtxSP -> t (TypeCtxSP)]
      deleteWithRelev = ((\(x) -> deleteValueM x) <$> xsWithName)
  γ' <- composeFunM deleteWithRelev γ

  types .= γ'

  return xτs'

getAllVars = do
  (γ :: TypeCtxSP) <- use types
  h <- case γ of
           Right _ -> throwUnlocatedError (ImpossibleError "getAllVars called on privacy context.")
           Left (Ctx (MonCom h')) -> return (H.toList h')
  return h

removeVarMaybe :: forall e t. (DMExtra e, MonadDMTC t) => Maybe TeVar -> t (WithRelev e)
removeVarMaybe Nothing = do
    v <- newVar
    return (WithRelev NotRelevant (v :@ zeroId))
removeVarMaybe (Just a) = removeVar a

removeVar :: forall e t. (DMExtra e, MonadDMTC t) => TeVar -> t (WithRelev e)
removeVar x =  do
  -- (γ :: Ctx Symbol (DMType :@ e)) <- use types
  γ <- use types
  v <- getValueM x γ
  vr <- case v of
     Just vv -> cast vv
     Nothing -> WithRelev IsRelevant <$> ((:@ zeroId) <$> newVar) -- ((:@) <$> newVar <*> return zeroId)
  γ' <- deleteValueM x γ
  types .= γ'
  return vr

lookupVar :: forall e t. (DMExtra e, MonadDMTC t) => TeVar -> t (Maybe (WithRelev e))
lookupVar x =  do
  γ <- use types
  v <- getValueM x γ
  cast v

getInteresting :: MonadDMTC t => t ([TeVar],[DMTypeOf MainKind :@ (Annotation PrivacyK)])
getInteresting = do
   γ <- use types
   h <- case γ of
           Left _ -> throwUnlocatedError (ImpossibleError "getInteresting called on sensitivity context.")
           Right (Ctx (MonCom h')) -> return (H.toList h')
   let f :: [(TeVar, WithRelev PrivacyK)] -> ([(TeVar, DMTypeOf MainKind :@ (Annotation PrivacyK))])
       f xs = [ (x , τ) | (x , WithRelev IsRelevant τ) <- xs ]
   return (unzip (f h))


---------------------------------------------------------------------------
-- Algebraic instances for annot

-- TODO: If we are going to implement 'Multiple', then this instance has to change
-- instance (Show e, IsT MonadDMTC t, SemigroupM t e) => SemigroupM t (WithRelev e) where
instance (Typeable e, SingI e, IsT MonadDMTC t) => SemigroupM t (WithRelev e) where
  (⋆) (WithRelev i e) (WithRelev j f) = WithRelev (i <> j) <$> (e ⋆ f)

instance (IsT MonadDMTC t, DMExtra e) => MonoidM t (WithRelev e) where
  neutral = WithRelev IsRelevant <$> (:@ zeroId ) <$> neutral

instance (IsT MonadDMTC t, DMExtra e) => CheckNeutral t (WithRelev e) where
  checkNeutral (WithRelev i (τ :@ s)) =
    do
      b1 <- checkNeutral τ
      b2 <- checkNeutral s
      return $ and [b1,b2]

