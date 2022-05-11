
{-# LANGUAGE UndecidableInstances #-}

{- |
Description: Wrapping monoidal combinations (`MonCom`) to use as data types for various contexts.
-}
module DiffMu.Abstract.Data.MonComCtx where

import DiffMu.Prelude
import DiffMu.Abstract.Data.MonadicPolynomial
import DiffMu.Abstract.Class.Term
import DiffMu.Abstract.Data.HashMap

import Data.HashMap.Strict as H

newtype Ctx v x = Ctx (MonCom x v)
  deriving (Generic, DictLike v x)
instance (Normalize t x) => Normalize t (Ctx v x) where
  normalize nt (Ctx m) = Ctx <$> normalize nt m

deriving instance (Typeable a, Typeable v, Typeable b, KEq v, FreeVars v a, FreeVars v b) => FreeVars v (Ctx a b)

instance Functor (Ctx v) where
  fmap f (Ctx (MonCom m)) = Ctx (MonCom (H.map f m))

instance (SemigroupM m x, HasMonCom m x v) => SemigroupM m (Ctx v x) where
  (⋆) (Ctx c) (Ctx d) = Ctx <$> (c ⋆ d)

instance (SemigroupM m x, HasMonCom m x v) => MonoidM m (Ctx v x) where
  neutral = (Ctx <$> neutral)

instance (HasMonCom Identity x v) => Semigroup (Ctx v x) where
  (<>) a b = (a ⋆! b)

instance (HasMonCom Identity x v) => Monoid (Ctx v x) where
  mempty = neutralId


instance (Show v, Show x, DictKey v) => Show (Ctx v x) where
  show (Ctx γ) = showWith ",\n" (\x τ -> show x <> " : " <> show τ) γ ""

instance (ShowPretty v, ShowPretty x, DictKey v) => ShowPretty (Ctx v x) where
  showPretty (Ctx γ) = showWith ",\n" (\x τ -> showPretty x <> " : " <> showPretty τ) γ ""

instance (ShowLocated v, ShowLocated x, DictKey v) => ShowLocated (Ctx v x) where
  showLocated (Ctx γ) = do
    source <- ask
    return $ showWith ",\n" (\x τ -> runReader (showLocated x) source <> " : " <> runReader (showLocated τ) source) γ ""


instance Default (Ctx v x)



instance (MonadInternalError t,
          DictLike k v1 d1, DictLike k v2 d2,
          Show k, Show v1, Show v2, Show d1, Show d2
         ) => DictLikeM t k (Either v1 v2) (Either d1 d2) where
  setValueM k (Left v) (Left d) = return $ Left (setValue k v d)
  setValueM k (Right v) (Right d) = return $ Right (setValue k v d)
  setValueM k v d = internalError $ "Trying to set " <> showT k <> " := " <> showT v <> " in dict " <> showT d
  getValueM k (Left d) = case getValue k d of
    Just x  -> return $ Just (Left (x))
    Nothing -> return $ Nothing
  getValueM k (Right d) = case getValue k d of
    Just x  -> return $ Just (Right (x))
    Nothing -> return $ Nothing
  deleteValueM k (Left d)  = return (Left (deleteValue k d))
  deleteValueM k (Right d) = return (Right (deleteValue k d))

