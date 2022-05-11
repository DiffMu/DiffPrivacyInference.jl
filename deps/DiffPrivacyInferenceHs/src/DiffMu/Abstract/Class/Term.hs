{-# LANGUAGE UndecidableInstances #-}

{- |
Description: Terms and substitutions.

Deals with multi-kinded terms and accumulation of their substitutions.
-}
module DiffMu.Abstract.Class.Term where

import DiffMu.Prelude
import Data.HashMap.Strict as H
import Debug.Trace

------------------------------------------------------------------------------------------
-- Sum type for multi-kinded types
------------------------------------------------------------------------------------------

data SomeK (v :: j -> *) where
  SomeK :: (Typeable v, Typeable k, SingI k) => v k -> SomeK v

compareVar :: KEq a => SomeK a -> SomeK a -> Bool
compareVar (SomeK (x :: a k)) (SomeK (y :: a k2)) =
    case testEquality (typeRep @k) (typeRep @k2) of
      Just Refl -> x == y
      Nothing -> False

instance (KHashable v) => Hashable (SomeK v) where
  hashWithSalt salt (SomeK x) = hashWithSalt salt x

instance (KShow v) => Show (SomeK (v :: j -> *)) where
  show (SomeK (x :: v k)) = show x

instance KEq v => Eq (SomeK v) where
  SomeK (a) == SomeK (b) = case testEquality (typeOf a) (typeOf b) of
    Nothing -> False
    Just Refl -> a == b

filterSomeK :: forall v k2. (Typeable k2) => [(SomeK v)] -> [v k2]
filterSomeK vs = [v | Just v <- (f <$> vs)]
  where
    f :: SomeK v -> Maybe (v k2)
    f (SomeK (v :: v k)) = 
      case testEquality (typeRep @k) (typeRep @k2) of
        Nothing -> Nothing
        Just Refl -> Just v

filterSomeKPair :: forall v k2 x. (Typeable k2) => [(SomeK v,x)] -> [(v k2, x)]
filterSomeKPair = undefined

------------------------------------------------------------------------------------------
-- Tracking of whether a substitution changed something (MonadWatch)
------------------------------------------------------------------------------------------

data Changed = IsChanged | NotChanged
  deriving (Generic, Show, Eq)

instance Default Changed where
  def = NotChanged

type Watch = Writer Changed

instance Semigroup Changed where
  (<>) IsChanged a = IsChanged
  (<>) a IsChanged = IsChanged
  (<>) NotChanged NotChanged = NotChanged

instance Monoid Changed where
  mempty = NotChanged

class Monad t => MonadWatch t where
  resetChanged :: t ()
  notifyChanged :: t ()
  getChanged :: t Changed

------------------------------------------------------------------------------------------
-- Raw multikinded substitutions (data type)
------------------------------------------------------------------------------------------
data Sub x a k = (:=) (x k) (a k)
data Sub' x a k j = (:=~) (x k) (a j)

fstSub (x := _) = x

instance (KShow x, KShow a) => Show (Sub x a k) where
  show (x := a) = show x <> " := " <> show a

instance (KShow x, KShow a) => Show (Sub' x a k j) where
  show (x :=~ a) = show x <> " := " <> show a

newtype ListK a k = ListK [a k]
  deriving Show

------------------------------------------------------------------------------------------
-- multi-kinded type with free vars (class)
------------------------------------------------------------------------------------------


class (Typeable v, Typeable a, forall k. Eq (v k)) => FreeVars (v :: j -> *) (a :: *) where
  freeVars :: a -> [SomeK v]


instance FreeVars v a => FreeVars v [a] where
  freeVars [] = []
  freeVars (τ:τs) = freeVars τ <> freeVars τs

instance (Typeable x, FreeVars v a, FreeVars v x) => FreeVars v (H.HashMap x a) where
  freeVars h = freeVars (H.toList h)

instance (FreeVars v a, FreeVars v b) => FreeVars v (a , b) where
  freeVars (a, b) = freeVars a <> freeVars b

instance (FreeVars v a, FreeVars v b, FreeVars v c) => FreeVars v (a , b, c) where
  freeVars (a, b, c) = freeVars a <> freeVars b <> freeVars c

instance (FreeVars v a, FreeVars v b, FreeVars v c, FreeVars v d) => FreeVars v (a , b, c, d) where
  freeVars (a, b, c, d) = freeVars a <> freeVars b <> freeVars c <> freeVars d

instance (FreeVars v a, FreeVars v b, FreeVars v c, FreeVars v d, FreeVars v e) => FreeVars v (a , b, c, d, e) where
  freeVars (a, b, c, d, e) = freeVars a <> freeVars b <> freeVars c <> freeVars d <> freeVars e

instance (FreeVars v a) => FreeVars v (Maybe a) where
  freeVars (Just a) = freeVars a
  freeVars (Nothing) = mempty


------------------------------------------------------------------------------------------
-- Substitute
--   multi-kinded type with substitutions
------------------------------------------------------------------------------------------

class (Typeable v, Typeable a, forall k. Eq (v k)) => Substitute (v :: j -> *) (a :: j -> *) x where
  substitute :: (Monad t) => (forall k. (IsKind k) => v k -> t (a k)) -> (x -> t x)


instance (Substitute v x a, Substitute v x b, Substitute v x c, Substitute v x d, Substitute v x e) => Substitute v x (a, b, c, d, e) where
  substitute σs (a, b, c, d, e) = (,,,,) <$> substitute σs a <*> substitute σs b <*> substitute σs c <*> substitute σs d <*> substitute σs e

instance (Substitute v x a, Substitute v x b, Substitute v x c, Substitute v x d) => Substitute v x (a, b, c, d) where
  substitute σs (a, b, c, d) = (,,,) <$> substitute σs a <*> substitute σs b <*> substitute σs c <*> substitute σs d

instance (Substitute v x a, Substitute v x b, Substitute v x c) => Substitute v x (a, b, c) where
  substitute σs (a, b, c) = (,,) <$> substitute σs a <*> substitute σs b <*> substitute σs c

instance (Substitute v a x, Substitute v a y) => Substitute v a (x,y) where
  substitute σs (x,y) = (,) <$> substitute σs x <*> substitute σs y

instance (Substitute v x a, Substitute v x b) => Substitute v x (a :=: b) where
  substitute σs (a :=: b) = (:=:) <$> substitute σs a <*> substitute σs b

instance Substitute v x a => Substitute v x [a] where
  substitute σs xs = mapM (substitute σs) xs

instance Substitute v x a => Substitute v x (Maybe a) where
  substitute σs (Just a) = Just <$> substitute σs a
  substitute σs (Nothing) = pure Nothing

------------------------------------------------------------------------------------------
-- Term
--   (multi-kinded type where substitution acts on itself)
------------------------------------------------------------------------------------------

class (KHashable v, KShow v, KShow a, KEq v, HasVarPriority v, forall k. (Substitute v a (a k))) => Term v a where
  var :: IsKind k => v k -> a k
  -- varPriority :: IsKind k => Proxy a -> v k -> NamePriority
  isVar :: IsKind k => a k -> Maybe (v k)

------------------------------------------------------------------------------------------
-- multi-kinded substitutions
------------------------------------------------------------------------------------------

data Subs v a where
  Subs :: Term v a => (HashMap (SomeK v) (SomeK a)) -> Subs v a

instance Show (Subs v a) where
  show (Subs s) = intercalate ", " ((\(SomeK x, SomeK a) -> show (x :=~ a)) <$> toList s)

instance Term v a => Default (Subs v a) where
  def = Subs empty


singletonSub :: (Term x a, IsKind k) => Sub x a k -> Subs x a
singletonSub ((x :: x k) := (a :: a k)) = case isVar @x a of
  Just av | varPriority x >= varPriority av  -- if the priority of x is higher, we replace `av`
           -> Subs (singleton (SomeK @_ @k av) (SomeK (var x)))
  _ -> Subs (singleton (SomeK @_ @k x) (SomeK a))

removeFromSubstitution :: (Monad t, Term v a) => [SomeK v] -> (forall k. IsKind k => v k -> t (a k)) -> (forall k. IsKind k => v k -> t (a k))
removeFromSubstitution vars σ x = case (SomeK x) `elem` vars of
  True -> pure (var x)
  False -> σ x

trySubstitute :: (MonadImpossible t, MonadWatch t, Term v a, IsKind k) => Subs v a -> v k -> t (a k)
trySubstitute (Subs m) (x :: v k) = case H.lookup (SomeK x) m of
  Just (SomeK (a :: a k2))  -> do
    case testEquality (typeRep @k) (typeRep @k2) of
      Nothing -> impossible $ "Encountered a wrongly kinded substitution: " <> showT (typeRep @k) <> " ≠ " <> showT (typeRep @k2)
      Just Refl -> notifyChanged >> pure a

  Nothing -> pure (var x)

substituteSingle :: (Typeable k, Term v a) => Sub v a k -> a j -> a j
substituteSingle ((x :: v k) := (a :: a k)) b = runIdentity (substitute f b)
  where f :: (forall k. (IsKind k) => v k -> Identity (a k))
        f (v :: v k2) = case testEquality (typeRep @k) (typeRep @k2) of
          Nothing -> pure (var v)
          Just Refl -> g v
            where g v | v == x    = pure a
                  g v | otherwise = pure (var v)

wellkindedSub :: (IsKind k, Typeable j, Term v a, Typeable k => FreeVars v (a k), MonadImpossible t, MonadUnificationError t) => Sub' v a k j -> t (Sub v a k)
wellkindedSub ((x :: v k) :=~ (a :: a j)) =
    case testEquality (typeRep @k) (typeRep @j) of
      Nothing -> impossible $ "Encountered a wrongly kinded substitution: " <> showT (typeRep @k) <> " ≠ " <> showT (typeRep @j)
      Just Refl -> do
        -- occur check
        let varsInA = freeVars a
        case x `elem` filterSomeK varsInA of
          False -> pure ()
          True -> unificationError (var x) a

        return (x := a)

substituteSingle' :: (Typeable k, Term v a) => Sub v a k -> SomeK a -> SomeK a
substituteSingle' ((x :: v k) := (a :: a k)) (SomeK (a0 :: a j)) = SomeK (substituteSingle (x := a) a0)




instance (MonadImpossible t, MonadUnificationError t, Term v a, forall k. Typeable k => FreeVars v (a k)) => SemigroupM t (Subs v a) where
  (⋆) (Subs m) (Subs n) = Subs <$> H.foldlWithKey f (pure m) n
    where f mm (SomeK (x :: v k)) (SomeK a) = do
            mm' <- mm
            case H.lookup (SomeK x) mm' of
              Just (SomeK a') -> impossible $ "Tried to extend a set of substitutions which already contains " <> showT (x :=~ a') <> " with a new substitution of the same variable, " <> showT (x :=~ a) <> "."
              Nothing -> do σ <- wellkindedSub (x :=~ a)
                            let mm1 = H.map (substituteSingle' σ) mm'
                            return (H.insert (SomeK x) (SomeK a) mm1)

instance (MonadImpossible t, MonadUnificationError t, Term v a, forall k. FreeVars v (a k)) => MonoidM t (Subs v a) where
  neutral = pure (Subs H.empty)

instance (MonadImpossible t, MonadWatch t, Term v a, Substitute v a x) => ModuleM t (Subs v a) x where
  (↷) σs a = substitute (trySubstitute σs) a


------------------------------------------------------------------------------------------
-- Monad keeping track of substitutions
------------------------------------------------------------------------------------------

class (Monad t, Term (VarFam a) a) => MonadTerm (a :: j -> *) t where
  type VarFam (a :: j -> *) :: j -> *
  newVar :: (IsKind k) => t (a k)
  addSub :: (IsKind k) => Sub (VarFam a) a k -> t ()
  getSubs :: t (Subs (VarFam a) a)
