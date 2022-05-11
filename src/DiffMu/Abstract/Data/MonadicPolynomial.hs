
{-# LANGUAGE UndecidableInstances #-}

{- |
Description: Monadic monoidal combinations and monadic polynomials.
-}
module DiffMu.Abstract.Data.MonadicPolynomial where

import DiffMu.Prelude
import DiffMu.Abstract.Class.Term
import DiffMu.Abstract.Class.Constraint
import DiffMu.Typecheck.Constraint.Definitions
import DiffMu.Abstract.Class.IsT
import DiffMu.Abstract.Data.HashMap

import qualified Prelude as P
import Data.HashMap.Strict as H
import qualified Data.Text as T

-- foldM

newtype MonCom m v = MonCom (HashMap v m)
  deriving (Generic, Show, Hashable, Eq, DictLike v m)
instance Default (MonCom m v) where
  def = MonCom H.empty
deriving instance (Typeable a, Typeable v, Typeable b, KEq v, FreeVars v a, FreeVars v b) => FreeVars v (MonCom a b)

class (MonoidM t m, CheckNeutral t m, Eq v, Hashable v)    => HasMonCom t m v
instance (MonoidM t m, CheckNeutral t m, Eq v, Hashable v) => HasMonCom t m v


instance (HasMonCom t m v) => SemigroupM t (MonCom m v) where
  (⋆) (MonCom m) (MonCom n) = MonCom <$> H.foldlWithKey f (pure m) n
    where f mm x a = do
            mm' <- mm
            case H.lookup x mm' of
              Just a' -> do a'' <- a' ⋆ a
                            return (H.insert x a'' mm')
              Nothing -> return (H.insert x a mm')

instance (HasMonCom t m v) => MonoidM t (MonCom m v) where
  neutral = pure (MonCom H.empty)

-- actions on moncom

newtype ActM a = ActM a
instance (HasMonCom t m v) => ModuleM t (ActM m) (MonCom m v) where
  (↷) (ActM m) (MonCom xs) =
    let g m₁ (v₂,m₂) = do m' <- m₁ ⋆ m₂
                          return (v₂, m')
        f m₁ xs = mapM (g m₁) xs

    in (MonCom <$> H.fromList <$> (f m (H.toList xs)))

newtype ActV a = ActV a
instance (HasMonCom t m v, MonoidM t v) => ModuleM t (ActV v) (MonCom m v) where
  (↷) (ActV v) (MonCom xs) =
    let g v₁ (v₂,m₂) = do v' <- v₁ ⋆ v₂
                          return (v', m₂)
        f v₁ xs = mapM (g v₁) xs

    in (MonCom <$> H.fromList <$> (f v (H.toList xs)))


-----------------------------------------------------------
-- usage as dictionary



class ShowDict k v d | d -> k v where
  showWith :: StringLike s => s -> (k -> v -> s) -> d -> s -> s


instance ShowDict k v (MonCom v k) where
  showWith comma merge (MonCom d) emptycase =
    let d' = H.toList d
    in case d' of
      [] -> emptycase
      _  -> intercalateS comma (sort ((\(k,v) -> merge k v) <$> d'))





-----------------------------------------------------------
-- LinCom


newtype LinCom r v = LinCom { getLinCom :: (MonCom r v) }
  deriving (Generic, Hashable, Default, Eq, DictLike v r, ShowDict v r)


injectCoeff :: (HasMonCom t r v, MonoidM t v) => r -> t (LinCom r v)
injectCoeff r = do
  o <- neutral
  return (LinCom (MonCom (H.singleton o r)))


injectCoeffId :: (HasMonCom Identity r v, MonoidM Identity v) => r -> (LinCom r v)
injectCoeffId r = LinCom (MonCom (H.singleton neutralId r))

instance (HasMonCom t r v) => SemigroupM t (LinCom r v) where
  (⋆) (LinCom p) (LinCom q) = LinCom <$> (p ⋆ q)

instance (HasMonCom t r v) => MonoidM t (LinCom r v) where
  neutral = LinCom <$> neutral

instance (HasMonCom t r v, SemiringM t r) => ModuleM t (ActM r) (LinCom r v) where

  (↷) (ActM m) (LinCom (MonCom xs)) =
    let g m₁ (v₂,m₂) = do m' <- m₁ ⋅ m₂
                          return (v₂, m')
        f m₁ xs = mapM (g m₁) xs

    in (LinCom <$> MonCom <$> H.fromList <$> (f m (H.toList xs)))

instance (HasMonCom t r v, MonoidM t v) => ModuleM t (ActV v) (LinCom r v) where
  (↷) v (LinCom p) = LinCom <$> (v ↷ p)


instance (CMonoidM t r, HasMonCom t r v) => CMonoidM t (LinCom r v)


instance (SemiringM t r, HasMonCom t r v, MonoidM t v) => SemiringM t (LinCom r v) where
  one = f <$> one <*> neutral
    where f a b = LinCom (MonCom (H.singleton b a))

  (⋅) (LinCom (MonCom p)) q = (f p q)
    where f :: HashMap v r -> LinCom r v -> t (LinCom r v)
          f map q = H.foldrWithKey' g (LinCom <$> neutral) map
            where g xv xr res = (ActM xr) ↷> ((ActV xv) ↷ q) <+> res

newtype SingleKinded a (k :: j) = SingleKinded a
  deriving (Eq, Generic, Hashable)

instance Show a => Show (SingleKinded a k) where
  show (SingleKinded a) = show a


instance ShowLocated a => ShowLocated (SingleKinded a k) where
  showLocated (SingleKinded a) = showLocated a


type CPolyM r e v = SingleKinded (LinCom r (MonCom e v))

constCoeff :: (HasMonCom Identity e v, Hashable e, SemiringM Identity e, SemiringM Identity r) => r -> CPolyM r e v k
constCoeff r = SingleKinded $ LinCom (MonCom (H.singleton neutralId r))


instance SemigroupM t a => SemigroupM t (SingleKinded a k) where
  (⋆) (SingleKinded a) (SingleKinded b) = SingleKinded <$> (a ⋆ b)

instance MonoidM t a => MonoidM t (SingleKinded a k) where
  neutral = SingleKinded <$> neutral

instance CMonoidM t a => CMonoidM t (SingleKinded a k) where

instance SemiringM t a => SemiringM t (SingleKinded a k) where
  (⋅) (SingleKinded a) (SingleKinded b) = SingleKinded <$> (a ⋅ b)
  one = SingleKinded <$> one

instance ModuleM t (ActV v) a => ModuleM t (ActV v) (SingleKinded a k) where
  (↷) a (SingleKinded b) = SingleKinded <$> (a ↷ b)

instance ModuleM t (ActM v) a => ModuleM t (ActM v) (SingleKinded a k) where
  (↷) a (SingleKinded b) = SingleKinded <$> (a ↷ b)





injectVarId :: (HasMonCom Identity e v, Hashable e, SemiringM Identity e, SemiringM Identity r) => v -> (CPolyM r e v k)
injectVarId v = SingleKinded $ LinCom (MonCom (H.singleton (MonCom (H.singleton v oneId)) oneId))



-------------------------------------------
-- Term instances




instance (Typeable j, Typeable r, Typeable v, IsKind (k :: j), KEq v, Eq r, KHashable v, CheckNeutral Identity r, SemiringM Identity r, forall k2. Substitute v (CPolyM r Int (v k)) (v k2)) => Substitute v (CPolyM r Int (v k)) (CPolyM r Int (v k) k1) where
  substitute σ (SingleKinded ls) =
    let
        f (v, e :: Int) = do v' <- substitute σ v
                             vs <- σ v'
                             let vslist = take e (repeat vs)
                             return (P.foldl (⋅!) oneId vslist)
        g (MonCom mvs, r :: r) = case runIdentity (checkNeutral r) of
                                  True -> return (zeroId)
                                  False -> 
                                    do mvs' <- mapM f (H.toList mvs)
                                       return $ (ActM r) ↷! P.foldl (⋅!) oneId mvs'
        h (LinCom (MonCom ls)) = do ls' <- mapM g (H.toList ls)
                                    return $ P.foldl (+!) zeroId ls'
    in coerce <$> (h ls)



instance (Show r , Show v, Eq r, SemiringM Identity r) => Show (LinCom r (MonCom Int v)) where
  show (poly) = showWith " + " (\vars r -> factor r vars <> showWith "⋅" f vars "") poly "0"
    where f v 1 = show v
          f v e = show v <> "^" <> show e
          factor r (MonCom vars) = case (H.null vars, (r == oneId)) of
                                            (True,True) -> "1"
                                            (True,False) -> show r
                                            (False,True) -> ""
                                            (False,False) -> show r <> "⋅"

instance (Show r , Show v, Eq r, SemiringM Identity r) => ShowLocated (LinCom r (MonCom Int v)) where
  showLocated = pure . T.pack . show




instance (HasVarPriority v, Typeable r, Typeable j, IsKind (k :: j), Typeable v, KHashable v, KShow v, Show r, KEq v, Eq r, CheckNeutral Identity r, SemiringM Identity r, forall k2. Substitute v (CPolyM r Int (v k)) (v k2)) => Term v (CPolyM r Int (v k)) where
  var (v :: v k2) = case testEquality (typeRep @k) (typeRep @k2) of
    Nothing -> zeroId -- NOTE: WARNING: This should actually be an error. But we currently do not have access to any failure monad here.
    Just Refl -> injectVarId v
  isVar (SingleKinded (LinCom (MonCom a)) :: SingleKinded (LinCom r (MonCom Int (v k))) k1) = 
    case testEquality (typeRep @k) (typeRep @k1) of
      Nothing -> undefined -- NOTE: WARNING: This should actually be an error. But we currently do not have access to any failure monad here.
      Just Refl ->
        case H.toList a of
          [(MonCom avars, ar)] ->
            case H.toList avars of
              [(v,1)] | ar == oneId -> Just v
              _ -> Nothing
          _ -> Nothing



-----------------------------------------------------------
-- unification

-- type HasPolyTerm :: (j -> *) -> * -> j -> Constraint
class  (Typeable r, Typeable j, IsKind (k :: j), Typeable v, KHashable v, KShow v, Show r, KEq v, Eq r, CheckNeutral Identity r, SemiringM Identity r) => HasPolyTerm v r (k :: j)
instance (Typeable r, Typeable j, IsKind (k :: j), Typeable v, KHashable v, KShow v, Show r, KEq v, Eq r, CheckNeutral Identity r, SemiringM Identity r) => HasPolyTerm v r (k :: j)

class CheckContains x y where
  checkContains :: x -> Maybe y

instance forall isT j v r (k :: j). (HasPolyTerm v r k,
          (forall t e. (IsT isT t => MonadConstraint isT (t)))

          , forall t e. (IsT isT t => MonadTerm @j (CPolyM r Int (v k)) (t)) --,
          -- (VarFam (CPolyM r Int (v k)) ~ v)
          , CheckContains (v k) (VarFam (CPolyM r Int (v k)) k)
          )

          => Solve isT IsEqual (CPolyM r Int (v k) k, CPolyM r Int (v k) k) where
  solve_ Dict _ name (IsEqual (x, y)) = solve_impl x y
    where solve_impl (SingleKinded (LinCom (MonCom a))) (SingleKinded (LinCom (MonCom b))) = f (H.toList a) (H.toList b)
          f a b | a == b = dischargeConstraint @isT name
          f a b | and [isZero a, isZero b] = dischargeConstraint @isT name
          f [(MonCom avars, ar)] [(MonCom bvars, br)] = g (toList avars) (toList bvars)
              where g [] []     | ar == br    = dischargeConstraint @isT name
                    g [] []     | otherwise   = failConstraint @isT name
                    g [(v,1)] _ | ar == oneId = case checkContains v of
                                                  Just v' -> addSub (v' := y) >> dischargeConstraint @isT name
                                                  Nothing -> return ()
                    g _ [(w,1)] | br == oneId = case checkContains w of
                                                  Just w' -> addSub (w' := x) >> dischargeConstraint @isT name
                                                  Nothing -> return ()
                    g _ _       = return ()

          f [(MonCom avars, ar)] bs = g (toList avars)
              where g [(v,1)] | ar == oneId = case checkContains v of
                                                  Just v' -> addSub (v' := y) >> dischargeConstraint @isT name
                                                  Nothing -> return ()
                    g _       = return ()

          f as [(MonCom bvars, br)] = g (toList bvars)
              where g [(w,1)] | br == oneId = case checkContains w of
                                                Just w' -> addSub (w' := x) >> dischargeConstraint @isT name
                                                Nothing -> return ()
                    g _       = return ()

          f _ _ = return ()

          -- we need a special test for zero, since there are two representation for it
          isZero [] = True
          isZero [(MonCom avars, ar)] | ar == zeroId = True
          isZero _ = False



--------------------------------
-- Normalize instance

instance Normalize t x => Normalize t (MonCom x v) where
  normalize nt (MonCom map) = MonCom <$> mapM (normalize nt) map

