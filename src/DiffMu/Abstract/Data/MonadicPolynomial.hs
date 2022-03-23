
{-# LANGUAGE UndecidableInstances #-}
module DiffMu.Abstract.Data.MonadicPolynomial where

import DiffMu.Prelude
import DiffMu.Abstract.Class.Term
import DiffMu.Abstract.Class.Constraint
import DiffMu.Abstract.Class.IsT

import qualified Prelude as P
import Data.HashMap.Strict as H

-- foldM

newtype MonCom m v = MonCom (HashMap v m)
  deriving (Generic, Show, Hashable, Eq)
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

    in (MonCom <$> H.fromList <$> (f m (H.toList xs))) -- >>= normalize
    -- in (MonCom <$> (f m xs)) -- >>= normalize

newtype ActV a = ActV a
instance (HasMonCom t m v, MonoidM t v) => ModuleM t (ActV v) (MonCom m v) where
  (↷) (ActV v) (MonCom xs) =
    let g v₁ (v₂,m₂) = do v' <- v₁ ⋆ v₂
                          return (v', m₂)
        f v₁ xs = mapM (g v₁) xs

    -- in (MonCom <$> (f v xs)) -- >>= normalize
    in (MonCom <$> H.fromList <$> (f v (H.toList xs))) -- >>= normalize


-----------------------------------------------------------
-- usage as dictionary

class DictKey k => DictLike k v d | d -> k v where
  setValue :: k -> v -> d -> d
  getValue :: k -> d -> Maybe v
  deleteValue :: k -> d -> d
  emptyDict :: d
  isEmptyDict :: d -> Bool
  getAllKeys :: d -> [k]
  getAllElems :: d -> [v]
  getAllKeyElemPairs :: d -> [(k,v)]
  fromKeyElemPairs :: [(k,v)] -> d

changeValue :: DictLike k v d => k -> (v -> v) -> d -> d
changeValue k f d = case getValue k d of
  Just x -> setValue k (f x) d
  Nothing -> d

popValue :: DictLike k v d => k -> d -> (Maybe v , d)
popValue k d = (getValue k d , deleteValue k d)

restoreValue :: DictLike k v d => d -> k -> d -> (Maybe v , d)
restoreValue oldDict key dict =
  let oldValue = getValue key oldDict
  in case oldValue of
    Nothing        -> (getValue key dict , deleteValue key dict)
    Just oldValue  -> (getValue key dict , setValue key oldValue dict)


getValueMaybe a scope = a >>= (\x -> getValue x scope)
setValueMaybe (Just k) v scope = setValue k v scope
setValueMaybe Nothing v scope = scope

class ShowDict k v d | d -> k v where
  showWith :: String -> (k -> v -> String) -> d -> String -> String

instance (DictKey k) => DictLike k v (MonCom v k) where
  setValue v m (MonCom h) = MonCom (H.insert v m h)
  deleteValue v (MonCom h) = MonCom (H.delete v h)
  getValue k (MonCom h) = h H.!? k
  emptyDict = MonCom H.empty
  isEmptyDict (MonCom h) = H.null h
  getAllKeys (MonCom h) = H.keys h
  getAllElems (MonCom h) = H.elems h
  getAllKeyElemPairs (MonCom h) = H.toList h
  fromKeyElemPairs list = MonCom (H.fromList list)

instance ShowDict k v (MonCom v k) where
  showWith comma merge (MonCom d) emptycase =
    let d' = H.toList d
    in case d' of
      [] -> emptycase
      _  -> intercalate comma ((\(k,v) -> merge k v) <$> d')





-----------------------------------------------------------
-- LinCom


newtype LinCom r v = LinCom { getLinCom :: (MonCom r v) }
  deriving (Generic, Hashable, Default, Eq, DictLike v r, ShowDict v r)

-- instance Show (LinCom r v) where

injectCoeff :: (HasMonCom t r v, MonoidM t v) => r -> t (LinCom r v)
injectCoeff r = do
  o <- neutral
  return (LinCom (MonCom (H.singleton o r)))

                  -- [(r , o)]))
  -- LinCom <$> ((ActM r) ↷> neutral) -- LinCom (MonCom [(r , o)])

injectCoeffId :: (HasMonCom Identity r v, MonoidM Identity v) => r -> (LinCom r v)
injectCoeffId r = LinCom (MonCom (H.singleton neutralId r))
                          -- [(r, neutralId)])
  -- o <- neutral
  -- return (LinCom (MonCom [(r , o)]))

instance (HasMonCom t r v) => SemigroupM t (LinCom r v) where
  (⋆) (LinCom p) (LinCom q) = LinCom <$> (p ⋆ q)

instance (HasMonCom t r v) => MonoidM t (LinCom r v) where
  neutral = LinCom <$> neutral

instance (HasMonCom t r v, SemiringM t r) => ModuleM t (ActM r) (LinCom r v) where
  -- (↷) r (LinCom p) = LinCom <$> (ActM r ↷ p)

  (↷) (ActM m) (LinCom (MonCom xs)) =
    let g m₁ (v₂,m₂) = do m' <- m₁ ⋅ m₂
                          return (v₂, m')
        f m₁ xs = mapM (g m₁) xs

    in (LinCom <$> MonCom <$> H.fromList <$> (f m (H.toList xs))) -- >>= normalize

instance (HasMonCom t r v, MonoidM t v) => ModuleM t (ActV v) (LinCom r v) where
  (↷) v (LinCom p) = LinCom <$> (v ↷ p)


instance (CMonoidM t r, HasMonCom t r v) => CMonoidM t (LinCom r v)


-- instance (HasOne r, HasMonCom t r v, Pointed v) => HasOne (LinCom r v) where
--   one = LinCom (MonCom [(one, pt)])

instance (SemiringM t r, HasMonCom t r v, MonoidM t v) => SemiringM t (LinCom r v) where
  one = f <$> one <*> neutral
    where f a b = LinCom (MonCom (H.singleton b a))

  (⋅) (LinCom (MonCom p)) q = (f p q)
    -- where f :: [(r,v)] -> LinCom r v -> t (LinCom r v)
    where f :: HashMap v r -> LinCom r v -> t (LinCom r v)
          f map q = H.foldrWithKey' g (LinCom <$> neutral) map
            where g xv xr res = (ActM xr) ↷> ((ActV xv) ↷ q) <+> res
          -- f [] q = 
          -- f ((xr,xv) : xs) q = xr ↷> (xv ↷ q) <+> (f xs q)

newtype SingleKinded a (k :: j) = SingleKinded a
  deriving (Eq, Generic, Hashable)

instance Show a => Show (SingleKinded a k) where
  show (SingleKinded a) = show a

-- instance (Typeable j, Typeable v, Typeable (k :: j), FreeVars v a) => FreeVars v (SingleKinded a k) where
--   freeVars (SingleKinded a) = freeVars a

type CPolyM r e v = SingleKinded (LinCom r (MonCom e v))

constCoeff :: (HasMonCom Identity e v, Hashable e, SemiringM Identity e, SemiringM Identity r) => r -> CPolyM r e v k
constCoeff r = SingleKinded $ LinCom (MonCom (H.singleton neutralId r))

-- instance FreeVars


-- deriving via (LinCom r (MonCom e v)) instance (Coercible a b => Coercible (t a) (t v), SemiringM t r) => SemiringM t (CPolyM r e v k)

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

-- instance SemigroupM t a => SemigroupM t (CPolyM r e v k) -- DIFF
-- instance SemiringM t r => MonoidM t (CPolyM r e v k)
-- instance SemiringM t r => CMonoidM t (CPolyM r e v k)
-- instance SemiringM t r => SemiringM t (CPolyM r e v k)
-- instance (HasMonCom t r v, MonoidM t v) => ModuleM t (ActV v) (CPolyM r e v k) where
-- instance (HasMonCom t r v, SemiringM t r) => ModuleM t (ActM r) (CPolyM r e v k) where





injectVarId :: (HasMonCom Identity e v, Hashable e, SemiringM Identity e, SemiringM Identity r) => v -> (CPolyM r e v k)
injectVarId v = SingleKinded $ LinCom (MonCom (H.singleton (MonCom (H.singleton v oneId)) oneId))
                           -- H.singleton (MonCom (H.singleton (v,neutralId)), oneId)))
  -- LinCom (MonCom (H.singleton neutralId r))




-------------------------------------------
-- Term instances


{-
instance (Hashable v, Show v, Show m, Eq v, Eq m, MonoidM Identity m, CheckNeutral Identity m) => Substitute v (MonCom m v) (MonCom m v) where
  substitute σ (MonCom t) =
    let f (v,m) = do vs <- σ v
                     return (ActM m ↷! vs)
    in do x <- mapM f (H.toList t)
          return $ P.foldl (⋆!) neutralId x

instance (Hashable v, Show v, Show m, Eq v, Eq m, MonoidM Identity m, CheckNeutral Identity m) => Term v (MonCom m v) where
  -- type Var (MonCom m v) = v
  var v = MonCom (H.singleton v neutralId) -- [(neutralId, v)]
-}
-- instance (Typeable j, Typeable r, Typeable (v :: j1 -> *), IsKind (k :: j), KEq v, Eq r
--           --  KHashable v, CheckNeutral Identity r,
--           --  SemiringM Identity r, forall k2. Substitute v (CPolyM r Int (v k)) (v k2)))
--           )
--       => FreeVars v (LinCom r (MonCom Int (v k))) where -- (CPolyM r Int (v k) k1)
--   freeVars x = undefined


instance (Typeable j, Typeable r, Typeable v, IsKind (k :: j), KEq v, Eq r, KHashable v, CheckNeutral Identity r, SemiringM Identity r, forall k2. Substitute v (CPolyM r Int (v k)) (v k2)) => Substitute v (CPolyM r Int (v k)) (CPolyM r Int (v k) k1) where
  substitute σ (SingleKinded ls) =
    let
        f (v, e :: Int) = do v' <- substitute σ v
                             vs <- σ v'
                             let vslist = take e (repeat vs)
                             return (P.foldl (⋅!) oneId vslist)
        -- f (e , v) = undefined
        g (MonCom mvs, r :: r) = case runIdentity (checkNeutral r) of
                                  True -> return (zeroId)
                                  False -> 
                                    do mvs' <- mapM f (H.toList mvs)
                                       return $ (ActM r) ↷! P.foldl (⋅!) oneId mvs'
        -- g' (r, mvs) = r ↷! g mvs
        h (LinCom (MonCom ls)) = do ls' <- mapM g (H.toList ls)
                                    return $ P.foldl (+!) zeroId ls'
    in coerce <$> (h ls)




    -- let f (m,v) = do vs <- σ v
    --                  return (m ↷! vs)
    -- in undefined

-- type CPolyM r e v = SingleKinded (LinCom r (MonCom e v))

instance (Show r , Show v, Eq r, SemiringM Identity r) => Show (LinCom r (MonCom Int v)) where
  show (poly) = showWith " + " (\vars r -> factor r vars <> showWith "⋅" f vars "") poly "∑∅"
    where f v 1 = show v
          f v e = show v <> "^" <> show e
          factor r (MonCom vars) = case (H.null vars, (r == oneId)) of
                                            (True,True) -> "1"
                                            (True,False) -> show r
                                            (False,True) -> ""
                                            (False,False) -> show r <> "⋅"
          -- factor r [] = _ -- case r == oneId of
          -- factor r = 

-- instance (Show r , KShow v) => Show (CPolyM r Int (v k) j) where


instance (Typeable r, Typeable j, IsKind (k :: j), Typeable v, KHashable v, KShow v, Show r, KEq v, Eq r, CheckNeutral Identity r, SemiringM Identity r, forall k2. Substitute v (CPolyM r Int (v k)) (v k2)) => Term v (CPolyM r Int (v k)) where
  var (v :: v k2) = case testEquality (typeRep @k) (typeRep @k2) of
    Nothing -> zeroId -- NOTE: WARNING: This should actually be an error. But we currently do not have access to any failure monad here.
    Just Refl -> injectVarId v


    -- coerce x
    -- where x :: CPolyM r Int (v k) k
    --       x = injectVarId v

  -- var v = coerce $ SingleKinded $ LinCom (MonCom (H.singleton (MonCom (H.singleton v oneId)) oneId))-- (injectVarId v)

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
          ) --,

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





    -- LinCom (MonCom [(oneId, var v)])

--------------------------------
-- Normalize instance

instance Normalize t x => Normalize t (MonCom x v) where
  normalize nt (MonCom map) = MonCom <$> mapM (normalize nt) map


-- instance (Normalize t x, Normalize t v, Eq v, Hashable v) => Normalize t (MonCom x v) where
--   normalize (MonCom map) = MonCom <$> H.fromList <$> mapM f (H.toList map)
--     where f (k,v) = (,) <$> normalize k <*> normalize v
{-
-}
