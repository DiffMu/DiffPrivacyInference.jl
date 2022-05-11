
{- |
Description: Kinded and unkinded name contexts.

These are contexts without any "type information" (except the kinding in the kinded case),
i.e., only a list of names. Used for type, and the various term variables.
-}
module DiffMu.Abstract.Data.NameCtx where

import DiffMu.Prelude
import DiffMu.Abstract.Class.Term


import qualified Data.Text as T
import qualified Data.HashMap.Strict as H

import qualified Prelude as P

---------------------------------------------------------------------
-- Utility
getAndInc :: (DictKey k) => H.HashMap k Int -> k -> (Int, H.HashMap k Int)
getAndInc d k = case H.lookup k d of
  Just v -> (v, H.insert k (v P.+ 1) d)
  Nothing -> (0, H.insert k (1) d)

---------------------------------------------------------------------
-- A simple (non-kinded) context for names
data NameCtx = NameCtx
  { names :: [IxSymbol]
  , currentCtr :: H.HashMap Symbol Int
  }
  deriving (Generic)
instance Default NameCtx where
  def = NameCtx [] H.empty

instance Show NameCtx where
  show (NameCtx names _) = "[" <> intercalate ", " (show <$> names) <> "]"

newName :: NamePriority -> Text -> NameCtx -> (IxSymbol, NameCtx)
newName np (hint) (NameCtx names ctrmap) =
  let (ctr, ctrmap') = getAndInc ctrmap (Symbol hint)
      name = IxSymbol (Symbol hint, ctr, np)
  in (name , NameCtx (name : names) (ctrmap'))




---------------------------------------------------------------------
-- A kinded context for names

data SingSomeK (v :: j -> *) where
  SingSomeK :: (Show (Demote (KindOf k)), SingKind (KindOf k), SingI k, Typeable v, Typeable k) => v k -> SingSomeK v

instance Eq (SingSomeK SymbolOf) where
  SingSomeK (a) == SingSomeK (b) = case testEquality (typeOf a) (typeOf b) of
    Nothing -> False
    Just Refl -> a == b

instance Hashable (SingSomeK SymbolOf) where
  hashWithSalt s (SingSomeK x) = s `hashWithSalt` x

instance DictKey (SingSomeK SymbolOf)

instance KShow v => Show (SingSomeK v) where
  show (SingSomeK (s :: v k)) = show s <> " : " <> show (demote @k)

data KindedNameCtx (v :: j -> *) = KindedNameCtx
  {
    namesK :: [SingSomeK v]
  , currentCtrK :: H.HashMap (Symbol) Int
  }
instance Default (KindedNameCtx v) where
  def = KindedNameCtx [] H.empty

instance KShow v => Show (KindedNameCtx v) where
  show (KindedNameCtx names _) = "[" <> intercalate ", " (show <$> names) <> "]"

newKindedName :: (Show (Demote (KindOf k)), SingKind (KindOf k), SingI k, FromSymbol v, Typeable k, Typeable v) => NamePriority -> Text -> KindedNameCtx v -> (v k, KindedNameCtx v)
newKindedName np (hint) (KindedNameCtx names ctrmap) =
  let (ctr, ctrmap') = getAndInc ctrmap (Symbol hint)
      name = (fromSymbol (Symbol hint) ctr np) -- (hint <> "_" <> T.pack (show ctr))))
  in (name , KindedNameCtx (SingSomeK (name) : names) (ctrmap'))

-- makeSing :: forall j (v :: j -> *). (forall k. (Show (Demote (KindOf k)))) => SomeK v -> SingSomeK v
-- makeSing (SomeK v) = SingSomeK v

-- addKindedNames :: [SomeK v] -> [SingSomeK v] -> [SingSomeK v]
-- addKindedNames xs ys = ys <> [SingSomeK x | SomeK x <- xs]

removeKindedNameBySubstitution :: ((forall j. Eq (v j)), Typeable k) => Sub v a k -> [SingSomeK v] -> [SingSomeK v]
removeKindedNameBySubstitution ((x :: v k) := _) names =
  let f :: Typeable j => v j -> Maybe (v j)
      f (v :: v j) = case testEquality (typeRep @j) (typeRep @k) of
        Just Refl -> case v == x of
          True -> Nothing
          False -> Just v
        Nothing -> Just v
      g :: SingSomeK v -> Maybe (SingSomeK v)
      g (SingSomeK x) = SingSomeK <$> (f x)
      names' = [n | (Just n) <- g <$> names]
  in names'



removeNameBySubstitution :: ((forall j. Eq (v j)), Typeable k) => Sub v a k -> KindedNameCtx v -> KindedNameCtx v
removeNameBySubstitution sub (KindedNameCtx names ctr) =
  KindedNameCtx (removeKindedNameBySubstitution sub names) ctr

  -- let f :: Typeable j => v j -> Maybe (v j)
  --     f (v :: v j) = case testEquality (typeRep @j) (typeRep @k) of
  --       Just Refl -> case v == x of
  --         True -> Nothing
  --         False -> Just v
  --       Nothing -> Just v
  --     g :: SingSomeK v -> Maybe (SingSomeK v)
  --     g (SingSomeK x) = SingSomeK <$> (f x)
  --     names' = [n | (Just n) <- g <$> names]
  -- in KindedNameCtx names' ctr


