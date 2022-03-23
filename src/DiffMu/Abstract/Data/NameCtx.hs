
module DiffMu.Abstract.Data.NameCtx where

import DiffMu.Prelude
import DiffMu.Abstract.Class.Term

-- import DiffMu.Abstract.Class.Term
-- import DiffMu.Abstract.MonadTC
-- import DiffMu.Abstract.MonadicPolynomial

import qualified Data.Text as T
import qualified Data.HashMap.Strict as H

---------------------------------------------------------------------
-- A simple (non-kinded) context for names
data NameCtx = NameCtx
  { names :: [Symbol]
  , currentCtr :: Int
  }
  deriving (Generic)
instance Default NameCtx
instance Show NameCtx where
  show (NameCtx names _) = "[" <> intercalate ", " (show <$> names) <> "]"

newName :: Text -> NameCtx -> (Symbol, NameCtx)
newName (hint) (NameCtx names ctr) =
  let name = Symbol (hint <> "_" <> T.pack (show ctr))
  in (name , NameCtx (name : names) (ctr +! 1))




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
  , currentCtrK :: Int
  }
instance Default (KindedNameCtx v) where
  def = KindedNameCtx [] 0

instance KShow v => Show (KindedNameCtx v) where
  show (KindedNameCtx names _) = "[" <> intercalate ", " (show <$> names) <> "]"

newKindedName :: (Show (Demote (KindOf k)), SingKind (KindOf k), SingI k, FromSymbol v, Typeable k, Typeable v) => Text -> KindedNameCtx v -> (v k, KindedNameCtx v)
newKindedName (hint) (KindedNameCtx names ctr) =
  let name = (fromSymbol (Symbol (hint <> "_" <> T.pack (show ctr))))
  in (name , KindedNameCtx (SingSomeK (name) : names) (ctr +! 1))

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


