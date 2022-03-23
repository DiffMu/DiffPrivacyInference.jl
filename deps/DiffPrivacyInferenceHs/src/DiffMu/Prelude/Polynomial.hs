
module DiffMu.Prelude.Polynomial where

import DiffMu.Imports
import DiffMu.Prelude.Algebra

-- import GHC.Generics as All (Generic)
-- import Prelude as All (Show, IO, putStrLn, undefined, otherwise, fst, snd)

import Data.Semigroup as All hiding (diff, Min, Max, Any, WrapMonoid)
import Data.Monoid as All hiding (Last, First, getLast, getFirst, WrapMonoid)


import DiffMu.Prelude.Algebra

class Normalizable n where
  normalize :: n -> n

newtype MonDict m v = MonDict [(m,v)]
  deriving (Generic, Show)

class (Monoid m, Eq m, Ord v)    => HasMonDict m v
instance (Monoid m, Eq m, Ord v) => HasMonDict m v

instance (HasMonDict m v) => Normalizable (MonDict m v) where
  normalize (MonDict xs) = MonDict (sor xs [])

    where singl :: (m,v) -> [(m,v)]
          singl (m,v) | m == mempty = []
          singl (m,v) | otherwise = [(m,v)]

          ins :: (m,v) -> [(m,v)] -> [(m,v)]
          ins (m,v) [] = singl (m,v)
          ins (m,v) ((m2, v2) : xs) = f (m,v) (m2,v2) xs (compare v v2)
             where f (m,v) (m2,v2) xs LT = singl (m,v) <> ((m2,v2) : xs)
                   f (m,v) (m2,v2) xs EQ = singl ((m <> m2), v) <> xs
                   f (m,v) (m2,v2) xs GT = (m2,v2) : ins (m,v) xs

          sor :: [(m,v)] -> [(m,v)] -> [(m,v)]
          sor [] ys = ys
          sor (x:xs) ys = sor xs (ins x ys)


instance (HasMonDict m v) => Semigroup (MonDict m v) where
  (<>) (MonDict xs) (MonDict ys) = normalize (MonDict (xs <> ys))

instance (HasMonDict m v) => Monoid (MonDict m v) where
  mempty = MonDict []

instance (HasMonDict m v) => Module m (MonDict m v) where
  (⋅) m (MonDict xs) = normalize (MonDict (f m xs))
    where f m xs = fmap (\(m1,v1) -> (m <> m1, v1)) xs

instance (HasMonDict m v, Monoid v) => Module v (MonDict m v) where
  (⋅) v (MonDict xs) = normalize (MonDict (f v xs))
    where f v xs = fmap (\(m1,v1) -> (m1, v <> v1)) xs


instance (HasMonDict m v) => Eq (MonDict m v) where
  (==) (xs) (ys) = f (normalize xs) (normalize ys)
    where
      f (MonDict xs) (MonDict ys) = xs == ys

instance (HasMonDict m v) => Ord (MonDict m v) where
  compare (xs) (ys) = f (normalize xs) (normalize ys)
    where
      f (MonDict xs) (MonDict ys) = compare (fmap snd xs) (fmap snd ys)

-- data PVars e v = PVars (MonDict e v)
--   deriving (Generic, Show)

-- instance Normalizable (Monom r v) where
--   normalize (Monom r vs) = Monom r (sort vs)
-- (PVars e v)

instance (HasInverse m, HasMonDict m v) => HasInverse (MonDict m v) where
  neg (MonDict xs) = MonDict (fmap (\(m,v) -> (neg m, v)) xs)

-- newtype WrapMonoid m = WrapMonoid m
--   deriving (Generic, Show)

-- instance (Ring r) => Monoid (WrapMonoid r) where

newtype Poly r v = Poly (MonDict r v)
  deriving (Generic, Show, Semigroup, Monoid, HasInverse)


instance (HasMonDict r v) => Module r (Poly r v) where
  (⋅) r (Poly p) = Poly (r ⋅ p)

instance (CMonoid r, HasMonDict r v) => CMonoid (Poly r v)

instance (SemiRing r, HasMonDict r v, Monoid v) => SemiRing (Poly r v) where
  one = Poly (MonDict [(one, mempty)])
  (*) (Poly (MonDict p)) (Poly q) = Poly (f p q)
    where f [] q = mempty
          f ((xr,xv) : xs) q = (xr ⋅ (xv ⋅ q)) <> f xs q

type CPoly r e v = Poly r (MonDict e v)


