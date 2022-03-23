
-- {-# LANGUAGE UndecidableInstances #-}

module DiffMu.Prelude.MonadicAlgebra
--   (
--     SemigroupM(..), MonoidM(..), CMonoidM(..), SemiringM(..)
-- -- , Abelian(..), Ring(..), Module(..)
--     -- HasInverse(..)
--   )
where

import DiffMu.Imports
import DiffMu.Prelude.Data

-- import Data.Semigroup as All hiding (diff, Min, Max, Any)
-- import Data.Monoid as All hiding (Last, First, getLast, getFirst)

import qualified Prelude as P


chainM2 :: Monad t => (a -> b -> t c) -> t a -> t b -> t c
chainM2 f a b = do
  a' <- a
  b' <- b
  f a' b'

chainM2_L :: Monad t => (a -> b -> t c) -> t a -> b -> t c
chainM2_L f a b = do
  a' <- a
  f a' b

chainM2_R :: Monad t => (a -> b -> t c) -> a -> t b -> t c
chainM2_R f a b = do
  b' <- b
  f a b'

extractIdentity2 :: (a -> b -> Identity c) -> a -> b -> c
extractIdentity2 f a b = runIdentity (f a b)

data NormalizationType = ExactNormalization | SimplifyingNormalization

class Monad t => Normalize t n where
  normalize :: NormalizationType -> n -> t n

normalizeExact = normalize ExactNormalization
normalizeSimplifying = normalize SimplifyingNormalization


instance Monad t => Normalize t Int where
  normalize _ i = pure i

instance (Normalize t a, Normalize t b) => Normalize t (a,b) where
  normalize nt (a,b) = (,) <$> normalize nt a <*> normalize nt b

instance (Normalize t a, Normalize t b) => Normalize t (Either a b) where
  normalize nt (Left a)   = Left <$> normalize nt a
  normalize nt (Right a)  = Right <$> normalize nt a

instance (Normalize t a, Normalize t b) => Normalize t (a :=: b) where
  normalize nt (a :=: b) =  (:=:) <$> normalize nt a <*> normalize nt b

instance Monad t => (Normalize t ()) where
  normalize nt () = pure ()


instance (Normalize t a) => Normalize t [a] where
  normalize nt as = mapM (normalize nt) as

instance (Normalize t a, Normalize t b, Normalize t c) => Normalize t (a, b, c) where
  normalize nt (a,b,c) = (,,) <$> normalize nt a <*> normalize nt b <*> normalize nt c

instance (Normalize t a, Normalize t b, Normalize t c, Normalize t d) => Normalize t (a, b, c, d) where
  normalize nt (a,b,c,d) = (,,,) <$> normalize nt a <*> normalize nt b <*> normalize nt c <*> normalize nt d

instance (Normalize t a, Normalize t b, Normalize t c, Normalize t d, Normalize t e) => Normalize t (a, b, c, d, e) where
  normalize nt (a,b,c,d,e) = (,,,,) <$> normalize nt a <*> normalize nt b <*> normalize nt c <*> normalize nt d <*> normalize nt e


-- class Has a where
--   mempty :: a
-- class Pointed a where
--   pt :: a


class Monad t => SemigroupM t a where
  (⋆) :: a -> a -> t a

(<⋆>) = chainM2 (⋆)
(<⋆)  = chainM2_L (⋆)
(⋆>)  = chainM2_R (⋆)
(⋆!)  = extractIdentity2 (⋆)

-- type Semigroup = SemigroupM Identity

class (SemigroupM t a) => MonoidM t a where
  neutral :: t a
neutralId :: MonoidM Identity a => a
neutralId = runIdentity neutral
-- type Monoid = MonoidM Identity

class (Monad t) => CheckNeutral t a where
  checkNeutral :: a -> t Bool
-- instance (SemigroupM t a) => MonoidM t a

class (MonoidM t a) => CMonoidM t a where
  (+) :: a -> a -> t a
  (+) x y = x ⋆ y
  zero :: t a
  zero = neutral

zeroId :: CMonoidM Identity r => r
zeroId = runIdentity zero

(<+>) = chainM2 (+)
(<+)  = chainM2_L (+)
(+>)  = chainM2_R (+)
(+!)  = extractIdentity2 (+)

-- type Semigroup = SemigroupM Identity

-- class HasOne r where
--   one :: r

class (CMonoidM t r) => SemiringM t r where
  one :: t r
  (⋅) :: r -> r -> t r

oneId :: SemiringM Identity r => r
oneId = runIdentity one

(<⋅>) = chainM2 (⋅)
(<⋅)  = chainM2_L (⋅)
(⋅>)  = chainM2_R (⋅)
(⋅!)  = extractIdentity2 (⋅)

(?:) = liftM2 (:)
(?<>) = liftM2 (<>)


-- NOTE: We do not require the constraint ```(MonoidM t m)```, even though this should be mathematically reasonable.
-- This is because we have cases where the monoidal structure needs a different monad t than the action.
class Monad t => ModuleM t m x where
  (↷) :: m -> x -> t x

-- NOTE: Appearently, these functions cannot be defined using
--       chainM2 and its variants. Reason unclear.
(<↷>) :: ModuleM t m x => t m -> t x -> t x
(<↷>) a b = do
  a' <- a
  b' <- b
  a' ↷ b'

(<↷) :: ModuleM t m x => t m -> x -> t x
(<↷) a b = do
  a' <- a
  a' ↷ b

(↷>) :: ModuleM t m x => m -> t x -> t x
(↷>) a b = do
  b' <- b
  a ↷ b'

(↷!) :: ModuleM Identity m x => m -> x -> x
(↷!) a b = runIdentity (a ↷ b)





instance Monad t => SemigroupM t Int where
  (⋆) a b = pure $ a P.+ b
instance Monad t => MonoidM t Int where
  neutral = pure 0
instance Monad t => CMonoidM t Int where
instance Monad t =>CheckNeutral t Int where
  checkNeutral a = pure (a == 0)

instance Monad t => SemiringM t Int where
  one = pure 1
  (⋅) a b = pure $ a P.* b

instance Monad t => SemigroupM t [a] where
  (⋆) a b = return (a <> b)

instance Monad t => MonoidM t [a] where
  neutral = return (mempty)

instance (Eq a, Monad t) => CheckNeutral t [a] where
  checkNeutral a = return (a == [])


  {-
(?:) :: Monad m => m a -> m [a] -> m [a]
(?:) x xs = (:) <$> x <⋅> xs

{-
class Monoid g => HasInverse g where
  neg :: g -> g

class Monoid t => Module t x where
  (⋅) :: t -> x -> x

class (SemiRing r, HasInverse r) => Ring r
instance (SemiRing r, HasInverse r) => Ring r

class (CMonoid t, HasInverse t) => Abelian t
instance (CMonoid t, HasInverse t) => Abelian t



-- class Group a => Abelian a where
--   (+) :: a -> a -> a
  -- (+) x y = x <> y

-- class Abelian r => Ring r where
--   one :: r
--   (⋅) :: r -> r -> r



-- instance P.Num a => Semigroup a where
--   (<>) a b = a P.+ b

-}
-}
