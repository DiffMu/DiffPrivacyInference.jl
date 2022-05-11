
{-# LANGUAGE UndecidableInstances #-}

module DiffMu.Prelude.Algebra
  (
    CMonoid(..), Monoid, Abelian(..), SemiRing(..), Ring(..), Module(..),
    HasInverse(..)
    -- module P
  )
where

import DiffMu.Imports

import Data.Semigroup as All hiding (diff, Min, Max, Any)
import Data.Monoid as All hiding (Last, First, getLast, getFirst)

import qualified Prelude as P

class Monoid a => CMonoid a where
  (+) :: a -> a -> a
  (+) x y = x <> y

class CMonoid r => SemiRing r where
  one :: r
  (*) :: r -> r -> r

class Monoid g => HasInverse g where
  neg :: g -> g

class Monoid m => Module m x where
  (⋅) :: m -> x -> x

class (SemiRing r, HasInverse r) => Ring r
instance (SemiRing r, HasInverse r) => Ring r

class (CMonoid m, HasInverse m) => Abelian m
instance (CMonoid m, HasInverse m) => Abelian m


