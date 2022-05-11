
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

{- |
Description: The class `IsT` describes the property of a monad being member of a subclass of monads.
-}
module DiffMu.Abstract.Class.IsT where

import DiffMu.Prelude

class (isT t, Monad t) => IsT (isT :: (* -> *) -> Constraint) (t :: * -> *) | t -> isT where

type HasNormalize :: ((* -> *) -> Constraint) -> (*) -> Constraint
type HasNormalize isT a = forall t. isT t => Normalize (t) a




