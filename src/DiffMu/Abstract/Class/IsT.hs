
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

module DiffMu.Abstract.Class.IsT where

import DiffMu.Prelude

class (isT t, Monad t) => IsT (isT :: (* -> *) -> Constraint) (t :: * -> *) | t -> isT where

type HasNormalize :: ((* -> *) -> Constraint) -> (*) -> Constraint
type HasNormalize isT a = forall t. isT t => Normalize (t) a


-- instance (isT t, Monad t) => IsT (isT :: (* -> *) -> Constraint) (t)

-- withIsT :: IsT isT t => (isT t => t a) -> t a
-- withIsT a = a


-- withIsT :: forall isT t a. isT t => (IsT isT t => t a) -> t a
-- withIsT a = withDict (makeDict @isT @t) a


