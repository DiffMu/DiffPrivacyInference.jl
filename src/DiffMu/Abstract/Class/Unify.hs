
{- |
Description: A monad in which unification of the given type can be done.
-}
module DiffMu.Abstract.Class.Unify where

import DiffMu.Prelude
import DiffMu.Abstract.Class.Term
import DiffMu.Abstract.Data.Error
import DiffMu.Abstract.Class.IsT
import DiffMu.Abstract.Class.Constraint


class MonadDMError e t => Unify e t a where
  unify_ :: (MessageLike t msg) => msg -> a -> a -> t a

unify :: (Unify e t a, Normalize (t) a, MessageLike t msg) => msg -> a -> a -> t a
unify name a b = (chainM2 (unify_ name) (normalizeExact a) (normalizeExact b))

unifyFromName :: (isT m, MonadConstraint isT m, Unify e m b, Normalize m b) => IxSymbol -> b -> b -> m b
unifyFromName name a b = do
  msg <- inheritanceMessageFromName name
  unify msg a b
