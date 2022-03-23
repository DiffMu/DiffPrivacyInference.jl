
module DiffMu.Prelude.Data where

import DiffMu.Imports as All hiding (msum)

data (:=:) a b = (:=:) a b

instance (Show a, Show b) => Show (a :=: b) where
  show (a :=: b) = show a <> " :=: " <> show b




