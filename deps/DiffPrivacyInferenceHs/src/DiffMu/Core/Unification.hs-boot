
module DiffMu.Core.Unification where

import DiffMu.Prelude
import DiffMu.Abstract
import DiffMu.Typecheck.Constraint.Definitions
import {-# SOURCE #-} DiffMu.Core.Definitions
import {-# SOURCE #-} DiffMu.Core.TC

import DiffMu.Core.Symbolic

instance (Typeable k, MonadDMTC t) => Unify (WithContext DMException) t (DMTypeOf k) where

instance Typeable k => Solve MonadDMTC IsEqual (DMTypeOf k, DMTypeOf k) where


