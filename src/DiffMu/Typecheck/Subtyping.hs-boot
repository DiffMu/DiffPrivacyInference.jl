
module DiffMu.Typecheck.Subtyping where

import DiffMu.Prelude
import DiffMu.Abstract
import DiffMu.Core.Definitions
import DiffMu.Core.Symbolic
import {-# SOURCE #-} DiffMu.Core.TC


instance (SingI k, Typeable k) => Solve MonadDMTC IsInfimum ((DMTypeOf k, DMTypeOf k) :=: DMTypeOf k) where
instance Typeable k => FixedVars TVarOf (IsLessEqual (DMTypeOf k, DMTypeOf k)) where
instance Typeable k => FixedVars TVarOf (IsSupremum ((DMTypeOf k, DMTypeOf k) :=: DMTypeOf k)) where
instance Typeable k => FixedVars TVarOf (IsInfimum ((DMTypeOf k, DMTypeOf k) :=: DMTypeOf k)) where


