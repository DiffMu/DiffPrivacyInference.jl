
module DiffMu.Core.Definitions where

import DiffMu.Prelude
import {-# SOURCE #-} DiffMu.Core.Symbolic

data DMKind
type role DMTypeOf nominal
data DMTypeOf (k :: DMKind) where
data AnnotationKind
instance Show AnnotationKind
instance Show (DMTypeOf (k :: DMKind))
-- data DMException
-- data WithContext (a :: *)
-- type LocatedDMException = WithContext DMException

-- data SourceLocExt

type TVarOf = SymbolOf @DMKind
type SVarOf = SymbolOf @SensKind






