
{-# LANGUAGE UndecidableInstances #-}

module DiffMu.Core.TC where

import DiffMu.Prelude
import DiffMu.Abstract
import DiffMu.Core.Symbolic
import DiffMu.Core.Logging
import {-# SOURCE #-} DiffMu.Core.Definitions
import {-# SOURCE #-} DiffMu.Abstract.Data.Error


-- type role Full nominal
data Full (t :: *)


class (FreeVars TVarOf x, Substitute TVarOf DMTypeOf x) => GoodConstraintContent (x :: *) where
instance (FreeVars TVarOf x, Substitute TVarOf DMTypeOf x) => GoodConstraintContent x where

class GoodConstraint (x :: *) where
instance GoodConstraint x where

class LiftTC (t :: * -> *)

class (MonadImpossible (t), MonadWatch (t), MonadLog t,
       MonadTerm DMTypeOf (t),
       MonadTerm SymTerm (t),
       MonadState (Full (DMPersistentMessage t)) (t),
       MonadWriter (DMMessages t) (t),
       MonadDMError (WithContext DMException) (t),
       MonadInternalError t,
       MonadUnificationError t,
       -- MonadConstraint' Symbol (TC) (t),
       -- MonadConstraint Symbol (MonadDMTC) (t),
       MonadConstraint (MonadDMTC) (t),
       MonadNormalize t,
       ContentConstraintOnSolvable t ~ GoodConstraintContent,
       ConstraintOnSolvable t ~ GoodConstraint,
       LiftTC t
      ) => MonadDMTC (t :: * -> *) where

