
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TemplateHaskell #-}

{- |
Description: Julia scope implementation used by typechecker.
-}
module DiffMu.Core.Scope where

import DiffMu.Prelude
import DiffMu.Abstract
import DiffMu.Core
import DiffMu.Core.Logging
import DiffMu.Core.Symbolic
import DiffMu.Core.TC

import qualified Data.HashMap.Strict as H

import Debug.Trace


------------------------------------------------------------------------
-- the scope used by the typechecker

newtype DMScope = DMScope (H.HashMap TeVar (TC DMMain))
  deriving Generic

-- our scopes are `DictLike`
instance DictLike TeVar (TC DMMain) (DMScope) where
  setValue v m (DMScope h) = DMScope (H.insert v m h)
  deleteValue v (DMScope h) = DMScope (H.delete v h)
  getValue k (DMScope h) = h H.!? k
  emptyDict = DMScope H.empty
  isEmptyDict (DMScope h) = H.null h
  getAllKeys (DMScope h) = H.keys h

instance Default (DMScope) where
  def = DMScope H.empty


-- pushing choices (multiple dispatch function variables) is different from pushing
-- normal variables because if another method of the same function was defined
-- earlier, their types have to be collected in one type using the `:∧:` operator
pushChoice :: TeVar -> (TC DMMain) -> DMScope -> DMScope
pushChoice name ma scope =
  let oldval = getValue name scope
      newval = case oldval of
        Nothing -> ma
        Just mb -> do
          (a',b') <- msumTup (ma, mb)
          return (a' :∧: b')
  in setValue name newval scope

