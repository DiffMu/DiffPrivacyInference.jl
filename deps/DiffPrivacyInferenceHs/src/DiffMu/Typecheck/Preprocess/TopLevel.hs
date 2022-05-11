
{-# LANGUAGE TemplateHaskell #-}

{- |
Description: Preprocessing step to deal with black boxes.

This step finds out the names of all global definitions and black boxes,
as well as making sure that black boxes are only defined on the top level,
and do not overlap in names with other global definitions.
-}
module DiffMu.Typecheck.Preprocess.TopLevel where

import DiffMu.Prelude
import DiffMu.Core
import DiffMu.Abstract.Data.Error
import DiffMu.Abstract.Class.Log
import DiffMu.Core.Logging
import DiffMu.Abstract.Data.HashMap
import DiffMu.Typecheck.Preprocess.Common

import qualified Data.HashMap.Strict as H

import qualified Data.Text as T

import Debug.Trace


data TopLevelInformation = TopLevelInformation
  {
    blackBoxNames :: H.HashMap ProcVar SourceLocExt
  , globalNames :: H.HashMap ProcVar SourceLocExt
  }


data TLFull = TLFull
  {
    _tlinfo :: TopLevelInformation
  }

instance Default TLFull where
  def = TLFull (TopLevelInformation H.empty H.empty)


$(makeLenses ''TLFull)

type TLTC = LightTC Location_PrePro_Global TLFull




instance Show TopLevelInformation where
  show (TopLevelInformation bbs gls) = "globals: " <> show gls <> "\nblack boxes: " <> show bbs <> "\n"

-- Walk through the toplevel code and get a list of all top-level definitions.
-- These are the global captures which are implicitly applied to black boxes.
--
-- Furthermore, make sure that blackbox lets (BBLet) are only on the top level,
-- (to make sure that the only captured scope is really the top-level one)
-- And that their names do not intersect with any top level name.
--
-- returns (blackbox names, global names)


--
-- since the toplevel-dmterm constructor is either
--  - Block: (contains multiple statements)
--  - something else: (to be treated as single statement)
--
-- we extract the list of statements, and call for each
-- of them the main `checkTopLevelStatement` function
--
checkTopLevel :: LocProcDMTerm -> TLTC (TopLevelInformation)
checkTopLevel (Located l term) = do
  let terms = case term of
        Extra (Block ts) -> ts
        other -> [Located l other]

  -- compute for all statements
  mapM checkTopLevelStatement terms

  -- return the accumulated tlinfo
  use tlinfo



--
-- check a single statement and update the state
-- according to above rules
--
checkTopLevelStatement :: LocProcDMTerm -> TLTC ()

-- if we have a black box
-- make sure that the name is not already taken by anything else
checkTopLevelStatement (Located l (Extra (ProcBBLet v body))) = do
  (TopLevelInformation bbvars glvars) <- use tlinfo

  case getValue v bbvars of
    Just l2 -> throwLocatedError (BlackBoxError "Black boxes are only allowed to have a single implementation.")
                 (SourceQuote
                  [(l2,"first definition of the black box " <> quote (showPretty v))
                  ,(l,"second definition of " <> quote (showPretty v) <> " attempted here ")
                  ]
                 )
    Nothing -> pure ()

  case v `getValue` glvars of
    Just l2 -> throwLocatedError (BlackBoxError "Black boxes cannot have the same name as other global definitions.")
                 (SourceQuote
                  [(l2,"global definition of " <> quote (showPretty v))
                  ,(l,"definition of black box " <> quote (showPretty v) <> " attempted here ")
                  ]
                 )
    Nothing -> pure ()

  tlinfo .= TopLevelInformation (setValue v l bbvars) (setValue v l glvars)

  return ()

-- if we have something else top level
checkTopLevelStatement (Located l (Extra (ProcSLetBase _ v body))) = do
  checkNonTopLevelBB body

  (TopLevelInformation bbvars glvars) <- use tlinfo

  case v `getValue` (bbvars) of
    Just l2 -> throwLocatedError (BlackBoxError "Global definitions cannot have the same name as black boxes.")
                 (SourceQuote
                  [(l2,"black box " <> quote (showPretty v) <> " defined here")
                  ,(l,"definition of " <> quote (showPretty v) <> " attempted here")
                  ]
                 )
    Nothing -> pure ()

  tlinfo .= TopLevelInformation bbvars (setValue v l glvars)

  return ()

checkTopLevelStatement (Located l (Extra (ProcFLet v body))) = do
  checkNonTopLevelBB body

  (TopLevelInformation bbvars glvars) <- use tlinfo

  case v `getValue` bbvars of
    Just l2 -> throwLocatedError (BlackBoxError "Global definitions cannot have the same name as black boxes.")
                 (SourceQuote
                  [(l2,"black box " <> quote (showPretty v) <> " defined here")
                  ,(l,"definition of " <> quote (showPretty v) <> " attempted here")
                  ]
                 )
    Nothing -> pure ()

  tlinfo .= TopLevelInformation bbvars (setValue v l glvars)

  return ()

checkTopLevelStatement (Located l (Extra (ProcTLetBase _ (vs) body))) = do
  checkNonTopLevelBB body

  (TopLevelInformation bbvars glvars) <- use tlinfo

  let letvars = vs

  let checkname v = case v `getValue` (bbvars) of
        Just l2 -> throwLocatedError (BlackBoxError "Global definitions cannot have the same name as black boxes.")
                 (SourceQuote
                  [(l2,"black box " <> quote (showPretty v) <> " defined here")
                  ,(l,"definition of " <> quote (showPretty v) <> " attempted here")
                  ]
                 )
        Nothing -> pure ()

  mapM checkname letvars

  tlinfo .= TopLevelInformation bbvars ((H.fromList [(v,l) | v <- letvars]) <> glvars)

  return ()

-- all other terms do nothing
checkTopLevelStatement rest = do
  return ()


-- make sure that no black box definitions are here.
checkNonTopLevelBB :: LocProcDMTerm -> TLTC LocProcDMTerm
checkNonTopLevelBB (Located l (BBLet v jt rest)) = throwLocatedError (BlackBoxError $ "Found a black box definition (" <> show v <> ") which is not in the top level scope. Black boxes can only be defined at the top level scope. " ) l
checkNonTopLevelBB term = recDMTermMSameExtension_Loc checkNonTopLevelBB term



