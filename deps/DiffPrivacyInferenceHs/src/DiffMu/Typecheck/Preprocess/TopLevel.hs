
{-# LANGUAGE TemplateHaskell #-}

module DiffMu.Typecheck.Preprocess.TopLevel where

import DiffMu.Prelude
import DiffMu.Core
import DiffMu.Abstract.Data.Error
import DiffMu.Abstract.Class.Log
import DiffMu.Core.Logging
import DiffMu.Typecheck.Preprocess.Common

import qualified Data.HashMap.Strict as H

import qualified Data.Text as T

import Debug.Trace


data TopLevelInformation = TopLevelInformation
  {
    blackBoxNames :: [ProcVar]
  , globalNames :: [ProcVar]
  }


data TLFull = TLFull
  {
    _tlinfo :: TopLevelInformation
  }

instance Default TLFull where
  def = TLFull (TopLevelInformation def def)


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
  mapM checkTopLevelStatement_Loc terms

  -- return the accumulated tlinfo
  use tlinfo



--
-- check a single statement and update the state
-- according to above rules
--
checkTopLevelStatement_Loc :: LocProcDMTerm -> TLTC ()
checkTopLevelStatement_Loc = checkTopLevelStatement . getLocated

checkTopLevelStatement :: ProcDMTerm -> TLTC ()

-- if we have a black box
-- make sure that the name is not already taken by anything else
checkTopLevelStatement (Extra (ProcBBLet v body)) = do
  (TopLevelInformation bbvars glvars) <- use tlinfo

  case v `elem` bbvars of
    True -> throwUnlocatedError (BlackBoxError $ "Found multiple black boxes definitions for the name " <> show v <> ". Black boxes are only allowed to have a single implementation.")
    False -> pure ()

  case v `elem` glvars of
    True -> throwUnlocatedError (BlackBoxError $ "Found a global definition for the name " <> show v <> ". This is not allowed since there already is a black box with that name.")
    False -> pure ()

  tlinfo .= TopLevelInformation (v : bbvars) (v : glvars)

  return ()

-- if we have something else top level
checkTopLevelStatement (Extra (ProcSLetBase _ v body)) = do
  checkNonTopLevelBB body

  (TopLevelInformation bbvars glvars) <- use tlinfo

  case v `elem` (bbvars) of
    True -> throwUnlocatedError (BlackBoxError $ "Found a black box definition for the name " <> show v <> ". This is not allowed since there already is a global variable with that name.")
    False -> pure ()

  tlinfo .= TopLevelInformation bbvars (v : glvars)

  return ()

checkTopLevelStatement (Extra (ProcFLet v body)) = do
  checkNonTopLevelBB body

  (TopLevelInformation bbvars glvars) <- use tlinfo

  case v `elem` bbvars of
    True -> throwUnlocatedError (BlackBoxError $ "Found a black box definition for the name " <> show v <> ". This is not allowed since there already is a global variable with that name.")
    False -> pure ()

  tlinfo .= TopLevelInformation bbvars (v : glvars)

  return ()

checkTopLevelStatement (Extra (ProcTLetBase _ (vs) body)) = do
  checkNonTopLevelBB body

  (TopLevelInformation bbvars glvars) <- use tlinfo

  let letvars = vs

  let checkname v = case v `elem` (bbvars) of
        True -> throwUnlocatedError (BlackBoxError $ "Found a black box definition for the name " <> show v <> ". This is not allowed since there already is a global variable with that name.")
        False -> pure ()

  mapM checkname letvars

  tlinfo .= TopLevelInformation bbvars (letvars <> glvars) 

  return ()

-- all other terms do nothing
checkTopLevelStatement rest = do
  return ()


-- make sure that no black box definitions are here.
checkNonTopLevelBB :: LocProcDMTerm -> TLTC LocProcDMTerm 
checkNonTopLevelBB (Located l (BBLet v jt rest)) = throwUnlocatedError (BlackBoxError $ "Found a black box definition (" <> show v <> ") which is not in the top level scope. Black boxes can only be defined at the top level scope. " )
checkNonTopLevelBB term = recDMTermMSameExtension_Loc checkNonTopLevelBB term



