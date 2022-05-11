
{- |
Description: A pipeline of all preprocessing steps.

The pipeline is as follows:
 1. `checkTopLevel`
 2. `demutate`
 3. `unblock`
 4. `collectAllFLets`
 5. `processLS`
 6. `processColors`
-}
module DiffMu.Typecheck.Preprocess.All where

import DiffMu.Prelude
import DiffMu.Abstract
import DiffMu.Core
import DiffMu.Core.Logging
import DiffMu.Typecheck.Preprocess.Common
import DiffMu.Typecheck.Preprocess.TopLevel
import DiffMu.Typecheck.Preprocess.Demutation
import DiffMu.Typecheck.Preprocess.FLetReorder
import DiffMu.Typecheck.Preprocess.LexicalScoping
import DiffMu.Typecheck.Preprocess.Unblock
import DiffMu.Typecheck.Preprocess.Colors

import qualified Data.HashMap.Strict as H

import qualified Data.Text as T

import Debug.Trace

type PreProTC = LightTC Location_PreProcess ()

preprocessAll :: LocProcDMTerm -> PreProTC (LocDMTerm)
preprocessAll term = do

  -- top level processing
  (tlinfo) <- liftLightTC def def (checkTopLevel term)
  info $ "-----------------------------------"
  info $ "Toplevel information:\n" <> showT tlinfo
  info $ "term prior to preprocessing:\n" <> showPretty term

  -- -- mutation processing
  term'' <- liftLightTC (MFull def def def def def def def tlinfo) (\_ -> ()) (demutate term)
  -- term'' <- liftLightTC () (\_ -> ()) (nondemutate term')

  info $ "-----------------------------------"
  info $ "demutated term:\n" <> showPretty term''

  -- de-proceduralizing processing
  term''' <- liftLightTC () (\_ -> ()) (unblock term'')

  info $ "-----------------------------------"
  info $ "deproceduralized term:\n" <> showPretty term'''
  
  -- flet processing
  term'''' <- liftLightTC def def (collectAllFLets term''')

  info $ "-----------------------------------"
  info $ "FLet processed term:\n" <> showPretty term''''

  -- lexical scoping processing
  term''''' <- liftLightTC (LSFull def) (\_ -> ()) (processLS term'''')

  info $ "-----------------------------------"
  info $ "Lexical scoping processed term:\n" <> showPretty term'''''


  -- color processing
  term'''''' <- liftLightTC (ColorFull def SensitivityK) (\_ -> ()) (processColors term''''')

  info $ "-----------------------------------"
  info $ "Color processed term:\n" <> showPretty term''''''

  -- done
  return term''''''

