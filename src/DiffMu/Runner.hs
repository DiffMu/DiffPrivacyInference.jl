
{- |
Description: Executing the preprocessing and typechecking pipeline.

This is the top level code which describes how a user input (a string passed to us from the julia runtime),
is fed into the preprocessing - typechecking - constraint solving pipeline. And furthermore how the resulting
output (logging, error messages) are presented to the user.
-}
module DiffMu.Runner where

import DiffMu.Prelude
import DiffMu.Abstract
import DiffMu.Core
import DiffMu.Core.TC
import DiffMu.Core.Definitions
import DiffMu.Core.Symbolic
import DiffMu.Core.Context
import DiffMu.Core.Logging
import DiffMu.Core.Scope
import DiffMu.Typecheck.Operations
import DiffMu.Typecheck.Subtyping
import DiffMu.Typecheck.Typecheck
import DiffMu.Typecheck.Preprocess.Common
import DiffMu.Typecheck.Preprocess.All
import DiffMu.Parser.FromString
import DiffMu.Parser.JExprToDMTerm

import DiffMu.Typecheck.JuliaType

import Algebra.PartialOrd

import           Foreign.C.String

import Debug.Trace
import qualified Data.Text as T
import qualified Data.Text.IO as TIO

run :: IO ()
run = putStrLn "Hello?"


typecheckFromString_DMTerm_Debug :: String -> String -> IO ()
typecheckFromString_DMTerm_Debug term rawsource = do
 let (res) = parseJTreeFromString term >>= parseJExprFromJTree
 case (res) of
   Left err -> putStrLn $ "Error while parsing DMTerm from string: " <> show err
   Right (term,files) -> do
     rs <- (rawSourceFromString rawsource files)
     typecheckFromJExpr_Debug term rs

typecheckFromString_DMTerm_Simple :: ShouldPrintConstraintHistory -> String -> String -> IO ()
typecheckFromString_DMTerm_Simple bHistory term rawsource = do
 let res = parseJTreeFromString term >>= parseJExprFromJTree
 case res of
   Left err -> putStrLn $ "Error while parsing DMTerm from string: " <> show err
   Right (term,files) -> do
     rs <- (rawSourceFromString rawsource files)
     typecheckFromJExpr_Simple bHistory term rs

data DoShowLog = DoShowLog DMLogSeverity [DMLogLocation] | DontShowLog

executeTC l r rawsource = do
  let (x,logs) = runWriter (runReaderT (runExceptT ((runStateT ((runTCT r)) (Full def def (Right def))))) rawsource)

  case l of
    (DoShowLog s ls) -> do
        -- we do log a message if
        -- 1. its severity is higher/equal than this one
        --   OR
        -- 2. it was logged below one of the given locations
        let severity = s
        let locations = ls
        let realLogs = getLogMessages logs severity locations
        putStrLn "======================== LOG ========================="
        putStrLn realLogs
        putStrLn "======================== End LOG ====================="

    (DontShowLog) -> return ()

  let (errs,res) = case (getErrors logs, x) of
                    (errs, Left err) -> (err:errs, Nothing)
                    (errs, Right res) -> (errs, Just res)

  case errs of
       [] -> pure ()
       _ -> do
              putStrLn "======================== Errors ====================="
              TIO.putStrLn (getErrorMessage rawsource errs)
              putStrLn "======================== End Errors ====================="

  return (errs,res)

typecheckFromJExprWithPrinter :: ((DMMain,Full (DMPersistentMessage TC)) -> Text) -> DoShowLog -> JExpr -> RawSource -> IO ()
typecheckFromJExprWithPrinter printer logoptions term rawsource = do
  let r = do

        log $ "Checking term   : " <> showT term

        term' <- parseDMTermFromJExpr term >>= (liftNewLightTC . preprocessAll)

        tres' <- checkSens def (term')

        tres''' <- solveAndNormalize ExactNormalization [SolveSpecial,SolveExact,SolveGlobal,SolveAssumeWorst,SolveFinal] tres'
        tres'''' <- solveAndNormalize SimplifyingNormalization [SolveSpecial,SolveExact,SolveGlobal,SolveAssumeWorst,SolveFinal] tres'''
        return tres''''

  x <- executeTC logoptions r rawsource

  case x of
    (_, Nothing) -> putStrLn $ "No type could be inferred"
    (_, Just x) -> TIO.putStrLn $ printer x


data ShouldPrintConstraintHistory = PrintConstraintHistory | DontPrintConstraintHistory

typecheckFromJExpr_Simple :: ShouldPrintConstraintHistory -> JExpr -> RawSource -> IO ()
typecheckFromJExpr_Simple bHistory term rawsource = do
  let printer (ty, full) =
        let cs = _topctx (_anncontent (_constraints (_meta full)))
            cs_simple :: Ctx IxSymbol (Watched (Solvable GoodConstraint GoodConstraintContent MonadDMTC)) = fmap (\(ConstraintWithMessage a m) -> a) cs

            pcs = case bHistory of
              PrintConstraintHistory     -> runReader (showLocated cs) rawsource
              DontPrintConstraintHistory -> runReader (showLocated cs_simple) rawsource

            cstring = case isEmptyDict cs of
                           True -> ""
                           _ -> "Constraints:\n" <> pcs
            fcs = (_failedConstraints (_meta full))
            pfcs = runReader (showLocated fcs) rawsource
            fcstring = case isEmptyDict fcs of
                           True -> ""
                           _ -> red "CHECKING FAILED" <> ": The following constraints are not satisfiable:\n"
                                <> pfcs
        in do
           "\n---------------------------------------------------------------------------\n"
           <> "Type:\n" <> runReader (showLocated ty) rawsource
           <> "\n" <> (showPretty (_userVars (_meta full)))
           <> "\n---------------------------------------------------------------------------\n"
           <> showSpecialWarnings ty <> "\n"
           <> cstring <> "\n"
           <> fcstring
  typecheckFromJExprWithPrinter printer (DontShowLog) term rawsource

typecheckFromJExpr_Debug :: JExpr -> RawSource -> IO ()
typecheckFromJExpr_Debug term rawsource = do

  let logging_locations = [
        -- Location_Check,
        Location_Constraint,
        Location_PrePro_Demutation,
        Location_PreProcess,
        -- Location_Subst
        -- Location_INC,
        Location_MonadicGraph
         --Location_All
        ]
  let printer (ty, full) =
        "\n---------------------------------------------------------------------------\n"
        <> "Type:\n" <> runReader (showLocated ty) rawsource
        <> "\n---------------------------------------------------------------------------\n"
        <> showSpecialWarnings ty <> "\n"
        <> "Monad state:\n" <> (showT full)

  typecheckFromJExprWithPrinter printer (DoShowLog Debug logging_locations) term rawsource


--------------------------------------------------------------------------------------------------
-- special warnings
showSpecialWarnings :: DMMain -> Text
showSpecialWarnings ty =
  let warns = checkSpecialWarnings ty
  in intercalateS "\n" (fmap (\tx -> yellow "WARNING" <> ":\n" <> indent tx) warns)

checkSpecialWarnings :: DMMain -> [Text]
checkSpecialWarnings ty = checkClipping
  where
    checkClipping = case ty of
      Fun xs ->
        let checkArg :: DMTypeOf MainKind -> [Text]
            checkArg arg@(NoFun (DMContainer dto' dto2 clip_parameter sk dto4)) | clip_parameter /= U =
               [ "The typechecked function has an input argument of type " <> quote (showPretty arg) <> ".\n" <>
                 "(Note the clipping parameter " <> showPretty clip_parameter <> ".)\n" <>
                 "This says that the input is required to be clipped wrt the norm " <> showPretty clip_parameter <> ",\n" <>
                 "where \"clipped\" means that each row must have an " <> showPretty clip_parameter <> "-norm that is less or equal than 1." <> "\n" <>
                 "\n" <>
                 "If your data is not clipped, you have to call `clip` in your code. Then the inferred type will be " <> quote (showPretty (NoFun (DMContainer dto' dto2 U sk dto4))) <> "."
               ]
            checkArg _ = []

            checkSingleFun :: DMTypeOf FunKind -> [Text]
            checkSingleFun = \case
              DMAny -> []
              TVar so -> []
              (:->:) xs dto  -> checkArg =<< (fstAnn <$> xs)
              (:->*:) xs dto -> checkArg =<< (fstAnn <$> xs)
        in checkSingleFun =<< (fstAnn <$> xs)
      _ -> []


