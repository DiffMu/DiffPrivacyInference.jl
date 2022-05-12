
{-# LANGUAGE TemplateHaskell #-}

{- |
Description: The color inference preprocessing step.

Preprocessing step to make Lets into Bind (and add Ret if necessary)
infers the color (whether its a priv or a sens term) recursively and, upon
encountering SLet/TLet, makes them into Bind if they are supposed to be.
they are supposed to be if the term that is assigned is a privacy term.
it is then required for the tail term to be a privacy term too, which is why
the main function takes the required color as input. it inserts Ret if the term
cannot be interpreted as a privacy term otherwise.
-}
module DiffMu.Typecheck.Preprocess.Colors where

import DiffMu.Prelude
import DiffMu.Abstract
import DiffMu.Core
import DiffMu.Core.Logging
import DiffMu.Abstract.Data.Error
import DiffMu.Typecheck.Preprocess.Common

import qualified Data.Text as T
import Data.Foldable

import qualified Data.HashSet as H
 
import Debug.Trace

------------------------------------------------
-- the state for our computation:
--    functionNames = the list of privacy functions in scope
--    inferredColor = the color that was inferred
type Color = AnnotationKind

instance Default (H.HashSet TeVar) where
    def = H.empty

data ColorFull = ColorFull
  {
    _functionNames :: H.HashSet TeVar,
    _inferredColor :: Color
  }

type ColorTC = LightTC Location_PrePro_Color ColorFull

$(makeLenses ''ColorFull)

-- set current inferred color
setColor :: (MonadState ColorFull m) => Color -> m ()
setColor color = inferredColor .= color

-- get current inferred color
getColor :: (MonadState ColorFull m) => m (Color)
getColor = use inferredColor

-- push a function name to the privacy function scope
pushFunction :: (MonadState ColorFull m) => TeVar -> m ()
pushFunction name = functionNames %%= (\set -> ((), H.insert name set))

-- check if a name corresponds t a privacy function
isPFunction :: (MonadState ColorFull m) => TeVar -> m Bool
isPFunction name = functionNames %%= (\set -> (H.member name set, set))

-- push all names to the priv function scope that are annotated as privacy
-- functions in the given argument list.
pushFunctionArgs :: (MonadState ColorFull m) => [Asgmt JuliaType] -> m ()
pushFunctionArgs args = let pushArg (x :- t) = case t of
                                JTPFunction -> pushFunction x -- user annotation says its a priva function
                                _ -> pure ()
                        in do
                            mapM pushArg args
                            pure ()

-- same as above but for argument lists that have relevance annotations too
pushFunctionArgsRel :: (MonadState ColorFull m) => [Asgmt (JuliaType, Relevance)] -> m ()
pushFunctionArgsRel args = pushFunctionArgs [(x :- t) | (x :- (t,_)) <- args]


------------------------------------------------

-- the function to be called from the outside, just for the log print
processColors :: LocDMTerm -> ColorTC LocDMTerm
processColors term = do
    nterm <- handleAnyTerm_Loc term
    logForce $ "-----------------------------------"
    logForce $ "Color corrected term is:\n" <> showPretty nterm
    return nterm

-- handle a term that is required to be a sensitivity term
handleSensTerm_Loc :: LocDMTerm -> ColorTC LocDMTerm
handleSensTerm_Loc term = do
    tterm <- transformLets_Loc (Just SensitivityK) term
    cterm <- getColor
    case cterm of
        PrivacyK -> throwLocatedError (TermColorError SensitivityK (showPretty (getLocated term))) (getLocation term)
        SensitivityK -> return tterm

-- handle a term that is required to be a privacy term
handlePrivTerm_Loc :: LocDMTerm -> ColorTC LocDMTerm
handlePrivTerm_Loc term = do
    tterm <- transformLets_Loc (Just PrivacyK) term
    cterm <- getColor
    case cterm of
        PrivacyK -> return tterm
        SensitivityK -> throwLocatedError (TermColorError PrivacyK (showPretty (getLocated tterm))) (getLocation term)

-- handle a term that can be whatever
-- handleAnyTerm :: DMTerm -> ColorTC DMTerm
-- handleAnyTerm term = transformLets Nothing term

handleAnyTerm_Loc :: LocDMTerm -> ColorTC LocDMTerm
handleAnyTerm_Loc term = transformLets_Loc Nothing term

retPriv_Loc :: LocDMTerm -> ColorTC LocDMTerm
retPriv_Loc t = setColor PrivacyK >> return t

retSens_Loc :: LocDMTerm -> ColorTC LocDMTerm
retSens_Loc t = setColor SensitivityK >> return t

retRequired :: Maybe Color -> LocDMTerm -> ColorTC LocDMTerm
retRequired reqc term@(Located l _) = case reqc of
                                      Just PrivacyK -> setColor PrivacyK >> return (Located l (Ret term))
                                      _ -> setColor SensitivityK >> return term

-- main function. takes a requested color (or nothing if we don;t care), and the term to
-- transform. does three interesting things:
--    Lets are turned into Binds if the thing that is assigned is inferred to be a privacy term.
--    If so, the trailing term is requested to be a privacy term. If not, the trailing term is
--    requested to be the requested color.
--
--    All privacy functions that occur are collected in a name context. Upon application their
--    presence in the context is checked to determine the return color.
--
--    Sensitivity terms are prepended by a Ret if they are requested to be privacy terms.

transformLets_Loc :: Maybe Color -> LocDMTerm -> ColorTC LocDMTerm
transformLets_Loc = transformLets

transformLets :: Maybe Color -> LocDMTerm -> ColorTC LocDMTerm
transformLets reqc (Located l_term (term)) = do
  let retPriv x = retPriv_Loc (Located l_term (x))
  let retSens x = retSens_Loc (Located l_term (x))

  case term of

   SLetBase PureLet x body tail -> do
       tbody <- handleAnyTerm_Loc body
       cbody <- getColor
       case cbody of
            SensitivityK -> do
                ttail <- transformLets_Loc reqc tail
                return (Located l_term (SLetBase PureLet x tbody ttail))
            PrivacyK -> do
                ttail <- handlePrivTerm_Loc tail
                return (Located l_term (SLetBase BindLet x tbody ttail))

   TLetBase PureLet ns body tail -> do
       tbody <- handleAnyTerm_Loc body
       cbody <- getColor
       case cbody of
            SensitivityK -> do
                ttail <- transformLets_Loc reqc tail
                return (Located l_term (TLetBase PureLet ns tbody ttail))
            PrivacyK -> do
                ttail <- handlePrivTerm_Loc tail
                return (Located l_term (TLetBase BindLet ns tbody ttail))

--    Reorder σ t -> do
--        tt <- handleAnyTerm t
--        return (Reorder σ tt)

   Lam args ret body -> do
       pushFunctionArgsRel args
       tbody <- handleSensTerm_Loc body
       return (Located l_term (Lam args ret tbody))

   LamStar args ret body -> do
       pushFunctionArgsRel args
       fn <- use functionNames
       tbody <- handlePrivTerm_Loc body
       retSens (LamStar args ret tbody) -- while the body is a priv term, the LamStar is a sens term

   TLetBase SampleLet ns body tail -> do
       tbody <- handleSensTerm_Loc body
       ttail <- handlePrivTerm_Loc tail
       setColor PrivacyK
       return (Located l_term (TLetBase SampleLet ns tbody ttail))

   FLet name (Located l (LamStar args ret body)) tail -> do
       pushFunction name -- collect privacy function names, all other functions are assumed to be sens functions
       tf <- handleAnyTerm_Loc (Located l (LamStar args ret body))
       ttail <- handleAnyTerm_Loc tail
       return (Located l_term (FLet name tf ttail))

   FLet name (Located l (Lam args ret body)) tail -> do
       tf <- handleAnyTerm_Loc (Located l (Lam args ret body))
       ttail <- handleAnyTerm_Loc tail
       return (Located l_term (FLet name tf ttail))

   Loop (i1,i2,i3) cs (x1, x2) body -> do
       ti1 <- handleSensTerm_Loc i1
       ti2 <- handleSensTerm_Loc i2
       ti3 <- handleSensTerm_Loc i3
       tbody  <- handleAnyTerm_Loc body
       return (Located l_term (Loop (ti1,ti2,ti3) cs (x1, x2) tbody))

   Apply f xs -> do
       txs <- mapM handleSensTerm_Loc xs
       case getLocated f of
            Var fn -> do
                                    isP <- isPFunction fn
                                    case isP of
                                       True  -> retPriv (Apply f txs)
                                       False -> retSens (Apply f txs) -- f is either a sfunc arg or not in scope
            _ -> do -- there are no functions that return priv functions, so we can assume here that this is a sens function
                   tf <- handleSensTerm_Loc f
                   retSens (Apply tf txs)

   Sng _ _ -> retRequired reqc (Located l_term (term))
   Var _ -> retRequired reqc (Located l_term (term))
   Arg _ _ _ -> retRequired reqc (Located l_term (term))

   TLetBase _ _ _ _ -> throwUnlocatedError (InternalError ("Parser spit out a non-pure TLet: " <> showPretty term))
   SLetBase _ _ _ _ -> throwUnlocatedError (InternalError ("Parser spit out a non-pure SLet: " <> showPretty term))
   FLet _ _ _ -> throwUnlocatedError (InternalError ("Parser spit out an FLet that has no lambda in its definition: " <> showPretty term))
   Ret _ -> throwUnlocatedError (InternalError ("Parser spit out a return term: " <> showPretty term))

   _ -> case reqc of
             Just PrivacyK -> do
                                   tterm <- recDMTermMSameExtension_Loc handleAnyTerm_Loc (Located l_term term)
                                   case term of
                                       Gauss _ _ _ _        -> retPriv_Loc tterm
                                       MutGauss _ _ _ _     -> retPriv_Loc tterm
                                       Laplace _ _ _        -> retPriv_Loc tterm
                                       MutLaplace _ _ _     -> retPriv_Loc tterm
                                       AboveThresh _ _ _ _  -> retPriv_Loc tterm
                                       Exponential _ _ _ _  -> retPriv_Loc tterm
                                       PReduceCols _ _      -> retPriv_Loc tterm
                                       PFoldRows _ _ _ _    -> retPriv_Loc tterm
                                       _                    -> retPriv_Loc (Located l_term (Ret (tterm)))
             _ -> do
                             tterm <- recDMTermMSameExtension_Loc handleSensTerm_Loc (Located l_term term)
                             case term of
                                 Gauss _ _ _ _        -> retPriv_Loc tterm
                                 MutGauss _ _ _ _     -> retPriv_Loc tterm
                                 Laplace _ _ _        -> retPriv_Loc tterm
                                 MutLaplace _ _ _     -> retPriv_Loc tterm
                                 AboveThresh _ _ _ _  -> retPriv_Loc tterm
                                 Exponential _ _ _ _  -> retPriv_Loc tterm
                                 PReduceCols _ _      -> retPriv_Loc tterm
                                 PFoldRows _ _ _ _    -> retPriv_Loc tterm
                                 _                    -> retSens_Loc tterm

