
{- |
Description: This file contains the solving code for constraints where said code is not very complex.
-}
module DiffMu.Typecheck.Constraint.CheapConstraints where

import DiffMu.Prelude
import DiffMu.Abstract
import DiffMu.Abstract.Data.Permutation
import DiffMu.Core.Definitions
import DiffMu.Core.Logging
import DiffMu.Core.Context
import DiffMu.Core.TC
import DiffMu.Core.Symbolic
import DiffMu.Core.Unification
import DiffMu.Typecheck.Subtyping
import DiffMu.Typecheck.JuliaType
import DiffMu.Typecheck.Constraint.Definitions
import Algebra.PartialOrd

import Debug.Trace

import qualified Data.HashSet as HS
import qualified Data.HashMap.Strict as H
import Data.HashMap.Strict (HashMap)
import qualified Data.POSet as PO
import Data.POSet (POSet)

import Debug.Trace
import qualified Data.HashMap.Strict as H
import qualified Prelude as P

default (Text)


-------------------------------------------------------------------
-- set the a type to a variable const, in case it's numeric or a tuple.
--

instance Solve MonadDMTC MakeConst (DMMain, Text) where
  solve_ Dict _ name (MakeConst (τ,username)) = case τ of
      TVar _ -> pure ()
      NoFun (TVar _) -> pure ()
      NoFun (DMTup ts) -> (mapM (\t -> (addConstraintFromName name) (Solvable (MakeConst (NoFun t, username)))) ts) >> dischargeConstraint name
      NoFun (Numeric k) -> do
                     cv <- newVar 
                     ck <- newSVarWithPriority UserNamePriority username
                     debug $ "While making const: priority of " <> showT ck <> " is: " <> showT (varPriority ck)
                     unifyFromName name (k) (Num cv (Const (svar ck)))
                     dischargeConstraint name
      _ -> dischargeConstraint name 


----------------------------------------------------------
-- replacing all Numeric TVars by non-const

instance Typeable k => Solve MonadDMTC MakeNonConst (DMTypeOf k, SolvingMode) where
  solve_ Dict currentMode name (MakeNonConst (τ, targetMode)) | currentMode == targetMode = do
     let freev = freeVars @_ @TVarOf τ
         freev0 = filterSomeK @TVarOf @BaseNumKind freev
         freev1 = filterSomeK @TVarOf @NormKind freev
         freev2 = filterSomeK @TVarOf @ClipKind freev
         freev3 = filterSomeK @TVarOf @NumKind freev
         freev4 = filterSomeK @TVarOf @ConstnessKind freev

     let makeVarNonConst v = do
                     τv <- newVar
                     unifyFromName name (TVar v) (Num τv NonConst)

     mapM makeVarNonConst freev3

     let makeCVarNonConst v = do unifyFromName name (TVar v) (NonConst)
     mapM makeCVarNonConst freev4

     dischargeConstraint name

  solve_ Dict currentMode name (MakeNonConst (τ, targetMode)) | otherwise = pure ()


-------------------------------------------------------------------
-- is it Loop or static Loop (i.e. is no of iterations const or not)

instance Solve MonadDMTC IsLoopResult ((Sensitivity, Sensitivity, Sensitivity), Annotation SensitivityK, (DMMain, DMMain, DMMain)) where
  solve_ Dict _ name (IsLoopResult ((s1, s2, s3), sa, (i1,i2,i3))) = do
     let SensitivityAnnotation s = sa
     let isConst :: DMMain -> Maybe (Either Sensitivity ())
         isConst t = case t of
                          (NoFun (Numeric (Num _ (Const n)))) -> Just (Left n)
                          (NoFun (Numeric (Num _ NonConst))) -> Just (Right ())
                          _ -> Nothing
     msg <- inheritanceMessageFromName name
     case (isConst i1,isConst i2,isConst i3) of
          (Just (Left start), Just (Left step), Just (Left end)) -> do -- all operands are const, so number of iterations is const too
             let η = ceil (divide ((minus end start) ⋆! oneId) step) -- compute number of iterations
             addConstraint (Solvable (IsLessEqual (start, end))) (msg :\\: "Start value of iterator must be <= end value of iterator.")
             unifyFromName name s1 zeroId -- iteration variable context scales with 0
             unifyFromName name s2 (exp s η)
             unifyFromName name s3 η
             dischargeConstraint name
          (Just _, Just _, Just _) -> do -- some operands are non-const
             unify (msg :\\: "The loop has variable number of iterations, so the sensitivity of all captured variables in the loop body must be 1.") s oneId
             unifyFromName name s1 inftyS -- iteration variable context scales with inf (dffers from paper but is true)
             unifyFromName name s2 oneId
             unifyFromName name s3 inftyS
             dischargeConstraint name
          _ -> pure ()


--------------------------------------------------
-- is it gauss or mgauss?
--

instance Solve MonadDMTC IsAdditiveNoiseResult (DMTypeOf MainKind, DMTypeOf MainKind) where
  solve_ Dict _ name (IsAdditiveNoiseResult (τgauss, τin)) =
     case τin of
        TVar x -> pure () -- we don't know yet.
        NoFun (TVar x) -> pure () -- we don't know yet.
        NoFun (DMContainer k nrm clp n τ) -> do -- is mgauss

           logForce $ ">>>>>>>>>>>>>>>>>>>>>>>>\nIn gauss, type is " <> showT (DMGrads nrm clp n τ) <> "<<<<<<<<<<<<<<<<<<<<<"

           iclp <- newVar -- clip of input matrix can be anything
           τv <- newVar -- input matrix element type can be anything (as long as it's numeric)

           -- set in- and output types as given in the mgauss rule
           -- input type gets a LessEqual so we can put Integer or Real (but not Data)
           addConstraintFromName name (Solvable(IsLessEqual(τin, (NoFun (DMContainer k L2 iclp n (NoFun (Numeric (Num (IRNum DMReal) τv))))))))
           unifyFromName name τgauss (NoFun (DMContainer k LInf U n (NoFun (Numeric (Num (IRNum DMReal) NonConst)))))

           dischargeConstraint @MonadDMTC name
        _ -> do -- regular gauss or unification errpr later
           τ <- newVar -- input type can be anything (as long as it's numeric)

           -- set in- and output types as given in the gauss rule
           addConstraintFromName name (Solvable(IsLessEqual(τin, (NoFun (Numeric (Num (IRNum DMReal) τ))))))
           unifyFromName name τgauss (NoFun (Numeric (Num (IRNum DMReal) NonConst)))

           dischargeConstraint @MonadDMTC name


--------------------------------------------------
-- projecting of tuples

instance Solve MonadDMTC IsTProject ((Int, DMTypeOf MainKind) :=: DMTypeOf MainKind) where
  solve_ Dict _ name (IsTProject ((i , ρs) :=: ρ)) = f ρs
    where
      f :: MonadDMTC t => DMTypeOf MainKind -> t ()
      f (TVar _) = pure ()
      f (a :∧: b) = unifyFromName name a b >> pure () -- since we know that the lhs is going to be a tuple (and thus NoFun) eventually, we can merge the values
      f (NoFun (TVar _)) = pure ()
      f (NoFun (DMTup ρs)) = do
        let ρ' = ρs ^? element i
        case ρ' of
          Just ρ' -> do
            unifyFromName name ρ (NoFun ρ')
            dischargeConstraint name
            pure ()
          Nothing -> internalError $ "tuple index out of range\nwhere index: " <> showPretty i <> ",tuple type: " <> showPretty ρs
      f (τs) = throwUnlocatedError (TypeMismatchError $ "Expected the type " <> showT ρs <> " to be a tuple type.")


--------------------------------------------------
-- black boxes

instance Solve MonadDMTC IsBlackBox (DMMain, [DMMain]) where
  solve_ Dict _ name (IsBlackBox (box, args)) =
     case box of
        TVar x -> pure () -- we don't know yet.
        BlackBox jts -> do -- its a box!
           case length jts == length args of
                True -> let setArg :: IsT MonadDMTC t => (JuliaType, DMMain) -> t ()
                            setArg (jt, arg) = addJuliaSubtypeConstraint arg jt ("Black box argument user type annotation.")
                        in do
                            mapM setArg (zip jts args)
                            dischargeConstraint @MonadDMTC name
                False -> throwUnlocatedError (NoChoiceFoundError "Wrong number of arguments for black box call.")
        _ -> impossible $ "Box Apply used with non-box!"



instance Solve MonadDMTC IsBlackBoxReturn (DMMain, Sensitivity) where
    solve_ Dict _ name (IsBlackBoxReturn (argt, args)) = do
     let discharge s = do
                          unifyFromName name args s
                          dischargeConstraint @MonadDMTC name
     case argt of
          TVar _ -> pure ()
          NoFun (TVar _) -> pure ()
          NoFun (DMContainer _ _ _ _ (TVar _)) -> pure ()
          NoFun (DMContainer _ _ _ _ (NoFun (TVar _))) -> pure ()
          NoFun (DMContainer _ _ _ _ (NoFun (Numeric targ))) -> do
              unifyFromName name targ (Num DMData NonConst)
              discharge oneId
          _ -> discharge inftyS


--------------------------------------------------
-- IsLess for sensitivities

instance Solve MonadDMTC IsLess (Sensitivity, Sensitivity) where
  solve_ Dict _ name (IsLess (s1, s2)) = solveLessSensitivity s1 s2
    where
      getVal :: Sensitivity -> Maybe SymVal
      getVal a@(SingleKinded (LinCom (MonCom as))) = case H.toList as of
         [(MonCom aterm, av)] -> case H.toList aterm of
                                      [] -> (Just av)
                                      _ -> Nothing
         [] -> (Just zeroId)
         _ -> Nothing
      solveLessSensitivity :: IsT MonadDMTC t => Sensitivity -> Sensitivity -> t ()
      solveLessSensitivity a b = case getVal a of
         Just av -> case getVal b of
                         Just bv -> case av == Infty of
                                         True -> do
                                           (b ==! constCoeff Infty) name
                                           dischargeConstraint name
                                         False -> case (av < bv) of
                                                       True -> dischargeConstraint name
                                                       False -> failConstraint name
                         Nothing -> return ()
         Nothing -> return ()



--------------------------------------------------
-- matrix or vector

instance Solve MonadDMTC IsVecOrMat (VecKind, Sensitivity) where
    solve_ Dict _ name (IsVecOrMat (k, s)) =
     case k of
        TVar _ -> pure ()
        Vector -> unifyFromName name oneId s >> dischargeConstraint name
        Matrix r -> unifyFromName name r s >> dischargeConstraint name
        _ -> failConstraint name

--------------------------------------------------
-- gradient or vector or 1d-matrix
--

instance Solve MonadDMTC IsVecLike VecKind where
    solve_ Dict _ name (IsVecLike k) =
     case k of
        TVar _ -> pure ()
        Vector -> dischargeConstraint name
        Gradient -> dischargeConstraint name
        Matrix r -> unifyFromName name r oneId >> dischargeConstraint name

--------------------------------------------------
-- container norm conversion
--

instance Solve MonadDMTC ConversionResult (DMTypeOf NormKind, DMTypeOf NormKind, Sensitivity, Sensitivity) where
    solve_ Dict _ name (ConversionResult (nrm_in, nrm_out, n, s)) =
     case (nrm_in, nrm_out) of
        (L1,_)      -> unify ("Setting container norm conversion penalty to 1.") s oneId >> dischargeConstraint name
        (L2,L2)     -> unify ("Setting container norm conversion penalty to 1.") s oneId >> dischargeConstraint name
        (LInf,LInf) -> unify ("Setting container norm conversion penalty to 1.") s oneId >> dischargeConstraint name
        (L2,L1)     -> unify ("Setting container norm conversion penalty to sqrt(n_rows).") s (sqrt n) >> dischargeConstraint name
        (L2,LInf)   -> unify ("Setting container norm conversion penalty to sqrt(n_rows).") s (sqrt n) >> dischargeConstraint name
        (LInf,L1)   -> unify ("Setting container norm conversion penalty to sqrt(n_rows).") s (sqrt n) >> dischargeConstraint name
        (LInf,L2)   -> unify ("Setting container norm conversion penalty to sqrt(n_rows).") s (sqrt n) >> dischargeConstraint name
        _           -> pure ()

