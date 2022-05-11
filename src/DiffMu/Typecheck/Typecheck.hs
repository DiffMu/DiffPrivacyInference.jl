
{- |
Description: The typechecking algorithm, defined inductively on `DMTerm`s.
-}
module DiffMu.Typecheck.Typecheck where

import DiffMu.Prelude
import DiffMu.Abstract
import DiffMu.Core
import DiffMu.Core.Logging
import DiffMu.Core.Symbolic
import DiffMu.Core.TC
import DiffMu.Core.Unification
import DiffMu.Typecheck.Operations
import DiffMu.Core.Scope
import DiffMu.Abstract.Data.Permutation
import DiffMu.Typecheck.JuliaType
import DiffMu.Typecheck.Constraint.Definitions
import DiffMu.Typecheck.Constraint.IsFunctionArgument
import DiffMu.Typecheck.Constraint.IsJuliaEqual
import DiffMu.Typecheck.Constraint.CheapConstraints

import qualified Data.HashMap.Strict as H

import qualified Data.Text as T

import Debug.Trace

import Data.IORef
import System.IO.Unsafe
import DiffMu.Abstract.Data.Error

default (Text)


catchNoncriticalError :: LocDMTerm -> TC DMMain -> TC DMMain
catchNoncriticalError a x = do
  catchAndPersist x $ \msg -> do
    resultType <- newVar
    let msg' = ("While checking the term" :\\->: a) :\\:
                 getLocation a
                :-----:
                ("Since the checking was not successful, created the following type for this term:" :: Text) :\\:
                resultType
                :-----:
                msg
    return (resultType, msg')

------------------------------------------------------------------------
-- The typechecking function
checkPriv :: DMScope -> LocDMTerm -> TC DMMain
checkPriv scope t = do

  -- The computation to do before checking
  γ <- use types
  case γ of -- TODO prettify.
      Left (Ctx (MonCom c)) | H.null c -> return ()
      Right (Ctx (MonCom c)) | H.null c -> return ()
      ctx   -> impossible $ "Input context for checking must be empty. But I got:\n" <> showT ctx
  types .= Right def -- cast to privacy context.

  -- The checking itself
  res <- catchNoncriticalError t (withLogLocation "Check" $ checkPri' scope t)

  -- The computation to do after checking
  γ <- use types
  case γ of
      Right γ -> return res
      Left γ -> error $ "checkPriv returned a sensitivity context!\n" <> "It is:\n" <> show γ <> "\nThe input term was:\n" <> show t




checkSens :: DMScope -> LocDMTerm -> TC DMMain
checkSens scope t = do
  -- The computation to do before checking
  γ <- use types
  case γ of -- TODO prettify.
      Left (Ctx (MonCom c)) | H.null c -> return ()
      Right (Ctx (MonCom c)) | H.null c -> return ()
      ctx   -> impossible $ "Input context for checking must be empty. But I got:\n" <> showT ctx <> "\nThe term is:\n" <> showPretty t
  types .= Left def -- cast to sensitivity context.


  -- get the delayed value of the sensititivty checking
  res <- catchNoncriticalError t (withLogLocation "Check" $ checkSen' scope t)

  -- The computation to do after checking
  γ <- use types
  case γ of
      Left γ -> return res
      Right γ -> error $ "checkSens returned a privacy context!\n" <> "It is:\n" <> show γ <> "\nThe input term was:\n" <> show t


--------------------
-- Sensitivity terms


checkSen' :: DMScope -> LocDMTerm -> TC DMMain

checkSen' scope (Located l (DMTrue)) = return (NoFun DMBool)
checkSen' scope (Located l (DMFalse)) = return (NoFun DMBool)


-- TODO: Here we assume that η really has type τ, and do not check it. Should maybe do that.
checkSen' scope (Located l (Sng η τ)) = case η < 0 of
    True -> NoFun <$> Numeric <$> (Num <$> (createDMTypeBaseNum τ) <*> pure NonConst) -- we don't allow negative const
    False -> NoFun <$> Numeric <$> (Num <$> (createDMTypeBaseNum τ) <*> pure (Const (constCoeff (Fin η)))) -- we don't allow negative const

    
-- typechecking an op
checkSen' scope (Located l (Op op args)) = do
  -- create a new typeop constraint for op
  -- res is resulting type of the operation when used on types in arg_sens
  -- arg_sens :: [(SMType, Sensitivity)]
  -- types are to be unified with the actual types of the args
  -- Sensitivities are scalars for the argument's context
  (res, arg_sens) <- makeTypeOp op (length args)
                      (DMPersistentMessage $ "Constraint on the builtin call:" :\\: (Op op args))

  -- typecheck, make the appropriate unification and scaling, then sum the contexts.
  let handleOpArg (t_arg, (τ, s)) = do
                                  τ_arg <- checkSens scope t_arg
                                  unify (l :\\: "Operands of " :<>: op) (NoFun τ) τ_arg
                                  mscale (svar s)
                                  return τ_arg
                                  
  msumS (map handleOpArg (zip args arg_sens))
  
  -- return the `res` type given by `makeTypeOp`
  return (NoFun res)


-- a special term for function argument variables.
-- those get sensitivity 1, all other variables are var terms
checkSen' scope (Located l (Arg x jτ i)) = do
  τs <- newVar
  logForce $ "checking arg:" <> showPretty (x :- jτ) <> ", dmtype is " <> showPretty τs
  -- the inferred type must be a subtype of the user annotation, if given.
  addJuliaSubtypeConstraint τs jτ (l :\\: "Function argument " :<>: x :<>: " user type annotation.")

  -- put the variable in the Γ context with sensitivity 1
  setVarS x (WithRelev i (τs :@ SensitivityAnnotation oneId))
  return τs


checkSen' scope (Located l (Var x)) =  -- get the term that corresponds to this variable from the scope dict
   let mτ = getValue x scope
   in case mτ of
     Nothing -> debug ("[Var-Sens] Scope is:\n" <> showT (getAllKeys scope)) >> throwUnlocatedError (VariableNotInScope x)
     Just jτ -> do
                     debug ("[Var-Sens] Scope is:\n" <> showT (getAllKeys scope))
                     jτ


checkSen' scope (Located l (Lam xτs retτ body)) = do

    -- put a special term to mark x as a function argument. those get special treatment
    -- because we're interested in their privacy. put the relevance given in the function signature, too.
    let f s sc (x :- (τ, rel)) = setValue x (checkSens s (Located (RelatedLoc "argument of this function" l) (Arg x τ rel))) sc
    let addArgs s = foldl (f s) s xτs
    let scope' = addArgs scope

    -- check the body in the modified scope
    btype <- checkSens scope' body

    -- make sure the return/body type is subtype of the given julia type
    addJuliaSubtypeConstraint btype retτ (l :\\: "The inferred return type of the function " :<>: btype :\\: "is subtype of the annotated return type " :<>: retτ)

    -- extract julia signature
    let sign = (fst <$> sndA <$> xτs)

    -- get inferred types and sensitivities for the arguments
    xrτs <- getArgList @_ @SensitivityK [(x :- τ) | (x :- (τ, _)) <- xτs]
    let xrτs' = [x :@ s | (x :@ SensitivityAnnotation s) <- xrτs]
    logForce $ "Checking Lam, outer scope: " <> showT (getAllKeys scope) <> " | inner: " <> showT (getAllKeys scope')

    -- add constraints for making non-const if not resolvable
    let addC :: (DMMain :@ b, Asgmt (a, Relevance)) -> TCT Identity ()
        addC ((τ :@ _), x :- (_, i)) = case i of
                     IsRelevant -> do
                         addConstraint (Solvable (MakeNonConst (τ, SolveAssumeWorst)))
                           (l :\\: "Lam argument " :<>: x :<>: "can become NonConst.")
                         pure ()
                     NotRelevant -> do
                                      addConstraint (Solvable (MakeConst (τ, (showPretty x))))
                                        (l :\\: "Static Lam argument " :<>: x :<>: " can become Const.")
                                      return ()
    mapM addC (zip xrτs xτs)
    
    -- make an arrow type.
    let τ = (xrτs' :->: btype)
    return (Fun [τ :@ (Just sign)])


checkSen' scope (Located l (LamStar xτs retτ body)) = do
    -- put a special term to mark x as a function argument. those get special treatment
    -- because we're interested in their sensitivity
    let f s sc (x :- (τ , rel)) = setValue x (checkSens s (Located (RelatedLoc "argument of this function" l) (Arg x τ rel))) sc
    let addArgs s = foldl (f s) s xτs
    let scope' = addArgs scope

    -- check the body in the modified scope
    btype <- checkPriv scope' body

    -- make sure the return/body type is subtype of the given julia type
    addJuliaSubtypeConstraint btype retτ (l :\\: "The inferred return type of the function " :<>: btype :\\: "is subtype of the annotated return type " :<>: retτ)

    -- extract julia signature
    let sign = (fst <$> sndA <$> xτs)

    -- get inferred types and privacies for the arguments
    xrτs <- getArgList @_ @PrivacyK [(x :- τ) | (x :- (τ, _)) <- xτs]

    -- variables that are annotated irrelevant can be made const in case they are
    -- numeric or tuples. that way we can express the result sensitivity/privacy
    -- in terms of the nonrelevant input variables
    let addC :: (DMMain :@ b, Asgmt (a, Relevance)) -> TCT Identity ()
        addC ((τ :@ _), x :- (_, i)) = case i of
                     IsRelevant -> do
                         addConstraint (Solvable (MakeNonConst (τ, SolveAssumeWorst)))
                           (l :\\: "LamStar argument " :<>: x :<>: "can become NonConst.")
                         pure ()
                     NotRelevant -> do
                                      addConstraint (Solvable (MakeConst (τ, (showPretty x))))
                                        (l :\\: "Static LamStar argument " :<>: x :<>: " can become Const.")
                                      return ()
    mapM addC (zip xrτs xτs)

    -- truncate function context to infinity sensitivity
    mtruncateS inftyS

    -- build the type signature and proper ->* type
    let xrτs' = [x :@ p | (x :@ PrivacyAnnotation p) <- xrτs]

    let τ = (xrτs' :->*: btype)
    return (Fun [τ :@ (Just sign)])


checkSen' scope (Located l (SLet x term body)) = do

   -- put the computation to check the term into the scope
   let scope' = setValue x (checkSens scope term) scope

   -- check body with that new scope
   result <- checkSens scope' body

   debug $ "checking sensitivity SLet: " <> showT x <> " = " <> showPretty term <> " in " <> showPretty body

   return result


checkSen' scope (Located l (BBLet name jτs tail)) = do

   -- the type of this is just a BlackBox, put it in the scope
   let scope' = setValue name (return (BlackBox jτs)) scope

   -- check tail with that new scope
   result <- checkSens scope' tail
   removeVar @SensitivityK name
   return result


checkSen' scope (Located l (BBApply app args cs k)) =
  let
    checkArg arg = do
      let τ = checkSens scope arg
      τ' <- τ
      s <- newVar
      mscale s -- all args get a sensitivity scalar that will be set to inf except if a very special case holds
      return (τ', s)

    checkCap :: TeVar -> TC ()
    checkCap c =
       let delτ = getValue c scope -- see if the capture is in the current scope
       in case delτ of
         Nothing -> return () -- if no, we don't need to do anything as it was not defined yet during this application
         Just delτ -> do      -- if yes, we need to make sure it gets infinite sensitivity in the result context.
                               τ <- newVar -- we achieve this by putting it into the context with some type var and inf annotation
                               setVarS c (WithRelev NotRelevant (τ :@ SensitivityAnnotation inftyS))
                               return ()

    -- find out if the (LInf,Data)-trick can be applied. That is, all functions from (*,Data)-containers to (LInf,Data)-vectors
    -- are 1-sensitive. So if the return type is an (LInf,Data)-vector (or gradient), we can have a constraint on the arguments
    -- that sets the sensitivity to 1 in case they turn out to be (*,Data).
    checkBBKind :: BBKind EmptyExtension -> TC (DMMain, Bool)
    checkBBKind a = let
        err jt form = throwUnlocatedError $ TypeMismatchError $ "The type " <> showPretty jt <> " is not allowed as return type of this black boxe call.\n"
                                                                <> form <> "See documentation of `unbox` for more information."
        -- check the user-given return type dimension and make sure it's const
        checkSize pdt = do
           pdt_actual_ty <- checkSens scope pdt <* mscale zeroId
           pdt_val <- newVar
           pdt_ty <- newVar
           unify (l :\\: "Setting user-given return container dimension.") pdt_actual_ty (NoFun $ Numeric $ Num pdt_ty (Const pdt_val))
           return pdt_val
           
      in case a of
         BBSimple jt -> case jt `elem` [JTInt, JTReal, JTData, JTBool] of
                             True -> do
                                 tt <- createDMType jt
                                 return (NoFun tt, False)
                             False -> err jt "It must be either one of [Integer, Real, Bool, Data] or you need to specify the size.\n"
         BBVecLike jt pdt -> do
           pdt_val <- checkSize pdt -- typecheck the length term

           tt <- createDMType jt -- get return dmtype
           case tt of -- set dimension, return return type
                DMMat _ _ _ _ _ -> err jt ("you gave 1 dim but matrix"<>showT tt)
                DMContainer k nrm clp d et -> do
                    unify (l :\\: "Setting black box return container dimension") d pdt_val
                    let niceType = (NoFun $ DMContainer k LInf clp d (NoFun $ Numeric $ Num DMData NonConst))
                    case (nrm, et) of -- distinguish the container cases where we can apply the (LInf,Data)-trick
                         (LInf, DMAny)   -> return (niceType, True)
                         (TVar _, DMAny) -> return (niceType, True)
                         (LInf, (NoFun (Numeric (Num DMData NonConst))))   -> return (niceType, True)
                         (TVar _, (NoFun (Numeric (Num DMData NonConst)))) -> return (niceType, True)
                         _ -> return (NoFun tt, False)
                DMModel d -> do
                    unify (l :\\: "Setting black box return model dimension") d pdt_val
                    return (NoFun tt, False)
                _ -> err jt "It must be one of [Vector, DMModel, DMGrads, MetricVector, MetricGradient].\n"
         BBMatrix jt pdt1 pdt2 -> do
           (pdt1_val,pdt2_val) <- msumTup (checkSize pdt1, checkSize  pdt2) -- typecheck the size terms
           
           tt <- createDMType jt -- get return dmtype
           case tt of
               DMMat nrm clp rws cls et -> do -- set dimensions, return best return type
                   unify (l :\\: "Setting black box return matrix number of rows") rws pdt1_val
                   unify (l :\\: "Setting black box return matrix number of cols") cls pdt2_val
                   return (NoFun tt, False)
               _ -> err jt "It must be a Matrix.\n"

    margs = checkArg <$> args
    mf = checkSens scope app
  in do
    -- we merge the different TC's into a single result TC
    let caps = checkCap <$> cs
    (τ_box :: DMMain, argτs, _, (τ_ret, isNice)) <- msum4Tup (mf , msumS margs, msumS caps, checkBBKind k) -- sum args and f's context

    addConstraint (Solvable (IsBlackBox (τ_box, fst <$> argτs))) -- constraint makes sure the signature matches the args
       (l :\\: "The signature of function " :<>: app :<>: " matches the arguments.")

    -- constraint sets the sensitivity to the right thing
    case isNice of
        True -> mapM (\s -> addConstraintNoMessage (Solvable (IsBlackBoxReturn s))) argτs >> return () -- trick might by applicable
        False -> -- (LInf,Data) trick is not applicable, set arg sensitivity to inf
          let
            unifyBad (_, s) = unify (l :\\: "Black box return is not a (LInf,Data)-container type, setting all args sensitivity to inf") s inftyS
          in do
            mapM unifyBad argτs
            return ()
        
    return τ_ret


checkSen' scope (Located l (Apply f args)) =
  let
    -- check the argument in the given scope,
    -- and scale scope by new variable, return both
    checkArg :: DMScope -> LocDMTerm -> (TC (DMMain :@ Sensitivity))
    checkArg scope arg = do
      τ' <- checkSens scope arg
      s <- newVar
      mscale s
      return (τ' :@ s)

    margs = checkArg scope <$> args
    mf = checkSens scope f

  in do
    logForce ("[Apply-Sens]Scope is:\n" <> showT (getAllKeys scope))
    (τ_sum :: DMMain, argτs) <- msumTup (mf , msumS margs) -- sum args and f's context
    τ_ret <- newVar -- a type var for the function return type
    addConstraint (Solvable (IsFunctionArgument (τ_sum, Fun [(argτs :->: τ_ret) :@ Nothing])))
      (l :\\:
      "The function " :<>: f :<>: "is applied to" :<>: args)
    return τ_ret


checkSen' scope (Located l (MMap f m)) = do
    s <- newVar
    mv <- svar <$> newSVarWithPriority UserNamePriority "m"
    mr <- newVar
    let mm = checkSens scope m <* mscale s
    let mf = checkSens scope f <* mscale mv <* mscale mr
    (τf :: DMMain, τm) <- msumTup (mf, mm) -- sum args and f's context

    τ_in <- newVar -- a type var for the function input / matrix element type
    τ_out <- newVar -- a type var for the function output type
    nrm <- TVar <$> newTVarWithPriority UserNamePriority "N" -- variable for norm
    clp <- TVar <$> newTVarWithPriority UserNamePriority "C" -- variable for clip
    k <- newVar -- variable for container kind
    unify (l :\\: "MMap argument type") τm (NoFun (DMContainer k nrm clp mv τ_in))

    -- only matrices or vectors (not gradients) are allowed.
    addConstraint (Solvable (IsVecOrMat (k, mr))) (l :\\: "MMap is only allowed on vectors and matrices, so " :<>: m :<>: " has to be one.")

    -- set the type of the function using IFA
    addConstraint (Solvable (IsFunctionArgument (τf, (Fun [([τ_in :@ s] :->: τ_out) :@ Nothing]))))
      (l :\\: "The function applied in MMap must have the right type.")

    return (NoFun (DMContainer k nrm U mv τ_out))


checkSen' scope (Located l (MapRows f m)) = do
    s <- newVar
    ηm <- svar <$> newSVarWithPriority UserNamePriority "m"
    ηn₁ <- svar <$> newSVarWithPriority UserNamePriority "n"
    ηn₂ <- svar <$> newSVarWithPriority UserNamePriority "n"
    let mm = checkSens scope m <* mscale s
    let mf = checkSens scope f <* mscale ηm
    (τf :: DMMain, τm) <- msumTup (mf, mm) -- sum args and f's context

    τ_in <- newVar -- a type var for the function input / matrix element type
    τ_out <- newVar -- a type var for the function output type
    nrm₁ <- TVar <$> newTVarWithPriority UserNamePriority "N" -- variable for norm
    clp₁ <- TVar <$> newTVarWithPriority UserNamePriority "C" -- variable for clip
    nrm₂ <- TVar <$> newTVarWithPriority UserNamePriority "N" -- variable for norm
    clp₂ <- TVar <$> newTVarWithPriority UserNamePriority "C" -- variable for clip
    unify (l :\\: "MapRows argument type") τm (NoFun (DMMat nrm₁ clp₁ ηm ηn₁ τ_in))

    -- set the type of the function using IFA
    addConstraint (Solvable (IsFunctionArgument (τf, (Fun [([NoFun (DMVec nrm₁ clp₁ ηn₁ τ_in) :@ s] :->: NoFun (DMVec nrm₂ clp₂ ηn₂ τ_out)) :@ Nothing]))))
      (l :\\: "The function applied in MapRows must have the right type.")

    return (NoFun (DMMat nrm₂ clp₂ ηm ηn₂ τ_out))


checkSen' scope (Located l (MapCols f m)) = do
    ς <- newVar
    r <- newVar
    ηm₁ <- svar <$> newSVarWithPriority UserNamePriority "m"
    ηm₂ <- svar <$> newSVarWithPriority UserNamePriority "m"
    let mf = checkSens scope f <* mscale (r)
    let mm = checkSens scope m <* mscale (ς ⋅! r)
    (τf :: DMMain, τm) <- msumTup (mf, mm) -- sum args and f's context

    τ_in <- newVar -- a type var for the function input / matrix element type
    τ_out <- newVar -- a type var for the function output type
    nrm₁ <- TVar <$> newTVarWithPriority UserNamePriority "N" -- variable for norm
    clp₁ <- TVar <$> newTVarWithPriority UserNamePriority "C" -- variable for clip
    nrm₂ <- TVar <$> newTVarWithPriority UserNamePriority "N" -- variable for norm
    clp₂ <- TVar <$> newTVarWithPriority UserNamePriority "C" -- variable for clip
    unify (l :\\: "MapCols argument type") τm (NoFun (DMMat nrm₁ clp₁ ηm₁ r τ_in))

    -- set the type of the function using IFA
    --
    -- the output matrix has to have L1 norm, because after (virtually) doing MapRows, we have to transpose the matrix,
    -- and this only works without further sensitivity costs when the norm is L1
    addConstraint (Solvable (IsFunctionArgument (τf, (Fun [([NoFun (DMVec nrm₁ clp₁ ηm₁ τ_in) :@ ς] :->: NoFun (DMVec L1 clp₂ ηm₂ τ_out)) :@ Nothing]))))
      (l :\\: "The function applied in MapCols must have the right type.")

    -- After transposing, since we have L1, we can output every norm,
    -- thus nrm₂ is freely choosable
    return (NoFun (DMMat nrm₂ U ηm₂ r τ_out))


checkSen' scope (Located l (MapCols2 f m₁ m₂)) = do
    ς₁ <- newVar
    ς₂ <- newVar
    r <- newVar
    ηm₁ <- svar <$> newSVarWithPriority UserNamePriority "m"
    ηm₂ <- svar <$> newSVarWithPriority UserNamePriority "m"
    ηm₃ <- svar <$> newSVarWithPriority UserNamePriority "m"
    let mf = checkSens scope f <* mscale (ηm₁ ⋅! r)
    let mm₁ = checkSens scope m₁ <* mscale (ς₁ ⋅! r)
    let mm₂ = checkSens scope m₂ <* mscale (ς₂ ⋅! r)
    (τf :: DMMain, τm₁, τm₂) <- msum3Tup (mf, mm₁, mm₂) -- sum args and f's context

    τ_in₁ <- newVar -- a type var for the function input / matrix element type
    τ_in₂ <- newVar -- a type var for the function input / matrix element type
    τ_out <- newVar -- a type var for the function output type
    nrm₁ <- TVar <$> newTVarWithPriority UserNamePriority "N" -- variable for norm
    clp₁ <- TVar <$> newTVarWithPriority UserNamePriority "C" -- variable for clip
    nrm₂ <- TVar <$> newTVarWithPriority UserNamePriority "N" -- variable for norm
    clp₂ <- TVar <$> newTVarWithPriority UserNamePriority "C" -- variable for clip
    nrm₃ <- TVar <$> newTVarWithPriority UserNamePriority "N" -- variable for norm
    clp₃ <- TVar <$> newTVarWithPriority UserNamePriority "C" -- variable for clip
    unify (l :\\: "Binary MapCols2 first argument type") τm₁ (NoFun (DMMat LInf clp₁ ηm₁ r τ_in₁))
    unify (l :\\: "Binary MapCols2 second argument type") τm₂ (NoFun (DMMat LInf clp₂ ηm₂ r τ_in₂))

    -- set the type of the function using IFA
    addConstraint (Solvable (IsFunctionArgument (τf, (Fun [([NoFun (DMVec nrm₁ clp₁ ηm₁ τ_in₁) :@ ς₁, NoFun (DMVec nrm₂ clp₂ ηm₂ τ_in₂) :@ ς₂] :->: NoFun (DMVec L1 clp₃ ηm₃ τ_out)) :@ Nothing]))))
      (l :\\: "The function applied in binary MapCols2 must have the right type.")

    -- After transposing, since we have L1, we can output every norm,
    -- thus nrm₂ is freely choosable
    return (NoFun (DMMat nrm₃ U ηm₃ r τ_out))


checkSen' scope (Located l (MapRows2 f m₁ m₂)) = do
    ς₁ <- newVar
    ς₂ <- newVar
    ηm <- svar <$> newSVarWithPriority UserNamePriority "m"
    ηn₁ <- svar <$> newSVarWithPriority UserNamePriority "n"
    ηn₂ <- svar <$> newSVarWithPriority UserNamePriority "n"
    ηn₃ <- svar <$> newSVarWithPriority UserNamePriority "n"
    let mf = checkSens scope f <* mscale (ηn₁)
    let mm₁ = checkSens scope m₁ <* mscale (ς₁)
    let mm₂ = checkSens scope m₂ <* mscale (ς₂)
    (τf :: DMMain, τm₁, τm₂) <- msum3Tup (mf, mm₁, mm₂) -- sum args and f's context

    τ_in₁ <- newVar -- a type var for the function input / matrix element type
    τ_in₂ <- newVar -- a type var for the function input / matrix element type
    τ_out <- newVar -- a type var for the function output type
    nrm₁ <- TVar <$> newTVarWithPriority UserNamePriority "N" -- variable for norm
    clp₁ <- TVar <$> newTVarWithPriority UserNamePriority "C" -- variable for clip
    nrm₂ <- TVar <$> newTVarWithPriority UserNamePriority "N" -- variable for norm
    clp₂ <- TVar <$> newTVarWithPriority UserNamePriority "C" -- variable for clip
    nrm₃ <- TVar <$> newTVarWithPriority UserNamePriority "N" -- variable for norm
    clp₃ <- TVar <$> newTVarWithPriority UserNamePriority "C" -- variable for clip
    unify (l :\\: "Binary MapRows2 first argument type") τm₁ (NoFun (DMMat LInf clp₁ ηm ηn₁ τ_in₁))
    unify (l :\\: "Binary MapRows2 second argument type") τm₂ (NoFun (DMMat LInf clp₂ ηm ηn₂ τ_in₂))

    -- set the type of the function using IFA
    addConstraint (Solvable (IsFunctionArgument (τf, (Fun [([NoFun (DMVec nrm₁ clp₁ ηn₁ τ_in₁) :@ ς₁, NoFun (DMVec nrm₂ clp₂ ηn₂ τ_in₂) :@ ς₂] :->: NoFun (DMVec nrm₃ clp₃ ηn₃ τ_out)) :@ Nothing]))))
      (l :\\: "The function applied in binary MapRows2 must have the right type.")

    -- After transposing, since we have L1, we can output every norm,
    -- thus nrm₂ is freely choosable
    return (NoFun (DMMat nrm₃ clp₃ ηm ηn₃ τ_out))


checkSen' scope (Located l (MFold f acc₀ m)) = do
    s₁ <- newVar
    s₂ <- newVar
    ηm <- svar <$> newSVarWithPriority UserNamePriority "m"
    ηn <- svar <$> newSVarWithPriority UserNamePriority "n"
    let mm = checkSens scope m <* mscale s₁
    let macc₀ = checkSens scope acc₀ <* mscale (exp s₂ (ηm ⋅! ηn))
    let mf = checkSens scope f <* mscale (ηm ⋅! ηn)
    (τf :: DMMain, τfold_in, τm) <- msum3Tup (mf, macc₀, mm) -- sum args and f's context

    τ_content <- newVar
    τbody_in <- newVar -- a type var for the function input / matrix element type
    τbody_out <- newVar -- a type var for the function output type
    clp₁ <- TVar <$> newTVarWithPriority UserNamePriority "C" -- variable for clip
    unify (l :\\: "MFold argument type") τm (NoFun (DMMat L1 clp₁ ηm ηn τ_content))

    -- set the type of the function using IFA
    addConstraint (Solvable (IsFunctionArgument (τf, (Fun [([τ_content :@ s₁, τbody_in :@ s₂] :->: τbody_out :@ Nothing)]))))
      (l :\\: "The function applied in MFold must have the right type.")


    -- we use the same constraints for dealing with constness
    -- in the different fold iterations as we do in loop
    --
    addConstraint (Solvable (IsNonConst (τbody_out, τbody_in)))
      (l :\\: "MFold map input and output types must match (except const-ness).")
    addConstraint (Solvable (UnifyWithConstSubtype (τfold_in, τbody_out)))
      (l :\\: "MFold accumulator type must match map output type (except const-ness).")

    return τbody_out


checkSen' scope (Located l (FLet fname term body)) = do

  -- make a Choice term to put in the scope
  let scope' = pushChoice fname (checkSens scope term) scope

  -- check body with that new scope. Choice terms will result in IsChoice constraints upon ivocation of fname

  logForce ("[FLet-Sens] for '" <> showT fname <> "', scope is: " <> showT (getAllKeys scope))
  result' <- checkSens scope' body
  removeVar @SensitivityK fname
  return result'


checkSen' scope (Located l (Choice d)) = do
  let delCs = checkSens scope <$> (snd <$> H.toList d)
  choices <- msumS delCs
  let combined = foldl (:∧:) (Fun []) choices
  return combined


checkSen' scope (Located l (Phi cond ifbr elsebr)) = do
  let ifd   = checkSens scope ifbr
  let elsed = checkSens scope elsebr
  let condd = checkSens scope cond <* mscale inftyS

  τ_sum <- msumS [ifd, elsed, condd]
  (τif, τelse, τcond) <- case τ_sum of
                       [τ1 , τ2 , τ3]  -> return (τ1, τ2, τ3)
                       _ -> throwUnlocatedError (ImpossibleError "Sum cannot return empty.")

  -- the branches need to return types that are indistinguishable by julia dispatch,
  -- otherwise we cannot resolve dispatch because we don't know which branch is going
  -- to be chosen at runtime.
  addConstraint (Solvable (IsJuliaEqual (τif, τelse)))
    (l :\\: "Both branches of a conditional statement must yield the same julia type.")

  unify (l :\\: "If condition must be boolean") τcond (NoFun DMBool)

  -- once we know they are julia-equal, we can safely make the Phi return their supremum.
  τ <- newVar
  addConstraint (Solvable (IsSupremum ((τif, τelse) :=: τ)))
    (l :\\: "Conditional statement returns supremum of branch types.")
  return τ


checkSen' scope (Located l (Tup ts)) = do

  -- check tuple entries and sum contexts
  τsum <- msumS (checkSens scope <$> ts)

  -- ensure nothing that is put in a tuple is a function
  let makeNoFun ty = do v <- newVar
                        unify (l :\\: "Tuple elements cannot be functions") (NoFun v) ty
                        return v
  τnf <- mapM makeNoFun τsum

  log $ "checking sens Tup: " <> showPretty (Tup ts) <> ", type is " <> showPretty (NoFun (DMTup τnf)) <> " when terms were " <> showPretty τsum
  -- return the tuple.
  return (NoFun (DMTup τnf))


checkSen' original_scope (Located l (TLet xs term body)) = do

  -- add all variables bound in the tuple let as args-checking-commands to the scope
  -- TODO: do we need to make sure that we have unique names here?
  let addarg scope x = setValue x (checkSens original_scope (Located (RelatedLoc "Arg generated by this tlet" l) (Arg x JTAny NotRelevant))) scope
  let scope_with_args = foldl addarg original_scope xs

  -- check the body in the scope with the new args
  let cbody = checkSens scope_with_args body

  -- append the computation of removing the args from the context again, remembering their types
  -- and sensitivities
  let cbody' = do
        τ <- cbody
        xs_types_sens <- mapM (removeVar @SensitivityK) xs
        let xs_types_sens' = [ (ty,sens) | WithRelev _ (ty :@ SensitivityAnnotation sens) <- xs_types_sens ]
        return (τ,xs_types_sens')

  -- the computation for checking the term
  let cterm = checkSens original_scope term

  -- merging the computations and matching inferred types and sensitivities
  -- create a new var for scaling the term context
  s <- newVar

  -- extract both TC computations
  -- (the computation for the term is scaled with s)
  ((τbody,xs_types_sens), τterm) <- msumTup (cbody', (cterm <* mscale s))

  -- split the sens/type pairs of the arguments
  let (xs_types , xs_sens) = unzip xs_types_sens

  -- helper function for making sure that type is a nofun, returning the nofun component
  let makeNoFun ty = do v <- newVar
                        unify (l :\\: "Tuple assignees cannot be functions") (NoFun v) ty
                        return v

  -- here we use `makeNoFun`
  -- we make all tuple component types into nofuns
  xs_types' <- mapM makeNoFun xs_types

  -- and require that the type of the term is actually this tuple type
  unify (l :\\: "Set tuple type of assignment") τterm (NoFun (DMTup xs_types'))

  -- finally we need make sure that our scaling factor `s` is the maximum of the tuple sensitivities
  (s ==! (maxS xs_sens)) (l :\\: "TLet sensitivity is maximum of entry sensitivities.")

  log $ "checking sensitivities TLet: " <> showPretty (xs) <> " = " <> showPretty term <> " in " <> showPretty body <> "\n ==> types are " <> showPretty τbody <> " for term " <> showPretty τterm
  -- and we return the type of the body
  return τbody


checkSen' scope (Located l (Loop (start, step, end) cs' (xi, xc) body)) = do
  let cstart = checkSens scope start
  let cstep = checkSens scope step
  let cend = checkSens scope end
  let cniter = msum3Tup (cstart, cstep, cend)

  let scope_vars = getAllKeys scope
  let s0 = "Capture tuple of this loop"
  let s1 = "Var generated for capture tuple by this loop"
  let s2 = "Iterator var generated by this loop"
  let s3 = "Capture var generated by this loop"

  -- build the tup of variables
  let cs = Located (RelatedLoc s0 l) $ Tup ((\a -> (Located (RelatedLoc s1 l) (Var a))) <$> cs')

  -- check it
  let ccs = checkSens scope cs

  -- add iteration and capture variables as args-checking-commands to the scope
  -- TODO: do we need to make sure that we have unique names here?
  let scope' = setValue xi (checkSens scope (Located (RelatedLoc s2 l) (Arg xi JTInt NotRelevant))) scope
  let scope'' = setValue xc (checkSens scope (Located (RelatedLoc s3 l) (Arg xc JTAny IsRelevant))) scope'

  -- check body term in that new scope
  let cbody = checkSens scope'' body

  -- append the computation of removing the args from the context again, remembering their types
  -- and sensitivities
  let cbody' = do
        τ <- cbody
        WithRelev _ (τi :@ si) <- removeVar @SensitivityK xi
        WithRelev _ (τc :@ sc) <- removeVar @SensitivityK xc
        return (τ, (τi, si), (τc, sc))


  -- add scalars for iterator, capture and body context
  -- we compute their values once it is known if the number of iterations is const or not.
  sit <- newVar
  scs <- newVar
  sb <- newVar

  -- scale and sum contexts
  -- τit = type of the iterator (i.e. the term describung the number of iterations)
  -- τcs = type of the capture input tuple
  -- τb = inferred type of the body
  -- τbit = type of the iterator variable xi inferred in the body
  -- τbcs = type of the capture variable xc inferred in the body
  ((tstart, tstep, tend), τloop_in, (τbody_out, (τbit, sbit), (τbody_in, sbcs))) <- msum3Tup (cniter <* mscale sit, ccs <* mscale scs, cbody' <* mscale sb)

  unify (l :\\: "Iterator must be integer.") (NoFun (Numeric (Num (IRNum DMInt) NonConst))) τbit

  τcsnf <- newVar
  unify (l :\\: "Loop captures cannot be functions") (NoFun τcsnf) τloop_in -- functions cannot be captured.

  addConstraint (Solvable (IsNonConst (τbody_out, τbody_in)))
    (l :\\: "Loop captures input must be non-const version of loop output.")
  addConstraint (Solvable (UnifyWithConstSubtype (τloop_in, τbody_out)))
    (l :\\: "Initial loop captures must match loop output.")
  addConstraint (Solvable (IsLoopResult ((sit, scs, sb), sbcs, (tstart,tstep,tend)))) -- compute the right scalars once we know if τ_iter is const or not.
    (l :\\: "Set the sensitivities right once it is known whether number of loop iterations is const.")

  return τbody_in


checkSen' scope (Located l (MCreate n m (x1, x2) body)) =
   let setDim :: TC DMMain -> Sensitivity -> TC DMMain
       setDim tm s = do
          τ <- tm -- check dimension term
          unify (l :\\: "Matrix dimension must be const in mcreate") τ (NoFun (Numeric (Num (IRNum DMInt) (Const s)))) -- dimension must be const integral
          mscale zeroId
          return τ

       checkBody :: TC DMMain -> Sensitivity -> Sensitivity -> TC DMMain
       checkBody bm nv mv = do
          τ <- bm -- check body lambda

          mscale (nv ⋅! mv) -- scale with dimension penalty

          -- remove index variables from the scope, ignore their sensitivity
          WithRelev _ (x1τ :@ _) <- removeVar @SensitivityK x1
          WithRelev _ (x2τ :@ _) <- removeVar @SensitivityK x2

          -- input vars must be integer
          addConstraint (Solvable (IsLessEqual (x1τ, NoFun (Numeric (Num (IRNum DMInt) NonConst)))))
            (l :\\: "First MCreate creation function argument must be integer.")
          addConstraint (Solvable (IsLessEqual (x2τ, NoFun (Numeric (Num (IRNum DMInt) NonConst)))))
            (l :\\: "Second MCreate creation function argument must be integer.")

          return τ
   in do

      let mn    = checkSens scope n
      let mm    = checkSens scope m
      let mbody = checkSens scope body

      -- variables for matrix dimension
      nv <- svar <$> newSVarWithPriority UserNamePriority "n"
      mv <- svar <$> newSVarWithPriority UserNamePriority "m"

      (τbody, _, _) <- msum3Tup (checkBody mbody nv mv, setDim mn nv, setDim mm mv)

      nrm <- TVar <$> newTVarWithPriority UserNamePriority "N" -- variable for norm
      return (NoFun (DMMat nrm U nv mv τbody))


checkSen' scope (Located l (Size m)) = do
  mt <- checkSens scope m

  -- variables for matrix dimension
  nv <- svar <$> newSVarWithPriority UserNamePriority "n"
  mv <- svar <$> newSVarWithPriority UserNamePriority "m"

  -- and matrix entries
  τ <- newVar

  nrm <- TVar <$> newTVarWithPriority UserNamePriority "N" -- variable for norm
  clp <- TVar <$> newTVarWithPriority UserNamePriority "C" -- variable for clip
  unify (l :\\: "Argument of `size` must be a matrix") mt (NoFun (DMMat nrm clp nv mv τ))

  mscale zeroId

  return (NoFun (DMTup [Numeric (Num (IRNum DMInt) (Const nv)), Numeric (Num (IRNum DMInt) (Const mv))]))


checkSen' scope (Located l (Length m)) = do
  mt <- checkSens scope m

  -- variables for vector dimension and entries
  nv <- svar <$> newSVarWithPriority UserNamePriority "n"
  τ <- newVar

  nrm <- TVar <$> newTVarWithPriority UserNamePriority "N" -- variable for norm
  clp <- TVar <$> newTVarWithPriority UserNamePriority "C" -- variable for clip
  unify (l :\\: "Arguemtn of `length` must be a vector.") mt (NoFun (DMVec nrm clp nv τ))

  mscale zeroId

  return (NoFun (Numeric (Num (IRNum DMInt) (Const nv))))


checkSen' scope (Located l (MutClipM c m)) = checkSens scope (Located l (ClipM c m))
checkSen' scope (Located l (ClipM c m)) = do
  τb <- checkSens scope m -- check the matrix

  -- variables for norm and clip parameters and dimension
  clp <- TVar <$> newTVarWithPriority UserNamePriority "C"
  n <- svar <$> newSVarWithPriority UserNamePriority "n"

  -- variable for vector kind
  k <- newVar

  -- only 1-d things are allowed here (vec, grad or 1-d matrix)
  addConstraint (Solvable (IsVecLike k))
    (l :\\: "Clip can only be used on 1-dimensional things.")

  -- set correct matrix type
  unify (l :\\: "Argument of `clip` must be an (LInf, Data)-Matrix.") τb (NoFun (DMContainer k LInf clp n (NoFun (Numeric (Num DMData NonConst)))))

  -- change clip parameter to input
  return (NoFun (DMContainer k LInf (Clip c) n (NoFun (Numeric (Num DMData NonConst)))))


checkSen' scope (Located l (MutConvertM nrm m)) = checkSens scope (Located l (ConvertM nrm m))
checkSen' scope (Located l (ConvertM nrm m)) = do
    
  s <- newVar -- scalar for conversion sensitivity, depends on the norms between which we convert
  τb <- checkSens scope m <* mscale s -- check the matrix

  -- variables for input norm and clip parameters, dimension and element type
  nrm_in <- TVar <$> newTVarWithPriority UserNamePriority "N"
  clp <- TVar <$> newTVarWithPriority UserNamePriority "C"
  n <- svar <$> newSVarWithPriority UserNamePriority "n"
  t <- newVar

  -- variable for container kind
  k <- newVar

  -- set correct matrix type
  unify (l :\\: "Argument of `norm_convert` must be a Matrix.") τb (NoFun (DMContainer k nrm_in clp n t))

  addConstraint (Solvable (ConversionResult (nrm_in, nrm, n, s))) (l :\\: "Set container norm conversion penalty.")

  -- change clip parameter to input
  return (NoFun (DMContainer k nrm clp n t))


checkSen' scope (Located l (ClipN value upper lower)) = do
  (τv,τu,τl) <- msum3Tup (checkSens scope value, checkSens scope upper, checkSens scope lower)

  tv <- newVar
  tk <- newVar
  tu <- newVar
  tl <- newVar
  unify (l :\\: "Parameter of `clip` must be a number.") τv (NoFun (Numeric (Num tv tk)))
  unify (l :\\: "Upper bound parameter of `clip` must be a number.") τu (NoFun (Numeric (Num tv tu)))
  unify (l :\\: "Lower bound parameter of `clip` must be a number.") τl (NoFun (Numeric (Num tv tl)))

  return (NoFun (Numeric (Num tv NonConst)))


checkSen' scope (Located l (Count f m)) = let
    mf = checkSens scope f <* mscale inftyS -- inf-sensitive in the function
    mm = checkSens scope m -- 1-sensitive in the matrix
  in do
    (tf, tm) <- msumTup (mf, mm)

    
    cl <- newVar
    n <- newVar
    r <- newVar
    s <- newVar
        
    unify (l :\\: "Parameter of `count` must be a Data vector.") tm (NoFun (DMVec n cl r (NoFun (Numeric (Num DMData NonConst)))))
    unify (l :\\: "Parameter of `count` must be a function from Data to Bool.") tf (Fun [[(NoFun (Numeric (Num DMData NonConst))) :@ s] :->: (NoFun DMBool) :@ (Just [JTAny])])
    
    return (NoFun (Numeric (Num (IRNum DMInt) NonConst)))


--------------------
-- NOTE this is different from what is in the paper (convert rule), as we scale the result context by 2 not by 1
-- a proof that this is correct is in the matrixnorm pdf, and the authors told me it's correct too
checkSen' scope (Located l (MutUndiscM m)) = checkSens scope (Located l (UndiscM m))
checkSen' scope (Located l (UndiscM m)) = do
  τb <- checkSens scope m -- check the matrix

  -- variables for norm and clip parameters and dimension
  nrm <- TVar <$> newTVarWithPriority UserNamePriority "N"
  clp <- TVar <$> newTVarWithPriority UserNamePriority "C" -- this is a norm, because we do not accept
                -- the unbounded clip value
  n <- newVar
  
  -- variable for vector kind (i.e. vector or grads)
  k <- newVar

  -- set correct matrix type
  unify (l :\\: "Parameter of `norm_convert` must be a container with Data elements and bounded clip parameter.") τb (NoFun (DMContainer k nrm (Clip clp) n (NoFun (Numeric (Num DMData NonConst)))))

  -- we have to scale by two unlike in the paper...see the matrixnorms pdf in julia docs
  mscale (oneId ⋆! oneId)

  -- move clip to the norm position,
  -- and forget about old `nrm
  -- technically the clipping parameter does not change, but we set it to U so it fits with the rest...
  -- see issue 
--  return (NoFun (DMGrads clp (Clip clp) n (Numeric (Num (IRNum DMReal) NonConst))))
  return (NoFun (DMContainer k clp U n (NoFun (Numeric (Num (IRNum DMReal) NonConst)))))

--------------------

{- TODO check issue #78
checkSen' (Transpose m) scope = do
   mb <- checkSens m scope -- check the matrix
   done $ do
      τb <- mb

      -- variables for norm and clip parameters and dimension
      τ <- newVar
      clp <- TVar <$> newTVarWithPriority UserNamePriority "C"
      n <- newVar
      m <- newVar

      -- set correct matrix type
      unify τb (NoFun (DMMat L1 clp n m (Numeric τ))) -- TODO actually mora than L1 would be possible if we had implicit fr-sens

      -- change clip parameter to input
      return (NoFun (DMMat L1 U m n (Numeric τ)))
-}


checkSen' scope  (Located l (Index m i j)) = do

      -- check indices and set their sensitivity to infinity
      let di = checkSens scope i
      let dj = checkSens scope j
      let dx = do
                   _ <- msumTup (di, dj)
                   mscale inftyS
                   return ()

      let dm = checkSens scope m -- check the matrix

      (τm, _) <- msumTup (dm, dx)

      -- variables for element type, norm and clip parameters and dimension
      τ <- newVar
      nrm <- TVar <$> newTVarWithPriority UserNamePriority "N"
      clp <- TVar <$> newTVarWithPriority UserNamePriority "C"
      n <- svar <$> newSVarWithPriority UserNamePriority "n"
      m <- svar <$> newSVarWithPriority UserNamePriority "m"

      -- set matrix type
      unify (l :\\: "Index parameter must be matrix") τm (NoFun (DMMat nrm clp n m τ))

      -- we don't restrict matrix dimension or index size, but leave that to the runtime errors...
      return τ


checkSen' scope (Located l (VIndex v i))  = do

      -- check index and set the sensitivity to infinity
      let di = checkSens scope i
      let dx = do
                   _ <- di
                   mscale inftyS
                   return ()

      let dv = checkSens scope v -- check the vector

      (τv, _) <- msumTup (dv, dx)

      -- variables for element type, norm and clip parameters and dimension
      τ <- newVar
      nrm <- TVar <$> newTVarWithPriority UserNamePriority "N"
      clp <- TVar <$> newTVarWithPriority UserNamePriority "C"
      n <- svar <$> newSVarWithPriority UserNamePriority "n"

      -- set vector type
      unify (l :\\: "single-index parameter must be vector") τv (NoFun (DMVec nrm clp n τ))

      -- we don't restrict vector dimension or index size, but leave that to the runtime errors...
      return τ


checkSen' scope (Located l (Row m i)) = do
          -- check index and set their sensitivity to infinity
      let di = checkSens scope i
      let dx = do
                   _ <- di
                   mscale zeroId
                   return ()

      let dm = checkSens scope m -- check the matrix

      (τm, _) <- msumTup (dm, dx)

      -- variables for element type, norm and clip parameters and dimension
      τ <- newVar
      nrm <- TVar <$> newTVarWithPriority UserNamePriority "N"
      clp <- TVar <$> newTVarWithPriority UserNamePriority "C"
      n <- svar <$> newSVarWithPriority UserNamePriority "n"
      m <- svar <$> newSVarWithPriority UserNamePriority "m"

      -- set matrix type
      unify (l :\\: "Rows can only be taken of matrices") τm (NoFun (DMMat nrm clp n m τ))

      -- we don't restrict matrix dimension or index size, but leave that to the runtime errors...

      return (NoFun (DMVec nrm clp m τ)) -- returns Vector type to accomodate julia behaviour


checkSen' scope (Located l (MutSubGrad ps gs)) = checkSen' scope (Located l (SubGrad ps gs))
checkSen' scope (Located l (SubGrad ps gs)) = do
      -- check model and gradient
      let dps = checkSens scope ps
      let dgs = checkSens scope gs
      (ps, gs) <- msumTup (dps, dgs)

      -- variables for element types, norm and clip parameters and dimension
      τgs <- newVar
      nrm <- TVar <$> newTVarWithPriority UserNamePriority "N"
      clp <- TVar <$> newTVarWithPriority UserNamePriority "C"
      m <- svar <$> newSVarWithPriority UserNamePriority "m"

      -- set argument types
      unify (l :\\: "The thing that the gradient is subtracted from must be a model") ps (NoFun (DMModel m))
      unify (l :\\: "The thing that is subtracted from the model must be a gradient") gs (NoFun (DMGrads nrm clp m (NoFun (Numeric τgs))))

      return (NoFun (DMModel m))


checkSen' scope term@(Located l (ScaleGrad scalar grad)) = do

  let makeNumeric t = do
          tn <- newVar
          unify (l :\\: "Scalar for gradient must be a number") t (Numeric tn)

  let dscalar = checkSens scope scalar
  let dgrad = checkSens scope grad

  -- Create sensitivity / type variables for the multiplication
  (τres , types_sens) <- makeTypeOp (IsBinary DMOpMul) 2
                           (DMPersistentMessage $ "Constraint on the builtin call:" :\\: term)

  ((τ1,s1),(τ2,s2)) <- case types_sens of
    [(τ1,s1),(τ2,s2)] -> pure ((τ1,s1),(τ2,s2))
    _ -> impossible $ "Wrong array return size of makeTypeOp in " <> showPretty term

  -- Create variables for the matrix type
  -- (norm and clip parameters and dimension)
  nrm <- TVar <$> newTVarWithPriority UserNamePriority "N"
  clp <- TVar <$> newTVarWithPriority UserNamePriority "C"
  m <- svar <$> newSVarWithPriority UserNamePriority "m"

  -- infer the types of the scalar and the gradient
  -- we get
  -- `Γ₁ ⋅ s₁ + Γ₂ ⋅ s₂`
  --   where (s₁,s₂) ⩯ tscalar ⋅ tgrad
  (tscalar, tgrad) <- msumTup ((dscalar <* mscale (svar s1)), (dgrad <* mscale (svar s2)))

  -- set τ1 to the actual type of the scalar
  makeNumeric τ1
  unify (l :\\: "Set scalar type") tscalar (NoFun τ1)

  -- and τ2 to the actual content type of the dmgrads
  -- (we allow any kind of annotation on the dmgrads here)
  makeNumeric τ2
  unify (l :\\: "Set gradient type") tgrad (NoFun (DMGrads nrm clp m (NoFun τ2)))

  -- the return type is the same matrix, but
  -- the clipping is now changed to unbounded
  -- and the content type is the result of the multiplication
  τresnum <- newVar
  unify (l :\\: "Set element type of scaled gradient") (Numeric τresnum) τres
  return (NoFun (DMGrads nrm U m (NoFun τres)))


checkSen' scope (Located l (TProject i t)) = do
  τ <- checkSens scope t
  ρ <- newVar
  addConstraintNoMessage (Solvable (IsTProject ((i , τ) :=: ρ)))
  return ρ


checkSen' scope (Located l (ZeroGrad m)) = do
   -- check model
   tm <- checkSens scope m

   -- variables for element type, dimension, result norm and clip parameters
   n <- svar <$> newSVarWithPriority UserNamePriority "n"
   nrm <- TVar <$> newTVarWithPriority UserNamePriority "N"
   clp <- TVar <$> newTVarWithPriority UserNamePriority "C" -- actually variable, as all entries are zero

   -- input must be a model
   unify (l :\\: "Input for `zero_gradient` must be a model") tm (NoFun (DMModel n))

   -- we could return const here but it'll probably be trouble
   return (NoFun (DMGrads nrm clp n (NoFun (Numeric (Num (IRNum DMReal) NonConst)))))


-- The user can explicitly copy return values.
checkSen' scope term@(Located l (Clone t)) = checkSen' scope t 


checkSen' scope term@(Located l (SumGrads g1 g2)) = do
        
  -- Create sensitivity / type variables for the addition
  (τres , types_sens) <- makeTypeOp (IsBinary DMOpAdd) 2
                           (DMPersistentMessage $ "Constraint on the builtin call:" :\\: term)

  ((τ1,s1),(τ2,s2)) <- case types_sens of
    [(τ1,s1),(τ2,s2)] -> pure ((τ1,s1),(τ2,s2))
    _ -> impossible $ "Wrong array return size of makeTypeOp in " <> showPretty term

  -- Create variables for the gradient type
  -- (norm and clip parameters and dimension)
  nrm <- TVar <$> newTVarWithPriority UserNamePriority "N"
  clp1 <- TVar <$> newTVarWithPriority UserNamePriority "C"
  clp2 <- TVar <$> newTVarWithPriority UserNamePriority "C"
  m <- svar <$> newSVarWithPriority UserNamePriority "m"

  -- infer the types of the scalar and the gradient
  let dg1 = checkSens scope g1
  let dg2 = checkSens scope g2

  -- sum contexts and scale with corresponding op sensitivities
  (tg1, tg2) <- msumTup ((dg1 <* mscale (svar s1)), (dg2 <* mscale (svar s2)))

  -- set types to the actual content type of the dmgrads
  -- (we allow any kind of annotation on the dmgrads here but they gotta match)
  τ1num <- newVar
  τ2num <- newVar
  unify (l :\\: "First gradient elements must be numbers") τ1 (Numeric τ1num)
  unify (l :\\: "Second gradient elements must be numbers") τ2 (Numeric τ2num)
  unify (l :\\: "Set first gradient") tg1 (NoFun (DMGrads nrm clp1 m (NoFun τ1)))
  unify (l :\\: "Set second gradient") tg2 (NoFun (DMGrads nrm clp2 m (NoFun τ2)))

  -- the return type is the same matrix, but
  -- the clipping is now changed to unbounded
  -- and the content type is the result type of the addition
  τresnum <- newVar
  return (NoFun (DMGrads nrm U m (NoFun (Numeric τresnum))))


checkSen' scope term@(Located l (SBind x a b)) = do
  throwUnlocatedError (TypeMismatchError $ "Found the term\n" <> showPretty term <> "\nwhich is a privacy term because of the bind in a place where a sensitivity term was expected.")


checkSen' scope term@(Located l (InternalExpectConst a)) = do
  res <- checkSens scope a
  sa <- newVar
  ta <- newVar
  res' <- unify (l :\\: "From explicit `internal_expect_const`") res (NoFun (Numeric (Num ta (Const sa))))

  return res'


checkSen' scope term@(Located l (InternalMutate a)) = do
  res <- checkSens scope a <* mscale (constCoeff $ Fin 2)
  return res


checkSen' scope term@(Located l (Disc t)) = do
  tt <- checkSen' scope t <* mtruncateS inftyS
  v <- newVar
  unify (l :\\: "Input for `disc` must be numeric") (NoFun (Numeric v)) tt
  return (NoFun (Numeric (Num DMData NonConst)))


checkSen' scope term@(Located l (MakeVec m)) = do
  mtype <- checkSens scope m

  -- variables for element type, norm and clip parameters and dimension
  τ <- newVar
  nrm <- TVar <$> newTVarWithPriority UserNamePriority "N"
  clp <- TVar <$> newTVarWithPriority UserNamePriority "C"
  cols <- svar <$> newSVarWithPriority UserNamePriority "n"

  -- set 1-row matrix type
  unify (l :\\: "`vec_from_row` expects one-row matrix") mtype (NoFun (DMMat nrm clp oneId cols τ))

  return (NoFun (DMVec nrm clp cols τ))


checkSen' scope term@(Located l (Undisc t)) = do
  tt <- checkSen' scope t <* mtruncateS inftyS
  v <- newVar
  unify (l :\\: "Input for `undisc` must be numeric (use `undisc_container` for container types)") (NoFun (Numeric v)) tt
  return (NoFun (Numeric (Num (IRNum DMReal) NonConst)))


checkSen' scope term@(Located l (MakeRow m)) = do
  mtype <- checkSens scope m

  -- variables for element type, norm and clip parameters and dimension
  τ <- newVar
  nrm <- TVar <$> newTVarWithPriority UserNamePriority "N"
  clp <- TVar <$> newTVarWithPriority UserNamePriority "C"
  cols <- svar <$> newSVarWithPriority UserNamePriority "m"

  -- set 1-row matrix type
  unify (l :\\: "`row_from_vec` expects vector") mtype (NoFun (DMVec nrm clp cols τ))

  return (NoFun (DMMat nrm clp oneId cols τ))


-- Everything else is currently not supported.
checkSen' scope t = throwLocatedError (TermColorError SensitivityK (showPretty $ getLocated t)) (getLocation t)

--------------------------------------------------------------------------------
-- Privacy terms

checkPri' :: DMScope -> LocDMTerm -> TC DMMain
checkPri' scope (Located l (Ret t)) = do
   τ <- checkSens scope t
   mtruncateP inftyP
   log $ "checking privacy " <> showPretty (Ret t) <> ", type is " <> showPretty τ
   return τ


checkPri' scope term@(Located l (Apply f args)) =
  let
    -- check the argument in the given scope,
    -- and scale scope by new variable, return both
    checkArg :: DMScope -> LocDMTerm -> (TC (DMMain :@ Privacy))
    checkArg scope arg = do
      τ <- checkSens scope arg
      restrictAll oneId -- sensitivity of everything in context must be <= 1
        (l :\\:
         "In the privacy function application: " :\\->: term :\\:
         "The argument" :<>: arg :<>: "has to be 1-sensitive in every variable which occurs within."
        )
      p <- newPVar
      mtruncateP p
      return (τ :@ p)

    margs = (\arg -> (checkArg scope arg)) <$> args

    f_check :: (TC DMMain) = do
       -- we typecheck the function, but `apply` our current layer on the Later computation
       -- i.e. "typecheck" means here "extracting" the result of the later computation
       res <- (checkSens scope f)
       logForce ("[Apply-Priv]Scope is:\n" <> showT (getAllKeys scope))
       mtruncateP inftyP -- truncate f's context to ∞
       return res

  in do
    (τ_sum :: DMMain, argτs) <- msumTup (f_check , msumP margs) -- sum args and f's context
    τ_ret <- newVar -- a type var for the function return type
    addConstraint (Solvable (IsFunctionArgument (τ_sum, Fun [(argτs :->*: τ_ret) :@ Nothing])))
      (l :\\:
        "In the privacy function application: " :\\->: term)

    return τ_ret


checkPri' scope (Located l (SLet x term body)) = do

  -- put the computation to check the term into the scope
  --  let scope' = setValue x (checkSens term scope) scope
  let scope' = setValue x (checkSens scope term) scope

  -- check body with that new scope
  result <- checkPriv scope' body

  log $ "checking (transparent) privacy SLet: " <> showPretty x <> " = " <> showPretty term <> " in " <> showPretty body

  return result


checkPri' scope (Located l (SBind x term body)) = do
  -- this is the bind rule.
  -- as it does not matter what sensitivity/privacy x has in the body, we put an Arg term in the scope
  -- and later discard its annotation. we use checkSens because there are no Vars in privacy terms so
  -- x will only ever be used in a sensitivity term.
  let scope' = setValue x (checkSens scope (Located (RelatedLoc "Arg generated by this bind" l) (Arg x JTAny NotRelevant))) scope

  -- check body with that new scope
  let dbody = checkPriv scope' body
  let mbody = do
             τ <- dbody
             -- discard x from the context, never mind it's inferred annotation
             WithRelev _ (τx :@ _) <- removeVar @PrivacyK x
             return (τ, τx)

  -- check term with old scope
  let dterm = checkPriv scope term

  -- sum contexts
  ((τbody, τx), τterm) <- msumTup (mbody, dterm)

  -- unify type of x in the body with inferred type of the assignee term
  unify (l :\\: "Assignee term must have same type as the inferred type of the variable in following code.") τx τterm

  -- make sure that τterm is not a functiontype
  -- this is necessary because elsewise it might be capturing variables
  -- which we do not track here. (We can only track that if we put the
  -- computation for checking the term itself into the scope, instead
  -- of an arg representing it. But this would not work with the bind rule.)
  -- See https://github.com/DiffMu/DiffPrivacyInferenceHs/issues/18
  τnofun <- newVar
  unify (l :\\: "Term after a bind cannot be a function") τbody (NoFun τnofun)

  debug $ "checking privacy SLet: " <> showPretty x <> " = " <> showPretty term <> " in " <> showPretty body<> "\n ==> inferred type is " <> showPretty τx <> ", term type is " <> showPretty τterm <> ", body types is " <> showPretty τbody
  -- return the type of this bind expression
  return τbody

checkPri' scope (Located l (FLet fname term body)) = do

  -- make a Choice term to put in the scope
  let scope' = pushChoice fname (checkSens scope term) scope

  -- check body with that new scope. Choice terms will result in IsChoice constraints upon ivocation of fname
  result <- checkPriv scope' body 

  removeVar @PrivacyK fname
  return result


-----------------------------------
-- "transparent" privacy tlets

checkPri' original_scope curterm@(Located l (TLet xs term body)) = do

  -- put the computations to check the terms into the scope
  -- (in privacy terms we use projections here, making this a "transparent" tlet)

  let addarg scope (x, i) = setValue x (checkSens original_scope (Located (RelatedLoc "TProject generated by this tlet" l) (TProject i term))) scope
  let scope_with_args = foldl addarg original_scope (xs `zip` [0..])

  -- -- check body with that new scope
  result <- checkPriv scope_with_args body

  log $ "checking (transparent) privacy SLet: " <> showPretty xs <> " = " <> showPretty term <> " in " <> showPretty body

  return result


checkPri' original_scope curterm@(Located l (TBind xs term body)) = do
  a <- newTeVar "tbind_var"
  -- we check the term
  -- ```
  --  sbind a <- term
  --  tlet (xs...) = a
  --  body
  -- ```
  let s1 = "SBind-TLet construction generated for this TBind"
  checkPri' original_scope (Located (RelatedLoc s1 l) (SBind a term
                   (Located (RelatedLoc s1 l) (TLet xs (Located (RelatedLoc s1 l) (Var a))
                         body))))


checkPri' scope (Located l (MutGauss rp εp δp f)) = checkPri' scope (Located l (Gauss rp εp δp f))
checkPri' scope term@(Located l (Gauss rp εp δp f)) =
  let
   setParam :: TC DMMain -> Sensitivity -> TC ()
   setParam dt v = do -- parameters must be const numbers.
      τ <- dt
      τv <- newVar
      unify (l :\\: "Gauss parameters must be const (Static) numbers.") τ (NoFun (Numeric (Num τv (Const v))))
      mtruncateP zeroId
      return ()

   setBody df (ε, δ) r = do
      -- extract f's type from the TC monad
      τf <- df
      -- interesting input variables must have sensitivity <= r
      restrictInteresting r
        (l :\\:
         "Gauss: All variables which are *NOT* annotated as 'Static' and are used in the body" :\\->: f :\\:
         "Have to have sensitivity <= " :<>: r
        )
      -- interesting output variables are set to (ε, δ), the rest is truncated to ∞
      ctxBeforeTrunc <- use types
      debug $ "[Gauss] Before truncation, context is:\n" <> showT ctxBeforeTrunc
      mtruncateP inftyP
      ctxAfterTrunc <- use types
      debug $ "[Gauss] After truncation, context is:\n" <> showT ctxAfterTrunc
      (ivars, itypes) <- getInteresting
      mapM (\(x, (τ :@ _)) -> setVarP x (WithRelev IsRelevant (τ :@ PrivacyAnnotation (ε, δ)))) (zip ivars itypes)
      -- return type is a privacy type.
      return τf
   in do
      -- check all the parameters and f, extract the TC monad from the Delayed monad.
      let drp = checkSens scope rp
      let dεp = checkSens scope εp
      let dδp = checkSens scope δp
      let df  = checkSens scope f

      -- create variables for the parameters
      v_ε :: Sensitivity <- newVar
      v_δ :: Sensitivity <- newVar
      v_r :: Sensitivity <- newVar

      -- parameters must be in (0,1) for gauss to be DP
      addConstraint (Solvable (IsLess (v_ε, oneId :: Sensitivity)))
        (l :\\: "Gauss epsilon parameter must be <= 1")
      addConstraint (Solvable (IsLess (v_δ, oneId :: Sensitivity)))
        (l :\\: "Gauss delta parameter must be <= 1")
      addConstraint (Solvable (IsLess (zeroId :: Sensitivity, v_ε)))
        (l :\\: "Gauss epsilon parameter must be > 0")

      addConstraint (Solvable (IsLess (zeroId :: Sensitivity, v_δ)))
        (l :\\: "Gauss delta parameter must be > 0")
        
      -- restrict interesting variables in f's context to v_r
      let mf = setBody df (v_ε, v_δ) v_r

      let mr = setParam drp v_r
      let mε = setParam dεp v_ε
      let mδ = setParam dδp v_δ

      (τf, _) <- msumTup (mf, msum3Tup (mr, mε, mδ))

      τgauss <- newVar
      addConstraint (Solvable (IsAdditiveNoiseResult ((NoFun τgauss), τf))) -- we decide later if its gauss or mgauss according to return type
        (l :\\: "Decide if it's gauss or matrix gauss.")

      return (NoFun (τgauss))


checkPri' scope (Located l (MutLaplace rp εp f)) = checkPri' scope (Located l (Laplace rp εp f))
checkPri' scope term@(Located l (Laplace rp εp f)) =
  let
   setParam :: TC DMMain -> Sensitivity -> TC ()
   setParam dt v = do -- parameters must be const numbers.
      τ <- dt
      τv <- newVar
      unify (l :\\: "Laplace parameters must be const (Static) numbers.") τ (NoFun (Numeric (Num τv (Const v))))
      mtruncateP zeroId
      return ()

   setBody df ε r = do
      -- extract f's type from the TC monad
      τf <- df
      -- interesting input variables must have sensitivity <= r
      restrictInteresting r
        (l :\\: 
         "Laplace: All variables which are *NOT* annotated as 'Static' and are used in the body" :\\->: f :\\:
         "Have to have sensitivity <= " :<>: r
        )
      -- interesting output variables are set to (ε, δ), the rest is truncated to ∞
      mtruncateP inftyP
      (ivars, itypes) <- getInteresting
      mapM (\(x, (τ :@ _)) -> setVarP x (WithRelev IsRelevant (τ :@ PrivacyAnnotation (ε, zeroId)))) (zip ivars itypes)
      -- return type is a privacy type.
      return τf
   in do
      -- check all the parameters and f, extract the TC monad from the Delayed monad.
      let drp = checkSens scope rp
      let dεp = checkSens scope εp
      let df  = checkSens scope f

      -- create variables for the parameters
      v_ε :: Sensitivity <- newVar
      v_r :: Sensitivity <- newVar

      -- eps parameter must be > 0 for scaling factor to be well-defined
      addConstraint (Solvable (IsLess (zeroId :: Sensitivity, v_ε)))
        (l :\\: "Laplace epsilon parameter must be > 0")

      -- sensitivity parameter must be > 0 for laplace distribution to be well-defined
      addConstraint (Solvable (IsLess (zeroId :: Sensitivity, v_r)))
        (l :\\: "Sensitivity of the input to Laplace must be > 0")

      -- restrict interesting variables in f's context to v_r
      let mf = setBody df v_ε v_r

      let mr = setParam drp v_r
      let mε = setParam dεp v_ε

      (τf, _) <- msumTup (mf, msumTup (mr, mε))

      τlap <- newVar
      addConstraint (Solvable (IsAdditiveNoiseResult ((NoFun τlap), τf))) -- we decide later if its lap or mlap according to return type
        (l :\\: "Decide if it's laplace or matrix laplace.")
 
      return (NoFun (τlap))


checkPri' scope (Located l (AboveThresh qs e d t)) = do
      eps <- newVar

      let mqs = checkSens scope qs <* mtruncateP inftyP
      let me = checkSens scope e   <* mtruncateP (zeroId, zeroId)
      let md  = checkSens scope d  <* mtruncateP (eps, zeroId)
      let mt  = checkSens scope t  <* mtruncateP inftyP

      n <- newVar -- number of queries
      nrm <- TVar <$> newTVarWithPriority UserNamePriority "N" -- norm of query vector
      clp <- TVar <$> newTVarWithPriority UserNamePriority "C" -- clip of query vector

      (τqs, (τe, τd, τt)) <- msumTup (mqs, msum3Tup (me, md, mt))

      tfun <- newVar
      addConstraint (Solvable (IsFunctionArgument (tfun, Fun([([τd :@ (oneId :: Sensitivity)] :->: (NoFun (Numeric (Num (IRNum DMReal) NonConst)))) :@ Nothing]))))
        (l :\\: "AboveThreshold query vector must contain functions of the right type.")
      unify (l :\\: "Set AboveThreshold query vector type") τqs (NoFun (DMVec nrm clp n tfun))
      
      addConstraint (Solvable (IsLessEqual (τe, (NoFun (Numeric (Num (IRNum DMReal) (Const eps)))))))
        (l :\\: "AboveThreshold epsilon parameter must be const (Static).")
      addConstraint (Solvable (IsLessEqual (τt, (NoFun (Numeric (Num (IRNum DMReal) NonConst))))))
        (l :\\: "AboveThreshold threshold parameter must be const (Static).")

      return (NoFun (Numeric (Num (IRNum DMInt) NonConst)))


checkPri' scope term@(Located l (Exponential rp εp xs f)) = do
  let
   setParamConst :: TC DMMain -> Sensitivity -> TC ()
   setParamConst dt v = do -- parameters must be const numbers.
      τ <- dt
      τv <- newVar
      unify (l :\\: "Exponential mechanism parameters must be const (Static) numbers.") τ (NoFun (Numeric (Num τv (Const v))))
      return ()

   setParamVecLike :: TC DMMain -> DMMain -> TC ()
   setParamVecLike dt v = do
      t_actual <- dt
      t_required <- NoFun <$> (DMVec <$> newVar <*> newVar <*> newVar <*> pure v)
      unify (l :\\: "Exponential mechanism expects a vector") t_actual t_required
      return ()

   -- the function (given as "body") needs to take the content type of the vector
   -- and return real.
   setBody df ε r t_x = do

      -- extract f's type from the TC monad
      t_f_actual <- df

      -- unify with expected
      --  the sensitivity of the function can be \infty,
      --  so we simply use a var and allow any sensitivity.
      s_input <- newVar
      let t_f_required = Fun ([([t_x :@ s_input] :->: (NoFun (Numeric (Num (IRNum DMReal) NonConst)))) :@ Just [JTAny]])
      unify (l :\\: "Exponential mechanism expects a function from element type to the reals.") t_f_actual t_f_required

      -- interesting input variables must have sensitivity <= r
      restrictInteresting r
        (l :\\:
         "Exponential: All variables which are *NOT* annotated as 'Static' and are used in the body" :\\->: f :\\:
         "Have to have sensitivity <= " :<>: r
        )

      -- interesting output variables are set to (ε, 0), the rest is truncated to ∞
      ctxBeforeTrunc <- use types
      debug $ "[Exponential] Before truncation, context is:\n" <> showT ctxBeforeTrunc
      mtruncateP inftyP
      ctxAfterTrunc <- use types
      debug $ "[Exponential] After truncation, context is:\n" <> showT ctxAfterTrunc
      (ivars, itypes) <- getInteresting
      mapM (\(x, (τ :@ _)) -> setVarP x (WithRelev IsRelevant (τ :@ PrivacyAnnotation (ε, zeroId)))) (zip ivars itypes)

      return ()

   in do
      -- check all the parameters and f, extract the TC monad from the Delayed monad.
      let drp = checkSens scope rp
      let dεp = checkSens scope εp
      let dxs = checkSens scope xs
      let df  = checkSens scope f

      -- create variables for the parameters
      v_ε :: Sensitivity <- newVar
      v_r :: Sensitivity <- newVar
      v_t_x :: DMMain   <- newVar

      -- restrict interesting variables in f's context to v_r
      let mf = setBody df v_ε v_r v_t_x

      let mr  = setParamConst drp v_r  <* mtruncateP zeroId
      let mε  = setParamConst dεp v_ε  <* mtruncateP zeroId
      let mxs = setParamVecLike dxs v_t_x <* mtruncateP inftyP

      (τf, _) <- msumTup (mf, msum3Tup (mr, mε, mxs))

      return (v_t_x)


checkPri' scope (Located l (Loop (start,step,end) cs' (xi, xc) body)) =
   let setInteresting (xs, τps) n = do
          let τs = map fstAnn τps
          let ps = map sndAnn τps

          let ε = maxS (map (\(PrivacyAnnotation (εs, _)) -> εs) ps)
          let δ = maxS (map (\(PrivacyAnnotation (_, δs)) -> δs) ps)

          δn :: Sensitivity <- newVar -- we can choose this freely!
          addConstraint (Solvable (IsLessEqual (δn, oneId :: Sensitivity))) -- otherwise we get a negative ε...
            (l :\\: "This variable can be chosen freely <= 1")
          addConstraint (Solvable (IsLess (zeroId :: Sensitivity, δn))) -- otherwise we get an infinite ε...
            (l :\\: "This variable can be chosen freely > 0")

          memorizeUserVar δn "within (0,1]" JTReal l

          -- compute the new privacy for the xs according to the advanced composition theorem
          let two = oneId ⋆! oneId
          let newp = (two ⋅! (ε ⋅! (sqrt (two ⋅! (n ⋅! (minus (ln oneId) (ln δn)))))), δn ⋆! (n ⋅! δ))

          mapM (\(x, τ) -> setVarP x (WithRelev IsRelevant (τ :@ PrivacyAnnotation newp))) (zip xs τs)
          return ()
   in do
      let s0 = "Capture tuple of this loop"
      let s1 = "Var generated for capture tuple by this loop"
      let s2 = "Iterator var generated by this loop"
      let s3 = "Capture var generated by this loop"

      let cstart = checkSens scope start
      let cstep = checkSens scope step
      let cend = checkSens scope end
      let cniter = msum3Tup (cstart, cstep, cend) <* mtruncateP zeroId

      -- build the tup of variables
      let cs = (Located (RelatedLoc s0 l) (Tup ((\a -> (Located (RelatedLoc s1 l) (Var a))) <$> cs')))

      -- check it
      let mcaps = checkSens scope cs <* mtruncateP inftyP

      -- add iteration and capture variables as args-checking-commands to the scope
      -- capture variable is not relevant bc captures get ∞ privacy anyways
      -- TODO: do we need to make sure that we have unique names here?
      let scope'  = setValue xi (checkSens scope (Located (RelatedLoc s2 l) (Arg xi JTInt NotRelevant))) scope
      let scope'' = setValue xc (checkSens scope (Located (RelatedLoc s3 l) (Arg xc JTAny NotRelevant))) scope'

      -- check body term in that new scope
      let cbody = checkPriv scope'' body 

      -- append the computation of removing the args from the context again, remembering their types
      -- and sensitivities
      let cbody' = do
            τ <- cbody
            WithRelev _ (τi :@ _) <- removeVar @PrivacyK xi
            WithRelev _ (τc :@ _) <- removeVar @PrivacyK xc -- unify with caps type?

            interesting <- getInteresting
            mtruncateP inftyP

            n <- newVar
            setInteresting interesting n
            return (τ, n, τi, τc)

      -- scale and sum contexts
      -- τit = type of the iterator (i.e. the term describung the number of iterations)
      -- τcs = type of the capture input tuple
      -- τb = inferred type of the body
      -- n = number of iterations as assumed in the loop body
      -- τbit = type of the iterator variable xi inferred in the body
      -- τbcs = type of the capture variable xc inferred in the body
      ((tstart, tstep, tend), τloop_in, (τbody_out, n, τbit, τbody_in)) <- msum3Tup (cniter, mcaps, cbody')

      n1 <- newVar
      n2 <- newVar
      n3 <- newVar
      unify (l :\\: "Start value of iterator in private loop must be const (Static) integer.") tstart (NoFun (Numeric (Num (IRNum DMInt) (Const n1)))) -- number of iterations must be constant integer
      unify (l :\\: "Step size in interator of private loop must be const (Static) integer.") tstep (NoFun (Numeric (Num (IRNum DMInt) (Const n2)))) -- number of iterations must be constant integer
      unify (l :\\: "End value of iterator in private loop must be const (Static) integer.") tend (NoFun (Numeric (Num (IRNum DMInt) (Const n3)))) -- number of iterations must be constant integer
      unify (l :\\: "Iterator in private loop must be integer") (NoFun (Numeric (Num (IRNum DMInt) NonConst))) τbit -- number of iterations must match type requested by body

      let η = ceil (divide (minus n3 (minus n1 oneId)) n2) -- compute number of iterations
      unify (l :\\: "User-given number of iterations must match number of iterations assumed in the loop.") n η
      
      τcsnf <- newVar
      unify (l :\\: "Loop captures cannot be functions.") (NoFun τcsnf) τloop_in -- functions cannot be captured.

      addConstraint (Solvable (IsNonConst (τbody_out, τbody_in)))
         (l :\\: "Loop captures input must be non-const version of loop output.")
      addConstraint (Solvable (UnifyWithConstSubtype (τloop_in, τbody_out)))
         (l :\\: "Initial loop captures must match loop output.")

      return τbody_in


checkPri' scope term@(Located l (SmpLet xs (Located l2 (Sample n m1_in m2_in)) tail)) =
  let checkArg :: LocDMTerm -> (TC (DMMain, Privacy))
      checkArg arg = do
         -- check the argument in the given scope,
         -- and scale scope by new variable, return both
         τ <- checkSens scope arg
         restrictAll oneId -- sensitivity of everything in context must be <= 1
           ("In the sample call: " :<>: term :\\:
           "The argument" :<>: arg :<>: "has to be 1-sensitive in every variable which occurs within."
           )
         p <- newPVar
         mtruncateP p
         return (τ, p)
         
      mn = checkArg n
      mm1 = checkArg m1_in
      mm2 = checkArg m2_in
      msum = msum3Tup (mn, mm1, mm2)
      
      mtail = do
                -- add all variables bound by the sample let as args-checking-commands to the scope
                -- TODO: do we need to make sure that we have unique names here?
                let addarg scope' (x) = setValue x (checkSens scope (Located (RelatedLoc "Arg generated for this sample" l) (Arg x JTAny IsRelevant))) scope'
                let scope_with_samples = foldl addarg scope xs
              
                -- check the tail in the scope with the new args
                τ <- checkPriv scope_with_samples tail
              
                -- append the computation of removing the args from the context again, remembering their types
                -- and privacies
                xs_types_privs <- mapM (removeVar @PrivacyK) xs
                let xs_types_privs' = [ (ty,p) | WithRelev _ (ty :@ PrivacyAnnotation p) <- xs_types_privs ]
                -- truncate tail context to infinite privacy and return tail type and args types/privacies
                case xs_types_privs' of
                     [(t1,p1), (t2,p2)] -> ((return (τ,(t1,p1),(t2,p2))) <* mtruncateP inftyP)
                     _ -> impossible $ ("Both results of sample must be assigned a name. Instead I got " <> (showPretty xs_types_privs'))
  in do
      -- sum all involved contexts.
      -- tn, tm1, tm2: types of n_samples and the two matrices that are sampled
      -- pn, pm1, pm2: privacy vars that truncate the context of n, m1_in and m2_in
      -- ttail: inferred type of the tail
      -- (t1, (e1,d1)), (t2, (e2,d2)): inferred types and privacies of the xs in the tail
      (((tn,pn), (tm1,pm1), (tm2,pm2)), (ttail, (t1, (e1,d1)), (t2, (e2,d2)))) <- msumTup (msum, mtail)
      
      -- variables for clip parameter, dimensions and number of samples (m2)
      clp <- TVar <$> newTVarWithPriority UserNamePriority "C"
      m1 <- svar <$> newSVarWithPriority UserNamePriority "m"
      m2 <- svar <$> newSVarWithPriority UserNamePriority "m"
      n1 <- svar <$> newSVarWithPriority UserNamePriority "n"
      n2 <- svar <$> newSVarWithPriority UserNamePriority "n"
    
      -- set number of samples to const m2 and truncate context with 0
      unify (l :\\: "Number of samples must be const (Static) integer") tn (NoFun (Numeric (Num (IRNum DMInt) (Const m2))))
      unify (l :\\: "Truncate context of number of samples with 0") pn (zeroId, zeroId)
      
      -- set input matrix types and truncate contexts to what it says in the rule
      unify (l :\\: "Sample input matrix must be (LInf, Data)") tm1 (NoFun (DMMat LInf clp m1 n1 (NoFun (Numeric (Num DMData NonConst)))))
      unify (l :\\: "Sample input matrix must be (LInf, Data)") tm2 (NoFun (DMMat LInf clp m1 n2 (NoFun (Numeric (Num DMData NonConst)))))
      let two = oneId ⋆! oneId
      unify (l :\\: "Truncate first sample matrix context") pm1 (divide (two ⋅! (m2 ⋅! e1)) m1, divide (m2 ⋅! d1) m1)
      unify (l :\\: "Truncate second sample matrix context") pm2 (divide (two ⋅! (m2 ⋅! e2)) m1, divide (m2 ⋅! d2) m1)

      -- set correct types for sample results in the tail
      unify (l :\\: "Set type of first sample result") tm1 t1
      unify (l :\\: "Set type of second sample result") tm2 t2

      -- expression has type of the tail
      return ttail


checkPri' scope (Located l (PReduceCols f m)) = do
    ε <- newVar
    δ <- newVar
    ηm <- svar <$> newSVarWithPriority UserNamePriority "m"
    r <- newVar
    let mm = checkSens scope m <* mtruncateP (r ⋅! ε, r ⋅! δ)
    let mf = checkSens scope f <* mtruncateP inftyP
    (τf :: DMMain, τm) <- msumTup (mf, mm) -- sum args and f's context

    c <- newVar -- input clipping parameter is free
    unify (l :\\: "Parameter of `reduce_cols` must be (Linf,Data)-Matrix") τm (NoFun (DMMat LInf c ηm r (NoFun (Numeric (Num DMData NonConst)))))

    -- set the type of the function using IFA
    τ_out <- newVar -- a type var for the function output type
    addConstraint (Solvable (IsFunctionArgument (τf, (Fun [([NoFun (DMMat LInf U ηm oneId (NoFun (Numeric (Num DMData NonConst)))) :@ (ε, δ)] :->*: τ_out) :@ Nothing]))))
      (l :\\: "ReduceCols map must have the right type.")

    return (NoFun (DMVec LInf U r τ_out))


checkPri' scope (Located l (MutPFoldRows f acc m₁ m₂)) = checkPri' scope (Located l (PFoldRows f acc m₁ m₂))
checkPri' scope (Located l (PFoldRows f acc m₁ m₂)) = do
    ε <- newVar
    δ <- newVar
    ηm <- svar <$> newSVarWithPriority UserNamePriority "m"
    ηn₁ <- svar <$> newSVarWithPriority UserNamePriority "n"
    ηn₂ <- svar <$> newSVarWithPriority UserNamePriority "n"
    l₁ <- TVar <$> newTVarWithPriority UserNamePriority "N"
    l₂ <- TVar <$> newTVarWithPriority UserNamePriority "N"
    c₁ <- TVar <$> newTVarWithPriority UserNamePriority "C"
    c₂ <- TVar <$> newTVarWithPriority UserNamePriority "C"
    let mf = checkSens scope f <* mtruncateP inftyP
    let macc = checkSens scope acc <* mtruncateP inftyP
    let mm₁ = checkSens scope m₁ <* mtruncateP (ε, δ)
    let mm₂ = checkSens scope m₂ <* mtruncateP (ε, δ)
    (τf :: DMMain, τfold_in, τm₁, τm₂) <- msum4Tup (mf, macc, mm₁, mm₂) -- sum args and f's context

    unify (l :\\: "The term " :<>: m₁ :\\: "Parameter of `parallel_private_fold_rows` must be a Data-Matrix")
      τm₁ (NoFun (DMMat l₁ c₁ ηm ηn₁ (NoFun (Numeric (Num DMData NonConst)))))

    unify (l :\\: "The term " :<>: m₂ :\\: "Parameter of `parallel_private_fold_rows` must be a Data-Matrix")
      τm₂ (NoFun (DMMat l₂ c₂ ηm ηn₂ (NoFun (Numeric (Num DMData NonConst)))))

    -- type variables for the accumulator (body input/output)
    τbody_in  <- newVar
    τbody_out <- newVar

    -- the body function may be anything private in the accumulator
    accε <- newVar
    accδ <- newVar

    -- set the type of the function using IFA
    addConstraint (Solvable (IsFunctionArgument (τf,
                                                 (Fun [([NoFun (DMVec l₁ c₁ ηn₁ (NoFun (Numeric (Num DMData NonConst)))) :@ (ε, δ)
                                                        ,NoFun (DMVec l₂ c₂ ηn₂ (NoFun (Numeric (Num DMData NonConst)))) :@ (ε, δ)
                                                        ,τbody_in :@ (accε,accδ)]
                                                        :->*:
                                                        τbody_out) :@ Nothing]))))
      (l :\\: "The term " :<>: f :\\: "Function parameter of `parallel_private_fold_rows` must have the right type.")

    addConstraint (Solvable (IsNonConst (τbody_out, τbody_in)))
      (l :\\: "MFold map input and output types must match (except const-ness).")
    addConstraint (Solvable (UnifyWithConstSubtype (τfold_in, τbody_out)))
      (l :\\: "MFold accumulator type must match map output type (except const-ness).")

    return τbody_out


checkPri' scope t = throwLocatedError (TermColorError PrivacyK (showPretty $ getLocated t)) (getLocation t)

