
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}

module DiffMu.Typecheck.Preprocess.Demutation.Main where

import DiffMu.Prelude
import DiffMu.Abstract
import DiffMu.Core
import DiffMu.Core.TC

import DiffMu.Core.Logging
import DiffMu.Abstract.Data.Permutation
import DiffMu.Typecheck.Preprocess.Common
import DiffMu.Typecheck.Preprocess.TopLevel
import DiffMu.Typecheck.Preprocess.Demutation.Definitions

import qualified Data.HashMap.Strict as H

import qualified Data.Text as T
import Data.Foldable

import Debug.Trace

import qualified Prelude as P
import Test.QuickCheck.Property (Result(expect))

import Control.Monad.Trans.Class
import qualified GHC.RTS.Flags as LHS
import Control.Exception (throw)
import DiffMu.Typecheck.Preprocess.Demutation.Definitions (getAllMemVarsOfMemState, procVarAsTeVarInMutCtx, MutationArgumentType)



ld s l = Located (downgradeToRelated s l)

demutTLetStatement :: SourceLocExt -> LetKind -> [ProcVar] -> LocDemutDMTerm -> MTC TermType
demutTLetStatement l ltype vars term = case vars of
  [var] -> do
            var' <- (procVarAsTeVar var)
            return (Statement l (Extra (DemutSLetBase ltype var' term))
                   (SingleMove var))
  vars -> do
            vars' <- mapM procVarAsTeVar vars
            return (Statement l (Extra (DemutTLetBase ltype (vars') term))
                   (TupleMove [(Located l (SingleMove v)) | v <- vars]))

---
-- elaborating loops
-- not allowed:
-- - FLet
-- - JuliaReturn
-- - modify iteration variable

demutate :: LocProcDMTerm -> MTC (LocDemutDMTerm)
demutate term = do
  -- logForce $ "Term before phi rearranging:\n" <> showPretty term

  -- term' <- rearrangePhi term

  -- logForce $ "-----------------------------------"
  logForce $ "Term before mutation elaboration:\n" <> showPretty term

  topscname <- newScopeVar "toplevel"

  res <- elaborateTopLevel (Scope [topscname]) term
  resterm <- termTypeAsTerm res
  logForce $ "-----------------------------------"
  logForce $ "Mutation elaborated term is:\n" <> showPretty resterm

  -- let optimized = optimizeTLet res
  -- logForce $ "-----------------------------------"
  -- logForce $ "TLet optimized term is:\n" <> showPretty optimized

  return resterm


elaborateValue :: Scope -> LocProcDMTerm -> MTC (ImmutType , LocMoveType)
elaborateValue scname te = do
  (te1type) <- elaborateMut scname te
  case te1type of
    Statement _ _ _ -> demutationError $ "Expected term to be a value, but it was a statement:\n" <> showPretty te
    StatementWithoutDefault _ _ -> demutationError $ "Expected term to be a value, but it was a statement:\n" <> showPretty te
    Value it mt -> return (it , mt)
    MutatingFunctionEnd _ -> demutationError $ "Expected term to be a value, but it was a return."
    -- PurePhiTermType cond tt1 tt2 -> case (tt1, tt2) of
    --   ((Value Pure mt1,tt1), (Value Pure mt2,tt2)) -> pure $ (Pure, (PhiMove cond (mt1,tt1) (mt2,tt2)))
    --   other -> demutationError $ "Expected a term to be a value, but found an if statement where the branches had term types: " <> show other

elaboratePureValue :: Scope -> LocProcDMTerm -> MTC (LocMoveType)
elaboratePureValue scname te = do
  (te1type) <- elaborateMut scname te
  case te1type of
    Statement _ _ _   -> demutationError $ "Expected term to be a value, but it was a statement:\n" <> showPretty te
    StatementWithoutDefault _ _   -> demutationError $ "Expected term to be a value, but it was a statement:\n" <> showPretty te
    MutatingFunctionEnd _ -> demutationError $ "Expected term to be a value, but it was a return."
    Value Pure mt -> return (mt)
    Value _ mt    -> demutationError $ "Expected term to be a pure value, but it has type: " <> show mt
                                    <> "The term is:\n"
                                    <> showPretty te
    -- PurePhiTermType cond tt1 tt2 -> case (tt1, tt2) of
    --   ((Value Pure mt1,tt1), (Value Pure mt2,tt2)) -> pure $ (PhiMove cond (mt1,tt1) (mt2,tt2))
    --   other -> demutationError $ "Expected a term to be a value, but found an if statement where the branches had term types: " <> show other



-- make sure there are no Value or MutatingFunctionEnd inside the blocks
-- reverse the block statements
-- concatenate Statements blocks
-- determine the correct LastTerm for the concatenation result
makeTermList :: [TermType] -> MTC (LastValue, Maybe LocDemutDMTerm, [LocDemutDMTerm])

-- empty list
makeTermList [] = demutationError $ "Found an empty list of statements."

-- single element left
makeTermList (Value it mt : [])         = case it of
                                            Pure -> do mt' <- moveTypeAsTerm_Loc mt ; return (PureValue mt, Nothing, [mt'])
                                            _    -> demutationError $ "The last value of a block has the type " <> show it <> "\n"
                                                                    <> "Only pure values are allowed.\n"
                                                                    <> "The value is:\n"
                                                                    <> show mt
makeTermList (Statement l term last : []) = do last' <- (moveTypeAsTerm last) ; return (PureValue (Located l last), Just (Located l last'), [Located l term])
makeTermList (StatementWithoutDefault l term : []) = return (NoLastValue , Nothing, [Located l term])
-- makeTermList (PurePhiTermType cond (Value Pure mt1,tt1) (Value Pure mt2,tt2) : []) = return (PureValue [mt1,mt2] , Nothing, [Extra (DemutPhi cond tt1 tt2)])
-- makeTermList (PurePhiTermType cond _ _ : [])     = demutationError $ "Encountered a phi as last statement in a block, but the branches to do not have pure values as returns."
makeTermList (MutatingFunctionEnd _ : [])          = return (MutatingFunctionEndValue , Nothing, [])

-- more than one element left
makeTermList (Value _ mt : ts)          = demutationError $ "Found a value term " <> show mt <> " inside a list of statements."
makeTermList (Statement l term _ : ts)    = do (last, lastt, ts') <- makeTermList ts
                                               return (last, lastt, ts' <> [Located l term])
makeTermList (StatementWithoutDefault l term : ts)
                                        = do (last, lastt, ts') <- makeTermList ts
                                             return (last, lastt, ts' <> [Located l term])
makeTermList (MutatingFunctionEnd _ : ts) = demutationError $ "Found a MutatingFunctionEnd inside a list of statements."
-- makeTermList (PurePhiTermType cond v1 v2 : ts) = demutationError "Phis in the middle of a block are currently not implemented."

--
-- with actually appending
--
makeTermListAndAppend :: [TermType] -> MTC (LastValue, [LocDemutDMTerm])
makeTermListAndAppend ts = do
  (last, lastt, ts') <- makeTermList ts
  case lastt of
    Nothing -> return (last, ts')
    Just lastt -> return (last, lastt:ts')

--
-- only allow terms which would have an append,
-- but then cancel the appending. Such that we can
-- append something of our own. (needed in loop demutation)
-- 
makeTermListAndCancelAppend :: [TermType] -> MTC (LastValue, [LocDemutDMTerm])
makeTermListAndCancelAppend ts = do
  (last, lastt, ts') <- makeTermList ts
  case lastt of
    Nothing -> return (last, ts')
    Just lastt -> return (last, ts')

--
-- Here we allow moving return types
--
elaborateTopLevel :: Scope -> LocProcDMTerm -> MTC (TermType)
elaborateTopLevel scname (Located l (Extra (Block ts))) = do
  ts' <- mapM (elaborateMut scname) ts
  (last_val, ts'') <- makeTermListAndAppend ts'

  mt <- case last_val of
    PureValue mt -> return mt
    MutatingFunctionEndValue -> demutationError $ "Encountered a 'return' which is not the last statement of a function."
    NoLastValue              -> demutationError $ "Encountered a statement without last value in top level."

  -- case mt of
  --   NoMove pdt -> pure ()
  --   _ -> demutationError $ "Encountered a block which is not top level and not in a function, but has a move as return type. This is currently not allowed."

  return (Value Pure (Located l (NoMove (Extra (DemutBlock ts'')))))

elaborateTopLevel scname t = elaborateMut scname t


--
-- The main elaboration function
--
elaborateMut :: Scope -> LocProcDMTerm -> MTC (TermType)

elaborateMut scname term@(Located l (Extra (Block ts))) = do
  ts' <- mapM (elaborateMut scname) ts
  (last_val, ts'') <- makeTermListAndAppend ts'

  mt <- case last_val of
    PureValue (Located _ mt) -> return mt
    MutatingFunctionEndValue -> demutationError $ "Encountered a 'return' which is not the last statement of a function."
    NoLastValue -> demutationError $ "Encountered a statement which is not allowed to be the last one in a block.\n"
                                    <> "The statement is:\n"
                                    <> showPretty term


  case mt of
    NoMove _  -> pure ()
    _ -> demutationError $ "Encountered a block which is not top level and not in a function, but has a move as return type. This is currently not allowed."

  return (Value Pure (Located l (NoMove (Extra (DemutBlock ts'')))))
    
elaborateMut scname (Located l (Op op args)) = do
  args' <- mapM (elaboratePureValue scname) args
  args'' <- mapM moveTypeAsTerm_Loc args'
  pure (Value Pure (Located l (NoMove (Op op args''))))

elaborateMut scname (Located l (Sng η τ)) = do
  return (Value Pure (Located l (NoMove $ Sng η τ)))

elaborateMut scname (Located l (DMTrue)) = do
  return (Value Pure (Located l (NoMove $ DMTrue)))

elaborateMut scname (Located l (DMFalse)) = do
  return (Value Pure (Located l (NoMove $ DMFalse)))

elaborateMut scname term@(Located l (Var _)) = demutationError $ "Unsupported term: " <> showPretty term

elaborateMut scname (Located l (Extra (ProcVarTerm x))) = do
  mx <- expectNotMoved x
  itype <- expectImmutType scname x

  return (Value itype (Located l (SingleMove x)))

elaborateMut scname (Located l (Extra (ProcBBLet procx args))) = do

  -- write the black box into the scope with its type
  scope'  <- setImmutType scname procx PureBlackBox

  -- allocate a memory location
  memx <- allocateMem scname (Just procx)

  -- write it into the memctx
  setMem procx [(SingleMem memx)]

  tevarx <- procVarAsTeVar procx

  return (Statement l (Extra (DemutBBLet tevarx args)) (SingleMove procx))


elaborateMut scname (Located l (Extra (ProcSLetBase ltype x term))) = do
  (newTermType, Located l_moveType moveType) <- elaborateValue scname term

  case newTermType of
    Pure -> pure ()
    Mutating _ -> pure ()
    PureBlackBox     -> throwUnlocatedError (DemutationError $ "Found an assignment " <> show x <> " = " <> showPretty term <> " where RHS is a black box. This is not allowed.")

  moveType' <- (moveTypeAsTerm moveType)

  --
  -- move out of variables on the RHS, getting the memory
  -- locations, and the new allocations, then:
  --
  -- 1. set memory locations for variables on the LHS
  -- 2. generate terms for the memory allocations
  -- 
  (mem) <- moveGetMem scname (Just x) moveType
  setMem x mem

  x' <- procVarAsTeVar x

  -- write the immut type into the scope
  setImmutType scname x newTermType

  -- log what happened
  debug $ "[elaborateMut/SLetBase]: The variable " <> show x <> " is being assigned." 
  logmem <- use memCtx
  debug $ "The memctx is now:\n"
  debug $ show logmem


  return (Statement l (Extra (DemutSLetBase ltype x' (Located l_moveType moveType')))
          (SingleMove x))


--
--
-- Tuple terms
--
elaborateMut scname (Located l (Tup t1s)) = do
  --
  -- We need to make sure that everything put into
  -- the tuple is pure, as this is expected when we
  -- take those things out of the tuple again.
  --
  results <- mapM (elaboratePureValue scname) t1s
  --
  -- what we return is pure, and is a tuple move of the entries
  return $ Value Pure (Located l (TupleMove results))

--
-- TLets
--
elaborateMut scname fullterm@(Located l (Extra (ProcTLetBase ltype vars term))) = do
  --
  (newTermType, moveType) <- elaborateValue scname term
  --
  -- deal with itype
  --
  -- What we additionally assume is that elements of tuples
  -- are always pure. (TODO: We have to check this in tuple creation terms)
  --
  case newTermType of
    Pure -> pure ()
    Mutating ims -> throwUnlocatedError (DemutationError $ "Found a tuple assignment " <> show vars <> " = " <> showPretty term <> " where RHS is a mutating function. This is not allowed.")
    PureBlackBox -> throwUnlocatedError (DemutationError $ "Found an assignment " <> show vars <> " = " <> showPretty term <> " where RHS is a black box. This is not allowed.")
  --
  -- we set the immuttype of every element on the LHS to Pure
  --
  mapM (\x -> setImmutType scname x Pure) vars

  moveType' <- (moveTypeAsTerm_Loc moveType)

  -- get memory of the RHS
  mem <- moveGetMem_Loc scname Nothing moveType

  -- write the list of possible memory types into the
  -- variables of the lhs
  setMemTupleInManyMems scname vars mem

  demutTLetStatement l ltype vars moveType'



elaborateMut scname (Located l (Extra (ProcLamStar args ret body))) = do
  bodyscname <- appendNewScopeVar "lamstar" scname
  (newBody, newBodyType) <- elaborateLambda bodyscname [(v ::- x) | (v ::- (x , _)) <- args] body
  return (Value newBodyType (Located l (NoMove (LamStar [(UserTeVar v) :- x | (v ::- x) <- args] ret newBody))))

elaborateMut scname (Located l (Extra (ProcLam args ret body))) = do
  bodyscname <- appendNewScopeVar "lam" scname
  (newBody, newBodyType) <- elaborateLambda bodyscname [(v ::- x) | (v ::- x) <- args] body
  return (Value newBodyType (Located l (NoMove (Lam [(UserTeVar v) :- x | (v ::- x) <- args] ret newBody))))



elaborateMut scname (Located l (Extra (ProcFLet name term))) = do
  --
  -- Regarding MoveType: it is not possible to have terms
  -- where an flet is followed by something movable, i.e.
  -- a variable. Because FLets are only generated when they
  -- are actually followed by an (anonymous) function definition.
  -- Which means that we do not have to mark anything as moved here.
  --

  (newTermType, Located l_moveType moveType) <- elaborateValue scname term

  case newTermType of
    Pure -> pure ()
    Mutating _ -> pure ()
    PureBlackBox     -> internalError $ "Found a BlackBox term inside a BlackBox term, this should not be possible."

  term' <- case moveType of
                NoMove t -> return t
                _ -> internalError $ "got a move from the FLet body, this should not happen"

  -- create memory location for function name
  mem <- allocateMem scname (Just name)
  setMem name [(SingleMem mem)]

  -- write the immut type into the scope
  setImmutTypeFLetDefined scname name newTermType

  -- log what happened
  debug $ "[elaborateMut/FLetBase]: The function " <> show name <> " is being defined."
  logmem <- use memCtx
  debug $ "The memctx is now:\n"
  debug $ show logmem


  return (Statement l (Extra (DemutFLet (UserTeVar name) (Located l_moveType term'))) (SingleMove name))



elaborateMut scname term@(Located l (Apply f args)) = do
  --
  -- The MoveType of function applications is always `NoMove`,
  -- because we make sure in typechecking that functions can
  -- never return objects which are aliased with some pre-existing
  -- variable (of a type which would contain mutable references)
  --
  -- Thus the return value of a function is always "at a fresh memory location"
  -- and we do not need to mark anything as moved.
  --
  -- See #171 / #172.
  --

  -- typecheck the function f
  (itype , movetype) <- elaborateValue scname f

  --------
  -- 2 cases
  --
  case itype of
    --
    -- case I : A mutating function call
    --
    Mutating muts -> do
        -- make sure that there are as many arguments as the function requires
        case length muts == length args of
          True -> pure ()
          False -> throwUnlocatedError (DemutationError $ "Trying to call the function '" <> showPretty f <> "' with a wrong number of arguments.")

        let mutsToOtherMuts mut = case mut of
              Mutated -> MutatedArg
              NotMutated -> NotMutatedArg Pure

        let mutargs = zip (mutsToOtherMuts <$> muts) args
        (newArgs , muts) <- elaborateMutList (showPretty f) scname mutargs

        movetype' <- (moveTypeAsTerm_Loc movetype)
        let funcallterm = (Apply movetype' newArgs)

        -- the new term
        demutTLetStatement l PureLet muts (Located l (funcallterm))

    --
    -- case II : A pure function call
    --
    Pure -> do
        let mutargs = zip (repeat (NotMutatedArg Pure)) args
        (newArgs , muts) <- elaborateMutList (showPretty f) scname mutargs

        movetype' <- (moveTypeAsTerm_Loc movetype)
        let funcallterm = (Apply movetype' newArgs)

        -- the new term
        return $ Value Pure (Located l (NoMove funcallterm))

    --
    -- case III: A call to a pure black box
    --
    --   since #202 this is handled in the case for `BBApply`.
    --
    
    PureBlackBox -> demutationError $ "Trying to call a black box without `unbox_call` wrapper. In the term: " <> showPretty term



elaborateMut scname term@(Located l (Extra (ProcBBApply f args bbkind))) = do
  -- typecheck the function f
  (itype , movetype) <- elaborateValue scname f

  -- elaborate the bbkind
  bbkind' <- elaborateBBKind scname bbkind

  --------
  -- 2 cases
  --
  case itype of
    PureBlackBox -> do
        
        -- the global variables which are implicitly applied
        -- and need to be added to the `BBApply`
        glvars <- globalNames <$> (use topLevelInfo)

        -- since the box is pure, we say so to `elaborateMutList`
        let mutargs = zip (repeat (NotMutatedArg Pure)) args
        (newArgs , muts) <- elaborateMutList (showPretty f) scname mutargs

        movetype' <- (moveTypeAsTerm_Loc movetype)
        let glvars' = map UserTeVar glvars
        return $ Value Pure (Located l (NoMove (BBApply movetype' newArgs glvars' bbkind')))

    otherType -> demutationError $ "Trying to call a function of type " <> show otherType <> " with `unbox_call`. In the term " <> showPretty term



elaborateMut scname (Located l (Extra (ProcPreLoop iters iterVar body))) = do -- demutationError $ "Not implemented: loop." -- do
  debug $ "[elaborateMut/Loop] BEGIN ---------------------"


  -- first, elaborate the iters
  (newIters) <- elaboratePureValue scname iters
  newIters' <- moveTypeAsTerm_Loc newIters
  --
  -- add the iterator to the scope,
  -- and backup old type
  oldIterImmutType <- backupAndSetImmutType scname iterVar Pure
  --
  -- backup iter memory location, and create a new one
  oldIterMem <- getValue iterVar <$> use memCtx
  setMem iterVar =<< pure <$> SingleMem <$> allocateMem scname (Just iterVar)
  --
  -- backup the vactx
  vanames <- getAllKeys <$> use vaCtx
  --


  -------------------------------------------------
  -- 
  -- Body elaboration
  --
  --
  -- We can now elaborate the body, and thus get the actual list
  -- of modified variables.
  --
  -- For this, we keep track of the memctx. We look at which procvar assignments
  -- changed during the body, and those are the captures.
  -- Additionally we require that all changed procvars cannot contain memory locations
  -- which were in use before the loop body.
  -- 
  memsBefore <- use memCtx
  mutsBefore <- use mutCtx
  (lastVal, bodyTerms) <- elaborateAsListAndCancelAppend scname body
  memsAfter <- use memCtx
  mutsAfter <- use mutCtx
  --
  --
  debug $ "----"
  debug $ "memctx before:\n"
  debug $ show memsBefore
  debug $ "----"
  debug $ "memctx after:\n"
  debug $ show memsAfter
  --
  --
  -- get all procvars in `memsAfter` which are different from `memsBefore` (or new).
  let isChangedOrNew (k,v0) = case getValue k memsBefore of
        Nothing -> True
        Just v1 | v0 == v1  -> False
        Just v1 | otherwise -> True
  let newMems = filter isChangedOrNew (getAllKeyElemPairs memsAfter)
  --
  -- get all memory vars used before, and make sure that
  -- they are not used in the new vars.
  let oldMemVars = getAllElems memsBefore >>= getAllMemVarsOfMemState
  let newMemVars = (snd <$> newMems) >>= getAllMemVarsOfMemState
  case newMemVars `intersect` oldMemVars of
    [] -> pure ()
    xs -> throwUnlocatedError $ DemutationMovedVariableAccessError $ "Found a loop body which moves variables around.\n"
                          <> "The following variables are changed and contain memory locations from before: " <> show xs <> "\n"
                          <> "Since this means that we cannot track what actually happens in the case of an unknown number of iterations,\n"
                          <> "this is not allowed.\n"
                          <> "\n"
                          <> "Loop body:\n"
                          <> showPretty body
  --
  -- The captures are the list of variables whoose mem changed.
  -- For this we do almost the same as for `newMems`, except that we
  -- do not want the procvars which were newly created in the body,
  -- since these are body-local, and freshly assigned in each iteration. 
  --
  -- TODO: This is only correct in non-mutating loops!
  --       In mutating ones, the mutated variables are also captures!
  --
  let isChanged (k,v0) = case getValue k memsAfter of
        -- 
        -- this case should actually not occur, since the variable `k` cannot simply disappear
        Nothing -> undefined
        -- 
        -- case 1: mem_after = mem_before,
        --   then we have to check whether the mem location was
        --   mutated (if the mem is a single_mem)
        Just v1 | v0 == v1  -> do
          case v1 of
            MemExists mts -> do
              let single_mems = [m | SingleMem m <- mts]
              let isChanged m = case (getValue m mutsBefore, getValue m mutsAfter) of {
                    (Just ma, Just ma') -> pure $ not $ ma == ma'
                    ; (ma, ma')         -> internalError $ "Did not expect the mutctx to have no entry for: " <> show v1
                    }
              mems_changed <- mapM isChanged single_mems
              return $ any (== True) mems_changed
            MemMoved      -> return False
        --
        -- case 2: mem_after /= mem_before,
        --   then obviously something changed,
        --   so this is a capture
        Just v1 | otherwise -> return True

  captureMems <- filterM isChanged (getAllKeyElemPairs memsBefore)
  capturesBefore <- mapM (procVarAsTeVarInMutCtx memsBefore mutsBefore) $ fst <$> captureMems
  capturesAfter  <- mapM (procVarAsTeVarInMutCtx memsAfter mutsAfter)  $ fst <$> captureMems
  --
  -- We have to add the capture assignment and the capture return
  -- to the body. Note that the order of `bodyTerms` is already
  -- reversed, hence the reversed appending.
  captureVar <- newTeVarOfMut "loop_capture" Nothing
  let s1 = "capture reading in loop body" 
  let s2 = "capture returning in loop body" 
  let capture_assignment   = ld s1 l $ Extra (DemutTLetBase PureLet capturesBefore (ld s1 l (Var captureVar)))
  let capture_return       = ld s2 l $ Tup [ld s2 l (Var v) | v <- capturesAfter]
  let demutated_body_terms = [capture_return] <> bodyTerms <> [capture_assignment]
  let demutated_loop = Extra (DemutLoop (newIters') capturesBefore capturesAfter ((UserTeVar iterVar, captureVar))
                             (Located l $ Extra (DemutBlock demutated_body_terms)))

  --
  ------------------------------------------------

  debug $ "----"
  debug $ "capture mems:\n"
  debug $ show captureMems


  ------------------------------------------------
  -- Restore the backups / apply appropriate diffs
  --
  -- After the body was elaborated, it might be that we have new
  -- variables in scope which are only local in the body
  -- What we do is we filter the VA(Ctx) to only contain the vars
  -- which were in it before the body was checked
  --
  let deleteIfNotOld k ctx = case k `elem` vanames of
                              True  -> ctx
                              False -> deleteValue k ctx
  vaCtx %= (\ctx -> foldr (\k ctx -> deleteIfNotOld k ctx) ctx (getAllKeys ctx))
  --
  -- restore old iter memory location,
  -- if there was something
  --
  case (oldIterMem) of
    (Just a) -> memCtx %= (setValue iterVar a)
    _ -> pure ()


  debug $ "[elaborateMut/Loop] END -----------------------"
  --
  -- Note: We do not build the tlet which belongs to a loop here
  --       This is done later in unblocking.
  return (StatementWithoutDefault l demutated_loop)

elaborateMut scname (Located l (Extra (ProcReturn))) = return $ MutatingFunctionEnd l

elaborateMut scname term@(Located l (Extra (ProcPhi cond tr fs))) = do
  ---------------------------------
  --
  -- elaborate the condition
  --
  cond' <- moveTypeAsTerm_Loc =<< elaboratePureValue scname cond

  ---------------------------------
  --
  -- backup the contexts
  --
  vaCtxBefore  <- use vaCtx
  mutCtxBefore <- use mutCtx
  memCtxBefore <- use memCtx

  ---------------------------------
  --
  -- Elaborate the if branches as lists
  --   We have to make sure that they do not contain return statements,
  --   so we check this using the `lastValue`
  --
  -------------
  -- Branch 1:
  --
  trTerms <- do
    (l_tr, (trLastVal,trLast,trTerms)) <- elaborateAsList scname tr
    case (trLastVal,trLast) of
      (MutatingFunctionEndValue,_) -> demutationError $ "Ifs cannot contain `return` statements.\n"
                                                  <> "In the term:\n"
                                                  <> showPretty term
      (PureValue mt, Just defaulval) -> pure (StatementBranch l_tr trTerms)
      (NoLastValue, _)               -> pure (StatementBranch l_tr trTerms)
      (PureValue mt, Nothing)        -> pure (ValueBranch l_tr trTerms mt)
  --
  -- save the mut and mem ctxs, since we need to know
  -- which assignments / mutations happened in either branch.
  mutCtxAfter1 <- use mutCtx
  memCtxAfter1 <- use memCtx
  --
  -- 
  -------------
  -- Branch 2:
  --
  -- Here we first have to reset the state to its original state.
  cleanupVACtxAfterScopeEnd vaCtxBefore
  mutCtx .= mutCtxBefore
  memCtx .= memCtxBefore
  --
  -- Now do the actual elaboration of this branch
  fsTerms <- do
    case fs of
      Nothing  -> pure (StatementBranch (downgradeToRelated "Empty branch of if without else part" l) [])
      Just fs -> do
        (l_fs, (fsLastVal,fsLast,fsTerms)) <- elaborateAsList scname fs
        case (fsLastVal,fsLast) of
          (MutatingFunctionEndValue,_) -> demutationError $ "Ifs cannot contain `return` statements.\n"
                                                      <> "In the term:\n"
                                                      <> showPretty term
          (PureValue mt, Just defaulval) -> pure (StatementBranch l_fs fsTerms)
          (NoLastValue, _)               -> pure (StatementBranch l_fs fsTerms)
          (PureValue mt, Nothing)        -> pure (ValueBranch l_fs fsTerms mt)
  --
  -- Again save mem / mut after second branch
  mutCtxAfter2 <- use mutCtx
  memCtxAfter2 <- use memCtx
  --
  ------------

  ---------------------------------
  --
  -- Compute the resulting contexts
  --
  let memCtxAfter = memCtxAfter1 ⋆! memCtxAfter2
  memCtx .= memCtxAfter
  (mutCtxAfter, (proj1, proj2)) <- coequalizeMutCtx mutCtxAfter1 mutCtxAfter2
  mutCtx .= mutCtxAfter
  cleanupVACtxAfterScopeEnd vaCtxBefore

  ---------------------------------
  --
  -- Return the resulting term type
  case (trTerms, fsTerms) of
    --
    -- case 1: statement branches
    --
    (StatementBranch l_tr trTerms, StatementBranch l_fs fsTerms) -> do
      let trTerms' = (Located l_tr (Extra (DemutBlock (proj1 <> trTerms))))
      let fsTerms' = (Located l_fs (Extra (DemutBlock (proj2 <> fsTerms))))

      return (StatementWithoutDefault l (Extra (DemutPhi cond' trTerms' fsTerms')))

    --
    -- case 2: value branches
    --
    (ValueBranch l_tr trTerms trMoves, ValueBranch l_fs fsTerms fsMoves) -> case (proj1,proj2) of
      ([],[]) -> return (Value Pure (Located l (PhiMove cond' (trMoves, (Located l_tr (Extra (DemutBlock trTerms)))) (fsMoves, (Located l_fs (Extra (DemutBlock fsTerms)))))))
      (proj1,proj2) -> demutationError $ "Found an if with branches of value-type, in such ifs mutation is not allowed."

    --
    -- error case: mixed branches
    --
    branchTypes -> demutationError $ "Found an if where the branch types differ: " <> show branchTypes



-- Special builtins
elaborateMut scname (Located l (MutPFoldRows t1 t2 t3 t4))   = do

  (argTerms, mutVars) <- elaborateMutList "pfoldrows!" scname [(NotMutatedArg (Mutating [NotMutated, NotMutated, Mutated]) , t1), (MutatedArg , t2), (NotMutatedArg Pure, t3), (NotMutatedArg Pure, t4)]
  case argTerms of
    [newT1, newT2, newT3, newT4] -> demutTLetStatement l PureLet mutVars (Located l (MutPFoldRows newT1 newT2 newT3 newT4))
    _ -> internalError ("Wrong number of terms after elaborateMutList")






----
-- Demutation of vector / matrix likes
--
-- We return the type `SingleRef`, as that is not allowed
-- to be passed in mutating positions, which is important
-- since the results of these functions are aliased references
-- to matrices.
--
-- See #183.
--

elaborateMut scname (Located l (Index t1 t2 t3)) = elaborateRefMove3 scname l Index t1 t2 t3
elaborateMut scname (Located l (VIndex t1 t2))   = elaborateRefMove2 scname l VIndex t1 t2
elaborateMut scname (Located l (Row t1 t2))      = elaborateRefMove2 scname l Row t1 t2

----
-- the mutating builtin cases

elaborateMut scname (Located l (MutSubGrad t1 t2)) = do
  (argTerms, mutVars) <- elaborateMutList "subgrad" scname [(MutatedArg , t1), (NotMutatedArg Pure , t2)]
  case argTerms of
    [newT1, newT2] -> demutTLetStatement l PureLet mutVars (Located l (MutSubGrad newT1 newT2))
    _ -> internalError ("Wrong number of terms after elaborateMutList")

elaborateMut scname (Located l (ScaleGrad scalar grads)) = do
  (argTerms, mutVars) <- elaborateMutList "scalegrad" scname [(NotMutatedArg Pure , scalar), (MutatedArg , grads)]
  case argTerms of
    [newT1, newT2] -> demutTLetStatement l PureLet mutVars (Located l (ScaleGrad newT1 newT2))
    _ -> internalError ("Wrong number of terms after elaborateMutList")

elaborateMut scname (Located l (MutClipM c t)) = do
  (argTerms, mutVars) <- elaborateMutList "clip" scname [(MutatedArg , t)]
  case argTerms of
    [newT] -> demutTLetStatement l PureLet mutVars (Located l (MutClipM c newT))
    _ -> internalError ("Wrong number of terms after elaborateMutList")

elaborateMut scname (Located l (MutGauss t1 t2 t3 t4)) = do
  (argTerms, mutVars) <- elaborateMutList "gauss" scname [(NotMutatedArg Pure , t1), (NotMutatedArg Pure , t2), (NotMutatedArg Pure , t3), (MutatedArg , t4)]
  case argTerms of
    [newT1, newT2, newT3, newT4] -> demutTLetStatement l PureLet mutVars (Located l (Gauss newT1 newT2 newT3 newT4))
    _ -> internalError ("Wrong number of terms after elaborateMutList")

elaborateMut scname (Located l (MutLaplace t1 t2 t3)) = do
  (argTerms, mutVars) <- elaborateMutList "laplace" scname [(NotMutatedArg Pure , t1), (NotMutatedArg Pure , t2), (MutatedArg , t3)]
  case argTerms of
    [newT1, newT2, newT3] -> demutTLetStatement l PureLet mutVars (Located l (Laplace newT1 newT2 newT3))
    _ -> internalError ("Wrong number of terms after elaborateMutList")

elaborateMut scname (Located l (MutConvertM t1)) = do
  (argTerms, mutVars) <- elaborateMutList "convert" scname [(MutatedArg , t1)]
  case argTerms of
    [newT1] -> demutTLetStatement l PureLet mutVars (Located l (MutConvertM newT1))
    _ -> internalError ("Wrong number of terms after elaborateMutList")


elaborateMut scname (Located l (InternalMutate t1)) = do
  (argTerms, mutVars) <- elaborateMutList "internal_mutate" scname [(MutatedArg , t1)]
  case argTerms of
    [newT1] -> demutTLetStatement l PureLet mutVars (Located l (InternalMutate newT1))
    _ -> internalError ("Wrong number of terms after elaborateMutList")

--
--
-- The non mutating builtin cases
-- ------------------------------
--

elaborateMut scname (Located l (MCreate t1 t2 t3 t4))     = elaborateNonMut3 scname l (\tt1 tt2 tt4 -> MCreate tt1 tt2 t3 tt4) t1 t2 t4
elaborateMut scname (Located l (Transpose t1))            = elaborateNonMut1 scname l Transpose t1
elaborateMut scname (Located l (Disc t1))                 = elaborateNonMut1 scname l Disc t1
elaborateMut scname (Located l (Size t1))                 = elaborateNonMut1 scname l Size t1
elaborateMut scname (Located l (Length t1))               = elaborateNonMut1 scname l Length t1
elaborateMut scname (Located l (ZeroGrad t1))             = elaborateNonMut1 scname l ZeroGrad t1
elaborateMut scname (Located l (SumGrads t1 t2))          = elaborateNonMut2 scname l SumGrads t1 t2
elaborateMut scname (Located l (SubGrad t1 t2))           = elaborateNonMut2 scname l SubGrad t1 t2
elaborateMut scname (Located l (Sample t1 t2 t3))         = elaborateNonMut3 scname l Sample t1 t2 t3
elaborateMut scname (Located l (InternalExpectConst t1))  = elaborateNonMut1 scname l InternalExpectConst t1
elaborateMut scname (Located l (Clone t1))                = elaborateNonMut1 scname l Clone t1
elaborateMut scname (Located l (ClipM c t1))              = elaborateNonMut1 scname l (ClipM c) t1
elaborateMut scname (Located l (ConvertM  t1))            = elaborateNonMut1 scname l ConvertM t1
elaborateMut scname (Located l (Gauss t1 t2 t3 t4))       = elaborateNonMut4 scname l Gauss t1 t2 t3 t4
elaborateMut scname (Located l (Laplace t1 t2 t3))        = elaborateNonMut3 scname l Laplace t1 t2 t3
elaborateMut scname (Located l (AboveThresh t1 t2 t3 t4)) = elaborateNonMut4 scname l AboveThresh t1 t2 t3 t4
elaborateMut scname (Located l (Exponential t1 t2 t3 t4)) = elaborateNonMut4 scname l Exponential t1 t2 t3 t4
elaborateMut scname (Located l (ClipN t1 t2 t3))          = elaborateNonMut3 scname l ClipN t1 t2 t3
elaborateMut scname (Located l (Count t1 t2))             = elaborateNonMut2 scname l Count t1 t2
elaborateMut scname (Located l (MakeVec t1))              = elaborateNonMut1 scname l MakeVec t1
elaborateMut scname (Located l (MakeRow t1))              = elaborateNonMut1 scname l MakeRow t1
elaborateMut scname (Located l (MMap t1 t2))              = elaborateNonMut2 scname l MMap t1 t2
elaborateMut scname (Located l (MapRows t1 t2))           = elaborateNonMut2 scname l MapRows t1 t2
elaborateMut scname (Located l (MapRows2 t1 t2 t3))       = elaborateNonMut3 scname l MapRows2 t1 t2 t3
elaborateMut scname (Located l (MapCols t1 t2))           = elaborateNonMut2 scname l MapCols t1 t2
elaborateMut scname (Located l (MapCols2 t1 t2 t3))       = elaborateNonMut3 scname l MapCols2 t1 t2 t3
elaborateMut scname (Located l (PReduceCols t1 t2))       = elaborateNonMut2 scname l PReduceCols t1 t2
elaborateMut scname (Located l (PFoldRows t1 t2 t3 t4))   = elaborateNonMut4 scname l PFoldRows t1 t2 t3 t4
elaborateMut scname (Located l (MFold t1 t2 t3))          = elaborateNonMut3 scname l MFold t1 t2 t3


-- the unsupported terms
elaborateMut scname term@(Located l (Choice t1))        = throwUnlocatedError (UnsupportedError ("When mutation-elaborating:\n" <> showPretty term))
elaborateMut scname term@(Located l (Loop t1 t2 t3 t4)) = throwUnlocatedError (UnsupportedError ("When mutation-elaborating:\n" <> showPretty term))
elaborateMut scname term@(Located l (TProject t1 t2))   = throwUnlocatedError (UnsupportedError ("When mutation-elaborating:\n" <> showPretty term))
elaborateMut scname term@(Located l (Arg x a b))        = throwUnlocatedError (UnsupportedError ("When mutation-elaborating:\n" <> showPretty term))
elaborateMut scname term@(Located l (Ret t1))           = throwUnlocatedError (UnsupportedError ("When mutation-elaborating:\n" <> showPretty term))


elaborateMut scname term@_    = throwUnlocatedError (UnsupportedError ("When mutation-elaborating:\n" <> showPretty term))


------------------------------------------------------
-- elaboration helpers
--

-- non mutating
elaborateNonMut1 :: Scope -> SourceLocExt -> (LocDemutDMTerm -> DemutDMTerm) -> (LocProcDMTerm -> MTC TermType)
elaborateNonMut1 scname l ctr = elaborateHelper1 scname l (NoMove . ctr)
elaborateNonMut2 scname l ctr = elaborateHelper2 scname l (((.).(.)) NoMove ctr)
elaborateNonMut3 scname l ctr = elaborateHelper3 scname l (((.).(.).(.)) NoMove ctr)
elaborateNonMut4 scname l ctr = elaborateHelper4 scname l (((.).(.).(.).(.)) NoMove ctr)

-- refMove
elaborateRefMove1 :: Scope -> SourceLocExt -> (LocDemutDMTerm -> DemutDMTerm) -> (LocProcDMTerm -> MTC TermType)
elaborateRefMove1 scname l ctr = elaborateHelper1 scname l (RefMove . ctr)
elaborateRefMove2 scname l ctr = elaborateHelper2 scname l (((.).(.)) RefMove ctr)
elaborateRefMove3 scname l ctr = elaborateHelper3 scname l (((.).(.).(.)) RefMove ctr)
elaborateRefMove4 scname l ctr = elaborateHelper4 scname l (((.).(.).(.).(.)) RefMove ctr)

elaborateHelper1 :: Scope -> SourceLocExt -> (LocDemutDMTerm -> MoveType) -> LocProcDMTerm -> MTC TermType
elaborateHelper1 scname l ctr t1 = do
  (newT1) <- moveTypeAsTerm_Loc =<< elaboratePureValue scname (t1)
  return (Value Pure (Located l (ctr newT1)))


elaborateHelper2 :: Scope
                    -> SourceLocExt
                    -> (LocDemutDMTerm -> LocDemutDMTerm -> MoveType)
                    -> LocProcDMTerm -> LocProcDMTerm
                    -> MTC TermType
elaborateHelper2 scname l ctr t1 t2 = do
  (newT1) <- moveTypeAsTerm_Loc =<< elaboratePureValue scname ((t1))
  (newT2) <- moveTypeAsTerm_Loc =<< elaboratePureValue scname ((t2))
  return (Value Pure (Located l (ctr newT1 newT2)))


elaborateHelper3 :: Scope
                    -> SourceLocExt
                    -> (LocDemutDMTerm -> LocDemutDMTerm -> LocDemutDMTerm -> MoveType)
                    -> LocProcDMTerm -> LocProcDMTerm -> LocProcDMTerm
                    -> MTC TermType
elaborateHelper3 scname l ctr t1 t2 t3 = do
  (newT1) <- moveTypeAsTerm_Loc =<< elaboratePureValue scname t1
  (newT2) <- moveTypeAsTerm_Loc =<< elaboratePureValue scname t2
  (newT3) <- moveTypeAsTerm_Loc =<< elaboratePureValue scname t3
  return (Value Pure (Located l (ctr newT1 newT2 newT3)))


elaborateHelper4 :: Scope
                    -> SourceLocExt
                    -> (LocDemutDMTerm -> LocDemutDMTerm -> LocDemutDMTerm -> LocDemutDMTerm -> MoveType)
                    -> LocProcDMTerm -> LocProcDMTerm -> LocProcDMTerm -> LocProcDMTerm
                    -> MTC TermType
elaborateHelper4 scname l ctr t1 t2 t3 t4 = do
  (newT1) <- moveTypeAsTerm_Loc =<< elaboratePureValue scname t1
  (newT2) <- moveTypeAsTerm_Loc =<< elaboratePureValue scname t2
  (newT3) <- moveTypeAsTerm_Loc =<< elaboratePureValue scname t3
  (newT4) <- moveTypeAsTerm_Loc =<< elaboratePureValue scname t4
  return (Value Pure (Located l (ctr newT1 newT2 newT3 newT4)))


---------------------------------------------------
-- list elaboration

elaborateAsList :: Scope -> LocProcDMTerm -> MTC (SourceLocExt, (LastValue, Maybe LocDemutDMTerm, [LocDemutDMTerm]))
elaborateAsList scname (Located l (Extra (Block ts))) = do
  ts' <- mapM (elaborateMut scname) ts
  res <- makeTermList ts'
  return (l, res)
elaborateAsList scname (Located l t) = do
  t' <- elaborateMut scname (Located l t)
  res <- makeTermList [t']
  return (l,res)

elaborateAsListAndAppend :: Scope -> LocProcDMTerm -> MTC (SourceLocExt, (LastValue, [LocDemutDMTerm]))
elaborateAsListAndAppend scname (Located l (Extra (Block ts))) = do
  ts' <- mapM (elaborateMut scname) ts
  res <- makeTermListAndAppend ts'
  return (l, res)
elaborateAsListAndAppend scname t@(Located l _) = do
  t' <- elaborateMut scname t
  res <- makeTermListAndAppend [t']
  return (l, res)


elaborateAsListAndCancelAppend :: Scope -> LocProcDMTerm -> MTC (LastValue, [LocDemutDMTerm])
elaborateAsListAndCancelAppend scname (Located l (Extra (Block ts))) = do
  ts' <- mapM (elaborateMut scname) ts
  makeTermListAndCancelAppend ts'
elaborateAsListAndCancelAppend scname t = do
  t' <- elaborateMut scname t
  makeTermListAndCancelAppend [t']

---------------------------------------------------
-- bbkind elaboration

elaborateBBKind :: Scope -> BBKind ProceduralExtension -> MTC (BBKind DemutatedExtension)
elaborateBBKind scname = \case
  BBSimple jt -> return $ BBSimple jt
  BBVecLike jt pdt -> do
    pdt' <- moveTypeAsTerm_Loc =<< elaboratePureValue scname pdt
    return $ BBVecLike jt pdt'
  BBMatrix jt pdt1 pdt2 -> do
    pdt1' <- moveTypeAsTerm_Loc =<< elaboratePureValue scname pdt1
    pdt2' <- moveTypeAsTerm_Loc =<< elaboratePureValue scname pdt2
    return $ BBMatrix jt pdt1' pdt2'


---------------------------------------------------
-- recurring utilities


-------------
-- elaborating a lambda term
--

elaborateLambda :: Scope -> [ProcAsgmt JuliaType] -> LocProcDMTerm -> MTC (LocDemutDMTerm , ImmutType)
elaborateLambda scname args body = do
  --
  -- Regarding Movetypes: We do not need to do anything here
  -- about them, because we make sure in typechecking that
  -- the return value of a function needs to be copied,
  -- if it is of a type containing references.
  -- Thus the move type of the body is irrelevant.
  --
  -- See #171.
  --


  -- 
  -- NO. Different since #185.
  -- ## First, backup the VA-Ctx to be able to restore those
  -- ## variables which have the same name as our arguments
  -- ##
  -- ## See https://github.com/DiffMu/DiffPrivacyInferenceHs/issues/148#issuecomment-1004950955
  -- ##
  -- ## Then, mark all function arguments as "SingleRead" and "Pure"
  -- ## for the current scope.
  oldMemCtx <- use memCtx
  oldVaCtx <- use vaCtx
  mapM (\x -> setImmutTypeOverwritePrevious scname x Pure) [a | (a ::- _) <- args]
  -- ##
  -- END NO.
  --
  -- Allocate new memory for the arguments.
  let arghint (x ::- _) = Just x
  argmvs <- mapM (allocateMem scname) (arghint <$> args)

  -- assign memory to variables
  mapM (\(x ::- _,a) -> setMem x [SingleMem a]) (zip args argmvs)



  --------------------
  --
  -- check the body
  --
  (l, (lastValue, new_body_terms)) <- elaborateAsListAndAppend scname body
  --
  -- find out which mem vars have been mutated
  --
  () <- do
    memctx <- use memCtx
    mutctx <- use mutCtx
    logForce $ ""
    logForce $ "[elaborateLambda]"
    logForce $ "memCtx:\n" <> show memctx
    logForce $ ""
    logForce $ "mutCtx:\n" <> show mutctx
    logForce $ ""
    return ()
  --
  (mutated_argmvs, mut_states) <- do
    muts <- mapM getMemVarMutationStatus argmvs
    let toMutRes [] = NotMutated
        toMutRes _  = Mutated

    let mutStates = [(s,t) | (s,(t:ts)) <- muts]

    let toTeVar (NotSplit, (t:ts)) = pure (Just t)
        toTeVar (NotSplit, [])     = pure Nothing
        toTeVar (Split as, (t:ts)) = throwUnlocatedError $ DemutationSplitMutatingArgumentError $ "While demutating a function definition, encountered the case that an argument memory location was split. This is not allowed"
        toTeVar (Split as, []) = do
          -- if a var was split, we check recursively if
          -- its parts have been mutated.
          let f a = do
                      partTerms <- toTeVar =<< getMemVarMutationStatus a
                      case partTerms of
                        Just _ -> throwUnlocatedError $ DemutationSplitMutatingArgumentError "Part of a split function argument was mutated. This is currently not allowed"
                        Nothing  -> pure ()

          mapM f as
          return Nothing

    mutTeVars <- mapM toTeVar muts
    let mutTeVars' = [v | Just v <- mutTeVars]
    return (mutTeVars', toMutRes <$> snd <$> muts)

  --
  --------------------


  ------------------------------
  -- Compute the elaborated function body
  --
  --   For this we look at the mutated memvars and the last value of the body,
  --   and if required append a statement which either returns the default value,
  --   or returns the tuple of mutated args.
  --
  --   See #190.
  --
  --
  (itype, full_body) <- case (lastValue, mutated_argmvs) of
    --
    -- case I: a pure function
    --
    (PureValue as, []) -> do
      --
      -- We lookup the proc vars of the move,
      -- and check that they do not contain memory
      -- locations which are function inputs.
      --
      debug $ "[elaborateLambda] pure function. move type: " <> show as
      debug $ "   movedVars: " <> show (movedVarsOfMoveType_Loc as) <> ", mutated_argmvs: " <> show mutated_argmvs
      --
      memTypesOfMove <- mapM expectNotMoved (movedVarsOfMoveType_Loc as)
      let memVarsOfMove = join memTypesOfMove >>= getAllMemVars
      --
      case memVarsOfMove `intersect` argmvs of
        [] -> pure ()
        pvs ->   demutationError $ "Found a function which passes through a reference given as input. This is not allowed.\n"
                                      <> "The function body is:\n" <> showPretty body <> "\n"
                                      <> "The passed through memory references are: " <> show pvs

      return $ (Pure, Extra $ DemutBlock new_body_terms)


    --
    -- case II: not allowed
    --
    (PureValue as, xs) -> demutationError $ "Found a function which is mutating, but does not have a 'return'. This is not allowed."
                                        <> "\nThe function body is:\n" <> showPretty body
    --
    -- case III: not allowed
    --
    (MutatingFunctionEndValue, []) -> demutationError $ "Found a function which is not mutating, but has a 'return'. This is not allowed."
                                                    <> "\nThe function body is:\n" <> showPretty body

    --
    -- case IV: mutating function
    --
    (MutatingFunctionEndValue, mvs) -> do
      let s1 = "Auto generated return tuple (or single value) of mutating function"
      let last_tuple = case mvs of
              [v] -> Var (v)
              vs  -> Tup [(Located (RelatedLoc s1 l) (Var (v))) | v <- mvs]
      return (Mutating mut_states, Extra (DemutBlock ((Located (downgradeToRelated s1 l) (last_tuple)) : new_body_terms)))

    (NoLastValue, _) -> demutationError $ "Found a function which has no last value, that is not allowed."
                                          <> "\nThe function body is:\n" <> showPretty body



  ------------------------------
  -- Restoration of state
  --

  --
  -- restore memctx,
  --   we simply take the old one,
  --   as all memory allocations which happened
  --   in the lambda should have no effect on outside.
  --
  memCtx .= oldMemCtx

  --  
  -- delete all memory variables for this scope from the mutctx
  --
  cleanupMem scname

  --
  -- Restore old VA state for all args
  -- (https://github.com/DiffMu/DiffPrivacyInferenceHs/issues/148#issuecomment-1004950955)
  --
  vactxBeforeRestoration <- use vaCtx
  let restoreArg procvar = do
        case getValue procvar oldVaCtx of
          Nothing -> vaCtx %%= (\ctx -> ((), deleteValue procvar ctx))
          Just (oldvalue) -> vaCtx %%= (\ctx -> ((), setValue procvar (oldvalue) ctx))
  mapM restoreArg [a | (a ::- _) <- args]
  --
  -----------


  return ((Located l (full_body)), itype)


-------------
-- elaborating a list of terms which are used in individually either mutating, or not mutating places
--

elaborateMutList :: String -> Scope -> [(MutationArgumentType , LocProcDMTerm)] -> MTC ([LocDemutDMTerm] , [ProcVar])
elaborateMutList f scname mutargs = do
  ---------------------------------------
  -- Regarding MoveTypes (#171)
  --
  -- Since functions make sure that they do not reassign terms
  -- passed in at non-mutating argument positions, the movetype 
  -- of these terms is irrelevant.
  -- The "movetype" of terms in mutating argument positions is easy:
  -- It needs to be a SingleArg term, thus we do not really need
  -- to look into the official `MoveType`.
  --

  -- function for typechecking a single argument
  let checkArg :: (MutationArgumentType , LocProcDMTerm) -> MTC (LocDemutDMTerm , LocMoveType, Maybe (ProcVar))
      checkArg (MutatedArg , (Located l (arg))) = do
        -- if the argument is given in a mutable position,
        -- it _must_ be a var
        case arg of
          Extra (ProcVarTerm (x)) -> do 
            -- say that this variable is being reassigned (VAT)
            setImmutType scname x Pure

            -- the elaborated value of x
            -- (this needs to be done before `markMutated` is called)
            x' <- (procVarAsTeVar x)

            -- get the memvar of this tevar from the memctx
            -- and say that the memory location is mutated
            markMutated x

            return ((Located l (Var (x'))), (Located l (SingleMove x)), Just x)

          -- if argument is not a var, throw error
          _ -> throwUnlocatedError (DemutationError $ "When calling the mutating function " <> f <> " found the term " <> showPretty arg <> " as argument in a mutable-argument-position. Only variables are allowed here.")

      checkArg (NotMutatedArg reqty , arg) = do
        -- if the argument is given in an immutable position,
        -- we allow to use the full immut checking
        (itype , movetype) <- elaborateValue scname arg

        -- we require the argument to be of the right type
        case itype == reqty of
          True -> pure ()
          False -> demutationError $ "While checking the argument " <> show arg <> " of the function " <> f <> ":"
                                    <> "Expected it to have demutation type " <> show reqty
                                    <> "But found type " <> show itype

        movetype' <- moveTypeAsTerm_Loc movetype

        return (movetype' , movetype , Nothing)


  -- check them
  newArgsWithMutTeVars <- mapM checkArg mutargs

  ------------------------- 
  -- extract for return
  --
  -- these types of the arguments carry the contained "possibly aliased variable names"
  let newArgs = [te | (te , _ , _) <- newArgsWithMutTeVars]
  let argTypes = [ty | (_ , ty, _) <- newArgsWithMutTeVars]
  let mutVars = [m | (_ , _ , Just m) <- newArgsWithMutTeVars]


  --
  -- Make sure that all variables in mutated argument positions are not aliased.
  -- For this we look at the types of the inputs.
  --
  -- See #95
  --
  let getPossiblyAliasedVars a = freeVarsOfProcDMTerm a


  -- Counting how many vars with a given name there are
  let addCount :: (ProcVar) -> Ctx ProcVar Int -> Ctx ProcVar Int
      addCount var counts = case getValue var counts of
                              Just a -> setValue var (a P.+ 1) counts
                              Nothing -> setValue var 1 counts

  -- number of occurences of all variables
  let varcounts = getAllKeyElemPairs $ foldr addCount def (getPossiblyAliasedVars =<< ((getLocated . snd) <$> mutargs))
  -- number of occurences of all variables, but only for variables which are mutated
  let mutvarcounts = filter (\(k,n) -> k `elem` (mutVars)) varcounts
  -- number of occurences of all variables, but only for variables which are mutated, with occurence > 1
  let wrongVarCounts = filter (\(k,n) -> n > 1) mutvarcounts

  -- make sure that such variables do not occur
  case wrongVarCounts of
    [] -> return ()
    xs -> throwUnlocatedError $ DemutationNonAliasedMutatingArgumentError
                     $ "The function '" <> f <> "' is called with the following vars in mutating positions:\n\n"
                        <> showvarcounts mutvarcounts <> "\n"
                        <> "But it is not allowed to have the same variable occur multiple times "
                        where showvarcounts ((name,count):rest) = " - variable `" <> show name <> "` occurs " <> show count <> " times." <> "\n"
                                                                  <> showvarcounts rest
                              showvarcounts [] = ""

  return (newArgs, mutVars)


{-
------------------------------------------------------------
-- preprocessing a for loop body

runPreprocessLoopBody :: Scope -> Maybe TeVar -> ProcDMTerm -> MTC (ProcDMTerm, [TeVar])
runPreprocessLoopBody scope iter t = do
  (a,x) <- runStateT (preprocessLoopBody scope iter t) def
  return (a, nub x)

-- | Walks through the loop term and changes SLet's to `modify!`
--   calls if such a variable is already in scope.
--   Also makes sure that the iteration variable `iter` is not assigned,
--   and that no `FLet`s are found.
--   Returns the variables which were changed to `modify!`.
preprocessLoopBody :: Scope -> Maybe TeVar -> ProcDMTerm -> StateT [TeVar] MTC ProcDMTerm

preprocessLoopBody scope iter (SLetBase ltype (v :- jt) term body) = do
  -- it is not allowed to change the iteration variable
  case (iter, v) of
    (Just iter, Just v) | iter == v
                          -> throwOriginalError (DemutationError $ "Inside for-loops the iteration variable (in this case '" <> show iter <> "') is not allowed to be mutated.")
    _ -> pure ()

  -- if an slet expression binds a variable which is already in scope,
  -- then this means we are actually mutating this variable.
  -- thus we update the term to be a mutlet and use the builtin modify!
  -- function for setting the variable
  -- if the variable has not been in scope, it is a local variable,
  -- and we do not change the term

  (term') <- preprocessLoopBody scope iter term
  -- let newVars = nub (termVars <> bodyVars)

  case v of
    Just v -> case getValue v scope of
      Just _ -> state (\a -> ((), a <> [v])) 
      Nothing -> pure ()
    Nothing -> pure ()

  (body') <- preprocessLoopBody scope iter body
  return (SLetBase ltype (v :- jt) term' body')


preprocessLoopBody scope iter (TLet (vs) term body) = do
  -- it is not allowed to change the iteration variable
  case (iter) of
    (Just iter) | (Just iter) `elem` (fstA <$> vs)
                          -> throwOriginalError (DemutationError $ "Inside for-loops the iteration variable (in this case '" <> show iter <> "') is not allowed to be mutated.")
    _ -> pure ()

  -- if an slet expression binds a variable which is already in scope,
  -- then this means we are actually mutating this variable.
  -- thus we update the term to be a mutlet and use the builtin modify!
  -- function for setting the variable
  -- if the variable has not been in scope, it is a local variable,
  -- and we do not change the term

  (term') <- preprocessLoopBody scope iter term

  -- we collect those values of vs for which there is something in the scope
  let vs_in_scope = [v | (Just v :- _) <- vs, (Just _) <- [getValue v scope]]


  state (\a -> ((), a <> vs_in_scope))

  body' <- preprocessLoopBody scope iter body
  return (TLet vs term' body')

preprocessLoopBody scope iter (FLet f _ _) = throwOriginalError (DemutationError $ "Function definition is not allowed in for loops. (Encountered definition of " <> show f <> ".)")
preprocessLoopBody scope iter (Ret t) = throwOriginalError (DemutationError $ "Return is not allowed in for loops. (Encountered " <> show (Ret t) <> ".)")

-- mutlets make us recurse
preprocessLoopBody scope iter (Extra (MutLet mtype t1 t2)) = do
  (t1') <- preprocessLoopBody scope iter t1
  (t2') <- preprocessLoopBody scope iter t2
  return (Extra (MutLet mtype t1' t2'))

preprocessLoopBody scope iter (Extra (DefaultRet a)) = do
  captureVars <- get
  lift $ debug $ "[preprocessLoopBody]: default ret in loop, building loopret with captures: " <> show captureVars
  return $ Extra $ LoopRet captureVars

preprocessLoopBody scope iter (Extra (MutRet)) = do
  captureVars <- get
  lift $ debug $ "[preprocessLoopBody]: mutret in loop, building loopret with captures: " <> show captureVars
  return $ Extra $ LoopRet captureVars

-- for the rest we simply recurse
preprocessLoopBody scope iter t = do
  x <- recDMTermMSameExtension (preprocessLoopBody scope iter) t
  return x






--------------------------------------------------------
-- removing unnecessary tlets

--
-- | Walk through the tlet sequence in `term` until
--  the last 'in', and check if this returns `αs`
--  as a tuple. If it does, replace it by `replacement`
--  and return the new term.
--  Else, return nothing.
replaceTLetIn :: [Maybe TeVar] -> DMTerm -> DMTerm -> Maybe DMTerm

-- If we have found our final `in` term, check that the tuple
-- is correct
replaceTLetIn αs replacement (TLet βs t1 (Tup t2s)) =

  let isvar :: (Maybe TeVar, DMTerm) -> Bool
      isvar (v, Var (w :- _)) | v == w = True
      isvar _ = False

  in case and (isvar <$> zip αs t2s) of
    -- if it does fit our pattern, replace by a single TLet
    -- and recursively call ourselves again
    True -> Just (TLet βs t1 replacement)

    -- if this does not fit our pattern, recurse into term and body
    False -> Nothing

-- If we have found our final `in` term (which is also allowed to be an slet),
-- check that the tuple is correct
replaceTLetIn αs replacement (SLet β t1 (Tup t2s)) =

  let isvar :: (Maybe TeVar, DMTerm) -> Bool
      isvar (v, Var (w :- _)) | v == w = True
      isvar _ = False

  in case and (isvar <$> zip αs t2s) of
    -- if it does fit our pattern, replace by a single TLet
    -- and recursively call ourselves again
    True -> Just (SLet β t1 replacement)

    -- if this does not fit our pattern, recurse into term and body
    False -> Nothing

-- if we have a next tlet, continue with it
replaceTLetIn αs replacement (TLet βs t1 (TLet γs t2 t3)) = TLet βs t1 <$> rest
  where
    rest = replaceTLetIn αs replacement (TLet γs t2 t3)

-- if we have an intermiediate slet, also continue
replaceTLetIn αs replacement (SLet βs t1 (TLet γs t2 t3)) = SLet βs t1 <$> rest
  where
    rest = replaceTLetIn αs replacement (TLet γs t2 t3)

-- if we have an intermiediate flet, also continue
replaceTLetIn αs replacement (FLet βs t1 (TLet γs t2 t3)) = FLet βs t1 <$> rest
  where
    rest = replaceTLetIn αs replacement (TLet γs t2 t3)

-- if the term is different, we cannot do anything
replaceTLetIn αs replacement _ = Nothing




optimizeTLet :: DMTerm -> DMTerm
-- the interesting case
optimizeTLet (TLet (αs) (term) t3) =
  -- if we have two tlets inside each other, where
  -- one of them returns the exactly the variables
  -- captured by the other, i.e:
  --
  -- > tlet αs... = tlet βs = t1
  -- >              in (αs...)
  -- > in t3
  --
  -- then we can change it to
  --
  -- > tlet βs = t1
  -- > in t3
  --
  --
  -- But, there is one complication, namely:
  -- It could be that the tlet with `in (αs...)`
  -- is not directly inside of our term, but
  -- further nested inside a tlet sequence.
  -- Thus we do search for the `in` using `replaceTLetIn`.
  case replaceTLetIn (fstA <$> αs) t3 term of

    -- if we were successfull, we simply use the returned
    -- term (after recursing on it)
    Just replaced -> optimizeTLet replaced

    -- if not successfull, we recurse
    Nothing -> TLet (αs) (optimizeTLet term) (optimizeTLet t3)

-- the recursion case
optimizeTLet t      = recDMTermSameExtension (optimizeTLet) t




-}

