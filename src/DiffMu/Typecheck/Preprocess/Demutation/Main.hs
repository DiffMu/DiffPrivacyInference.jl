
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}

{- |
Description: The demutation preprocessing step.

This step takes a `ProcDMTerm` which is a procedural-style term as was parsed by the parser,
and turns it into a `DemutDMTerm` in which all mutating function calls are replaced by let-statements,
which explicitly reassign those variables which have been mutated.

The resulting `DemutDMTerm` has a semi-ssa form, where all mutations are assigned to a new variable name.
(The form is only "semi"-ssa because variable reassignments by the user are allowed, and passed through as is.)
Black box calls are given custom application terms (`BBApply`).

Furthermore, it is checked that our strict scoping rules are followed (`VariableAccessType`).
-}
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
import DiffMu.Abstract (Located(getLocation))
import Text.Parsec (getPosition)

default (Text)

ld s l = Located (downgradeToRelated s l)

demutTLetStatement :: SourceLocExt -> LetKind -> [ProcVar] -> LocDemutDMTerm -> MTC TermType
demutTLetStatement l ltype vars term = case vars of
  [var] -> do
            var' <- (procVarAsTeVar var l)
            return (Statement l (Extra (DemutSLetBase ltype var' term))
                   (SingleMove var))
  vars -> do
            vars' <- mapM (\v -> procVarAsTeVar v l) vars
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
  resterm <- termTypeAsTerm (getLocation term) res
  logForce $ "-----------------------------------"
  logForce $ "Mutation elaborated term is:\n" <> showPretty resterm

  -- let optimized = optimizeTLet res
  -- logForce $ "-----------------------------------"
  -- logForce $ "TLet optimized term is:\n" <> showPretty optimized

  return resterm


elaborateValue :: Scope -> LocProcDMTerm -> MTC (ImmutType , LocMoveType)
elaborateValue scname te@(Located l _) = do
  (te1type) <- elaborateMut scname te
  case te1type of
    Statement _ _ _ -> demutationError ("Expected term to be a value, but it was a statement:\n" <> showPretty te) l
    StatementWithoutDefault _ _ -> demutationError ("Expected term to be a value, but it was a statement:\n" <> showPretty te) l
    Value it mt -> return (it , mt)
    MutatingFunctionEnd _ -> demutationError "Expected term to be a value, but it was a return." l
    -- PurePhiTermType cond tt1 tt2 -> case (tt1, tt2) of
    --   ((Value Pure mt1,tt1), (Value Pure mt2,tt2)) -> pure $ (Pure, (PhiMove cond (mt1,tt1) (mt2,tt2)))
    --   other -> demutationErrorNoLoc $ "Expected a term to be a value, but found an if statement where the branches had term types: " <> show other

elaboratePureValue :: Scope -> LocProcDMTerm -> MTC (LocMoveType)
elaboratePureValue scname te@(Located l _) = do
  (te1type) <- elaborateMut scname te
  case te1type of
    Statement _ _ _   -> demutationError ("Expected term to be a value, but it was a statement:\n" <> showPretty te) l
    StatementWithoutDefault _ _   -> demutationError ("Expected term to be a value, but it was a statement:\n" <> showPretty te) l
    MutatingFunctionEnd _ -> demutationError "Expected term to be a value, but it was a return." l
    Value Pure mt -> return (mt)
    Value _ mt    -> demutationError ("Expected term to be a pure value, but it has type: " <> showPretty mt) l


-- make sure there are no Value or MutatingFunctionEnd inside the blocks
-- reverse the block statements
-- concatenate Statements blocks
-- determine the correct LastTerm for the concatenation result
makeTermList :: [TermType] -> MTC (LastValue, Maybe LocDemutDMTerm, [LocDemutDMTerm])

-- empty list
makeTermList [] = throwUnlocatedError $ DemutationError $ "Found an empty list of statements."

-- single element left
makeTermList (Value it mt : [])         = case it of
                                            Pure -> do mt' <- moveTypeAsTerm_Loc (getLocation mt) mt ; return (PureValue mt, Nothing, [mt'])
                                            _    -> throwUnlocatedError $ DemutationError ("The last value of a block has the type " <> showPretty it <> "\n"
                                                                    <> "Only pure values are allowed.\n"
                                                                    <> "The value is:\n"
                                                                    <> showPretty mt)
makeTermList (Statement l term last : []) = do last' <- (moveTypeAsTerm l last) ; return (PureValue (Located l last), Just (Located l last'), [Located l term])
makeTermList (StatementWithoutDefault l term : []) = return (NoLastValue , Nothing, [Located l term])
-- makeTermList (PurePhiTermType cond (Value Pure mt1,tt1) (Value Pure mt2,tt2) : []) = return (PureValue [mt1,mt2] , Nothing, [Extra (DemutPhi cond tt1 tt2)])
-- makeTermList (PurePhiTermType cond _ _ : [])     = demutationErrorNoLoc $ "Encountered a phi as last statement in a block, but the branches to do not have pure values as returns."
makeTermList (MutatingFunctionEnd retloc : [])          = return (MutatingFunctionEndValue retloc, Nothing, [])

-- more than one element left
makeTermList (Value _ mt : ts)          = throwUnlocatedError $ DemutationError $ "Found a value term " <> showPretty mt <> " inside a list of statements."
makeTermList (Statement l term _ : ts)    = do (last, lastt, ts') <- makeTermList ts
                                               return (last, lastt, ts' <> [Located l term])
makeTermList (StatementWithoutDefault l term : ts)
                                        = do (last, lastt, ts') <- makeTermList ts
                                             return (last, lastt, ts' <> [Located l term])
makeTermList (MutatingFunctionEnd _ : ts) = throwUnlocatedError $ DemutationError $ "Found a MutatingFunctionEnd inside a list of statements."
-- makeTermList (PurePhiTermType cond v1 v2 : ts) = demutationErrorNoLoc "Phis in the middle of a block are currently not implemented."

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
    MutatingFunctionEndValue retloc -> demutationError ("Encountered a 'return' which is not the last statement of a function.") retloc
    NoLastValue              -> demutationError "Encountered a statement without last value in top level." l

  -- case mt of
  --   NoMove pdt -> pure ()
  --   _ -> demutationErrorNoLoc $ "Encountered a block which is not top level and not in a function, but has a move as return type. This is currently not allowed."

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
    PureValue (Located _ mt)        -> return mt
    MutatingFunctionEndValue retloc -> demutationError ("Encountered a 'return' which is not the last statement of a function.") retloc
    NoLastValue -> demutationError "Encountered a statement which is not allowed to be the last one in a block.\n" l


  case mt of
    NoMove _  -> pure ()
    _ -> demutationError "Encountered a block which is not top level and not in a function, but has a move as return type. This is not allowed." l

  return (Value Pure (Located l (NoMove (Extra (DemutBlock ts'')))))

elaborateMut scname (Located l (Op op args)) = do
  args' <- mapM (elaboratePureValue scname) args
  args'' <- mapM (moveTypeAsTerm_Loc l) args'
  pure (Value Pure (Located l (NoMove (Op op args''))))

elaborateMut scname (Located l (Sng η τ)) = do
  return (Value Pure (Located l (NoMove $ Sng η τ)))

elaborateMut scname (Located l (DMTrue)) = do
  return (Value Pure (Located l (NoMove $ DMTrue)))

elaborateMut scname (Located l (DMFalse)) = do
  return (Value Pure (Located l (NoMove $ DMFalse)))

elaborateMut scname term@(Located l (Var _)) = demutationError ("Unsupported term: " <> showPretty term) l

elaborateMut scname (Located l (Extra (ProcVarTerm x))) = do
  mx <- expectNotMoved l x
  itype <- expectImmutType scname l x

  return (Value itype (Located l (SingleMove x)))

elaborateMut scname (Located l (Extra (ProcBBLet procx args))) = do

  -- write the black box into the scope with its type
  scope'  <- setImmutType ReassignmentWrite scname l procx PureBlackBox

  -- allocate a memory location
  memx <- allocateMem scname (Just procx) (MemVarInfo NotFunctionArgument l)

  -- write it into the memctx
  setMem procx [(SingleMem memx)]

  tevarx <- procVarAsTeVar procx l

  return (Statement l (Extra (DemutBBLet tevarx args)) (SingleMove procx))


elaborateMut scname (Located l (Extra (ProcSLetBase ltype x term))) = do
  (newTermType, Located l_moveType moveType) <- elaborateValue scname term

  case newTermType of
    Pure -> pure ()
    Mutating _ -> pure ()
    PureBlackBox     -> throwLocatedError (DemutationError $ "Found an assignment where RHS is a black box. This is not allowed.") l

  moveType' <- (moveTypeAsTerm l moveType)

  --
  -- move out of variables on the RHS, getting the memory
  -- locations, and the new allocations, then:
  --
  -- 1. set memory locations for variables on the LHS
  -- 2. generate terms for the memory allocations
  -- 
  (mem) <- moveGetMem scname l (Just x) moveType
  setMem x mem

  x' <- procVarAsTeVar x l

  -- write the immut type into the scope
  setImmutType ReassignmentWrite scname l x newTermType

  -- log what happened
  debug $ "[elaborateMut/SLetBase]: The variable " <> showPretty x <> " is being assigned." 
  logmem <- use memCtx
  debug $ "The memctx is now:\n"
  debug $ showT logmem


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
    Mutating ims -> throwLocatedError (DemutationError $ "Found a tuple assignment where RHS is a mutating function. This is not allowed.") l
    PureBlackBox -> throwLocatedError (DemutationError $ "Found a tuple assignment where RHS is a black box. This is not allowed.") l
  --
  -- we set the immuttype of every element on the LHS to Pure
  --
  mapM (\x -> setImmutType ReassignmentWrite scname l x Pure) vars

  moveType' <- (moveTypeAsTerm_Loc l moveType)

  -- get memory of the RHS
  mem <- moveGetMem_Loc scname l Nothing moveType

  -- write the list of possible memory types into the
  -- variables of the lhs
  setMemTupleInManyMems l scname vars mem

  demutTLetStatement l ltype vars moveType'



elaborateMut scname (Located l (Extra (ProcLamStar args ret body))) = do
  bodyscname <- appendNewScopeVar "lamstar" scname
  (newBody, newBodyType) <- elaborateLambda bodyscname [(v ::- x) | (v ::- (x , _)) <- args] body
  return (Value newBodyType (Located l (NoMove (LamStar [(UserTeVar v) :- x | (v ::- x) <- args] ret newBody))))

elaborateMut scname (Located l (Extra (ProcLam args ret body))) = do
  bodyscname <- appendNewScopeVar "lam" scname
  (newBody, newBodyType) <- elaborateLambda bodyscname [(v ::- x) | (v ::- (x, _)) <- args] body
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
  mem <- allocateMem scname (Just name) (MemVarInfo NotFunctionArgument l)
  setMem name [(SingleMem mem)]

  -- write the immut type into the scope
  setImmutTypeFLetDefined scname l name newTermType

  -- log what happened
  debug $ "[elaborateMut/FLetBase]: The function " <> showPretty name <> " is being defined."
  logmem <- use memCtx
  debug $ "The memctx is now:\n"
  debug $ showT logmem


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
          False -> throwLocatedError (DemutationError $ "Trying to call the function '" <> showPretty f <> "' with a wrong number of arguments.")
                     (l :\\:
                     "The function " <> quote (showPretty f) <> " has " <> showPretty (length muts) <> " arguments but has been given " <> showPretty (length args) <> "."
                     )

        let mutsToOtherMuts mut = case mut of
              Mutated -> MutatedArg
              NotMutated -> NotMutatedArg Pure

        let mutargs = zip (mutsToOtherMuts <$> muts) args
        (newArgs , muts) <- elaborateMutList l (showPretty f) scname mutargs

        movetype' <- (moveTypeAsTerm_Loc l movetype)
        let funcallterm = (Apply movetype' newArgs)

        -- the new term
        demutTLetStatement l PureLet muts (Located l (funcallterm))

    --
    -- case II : A pure function call
    --
    Pure -> do
        let mutargs = zip (repeat (NotMutatedArg Pure)) args
        (newArgs , muts) <- elaborateMutList l (showPretty f) scname mutargs

        movetype' <- (moveTypeAsTerm_Loc l movetype)
        let funcallterm = (Apply movetype' newArgs)

        -- the new term
        return $ Value Pure (Located l (NoMove funcallterm))

    --
    -- case III: A call to a pure black box
    --
    --   since #202 this is handled in the case for `BBApply`.
    --

    PureBlackBox -> demutationError "Trying to call a black box without `unbox_call` wrapper." l



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
        (newArgs , muts) <- elaborateMutList l (showPretty f) scname mutargs

        movetype' <- (moveTypeAsTerm_Loc l movetype)
        let glvars' = map UserTeVar (getAllKeys glvars)
        return $ Value Pure (Located l (NoMove (BBApply movetype' newArgs glvars' bbkind')))

    otherType -> demutationError ("Trying to call a function of type " <> showPretty otherType <> " with `unbox_call`.") l



elaborateMut scname (Located l (Extra (ProcPreLoop (i1,i2,i3) iterVar body))) = do -- demutationErrorNoLoc $ "Not implemented: loop." -- do
  debug $ "[elaborateMut/Loop] BEGIN ---------------------"


  -- first, elaborate the iters
  (newi1) <- elaboratePureValue scname i1
  newi1' <- moveTypeAsTerm_Loc l newi1
  (newi2) <- elaboratePureValue scname i2
  newi2' <- moveTypeAsTerm_Loc l newi2
  (newi3) <- elaboratePureValue scname i3 
  newi3' <- moveTypeAsTerm_Loc l newi3
  --
  -- add the iterator to the scope,
  -- and backup old type
  oldIterImmutType <- backupAndSetImmutType scname l iterVar Pure
  --
  -- backup iter memory location, and create a new one
  oldIterMem <- getValue iterVar <$> use memCtx
  setMem iterVar =<< pure <$> SingleMem <$> allocateMem scname (Just iterVar) (MemVarInfo NotFunctionArgument l)
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
  debug $ showT memsBefore
  debug $ "----"
  debug $ "memctx after:\n"
  debug $ showT memsAfter
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
    xs -> throwLocatedError (DemutationLoopError $ "Found a loop body which moves variables around.")
                            (l :\\:
                             ("The following variables are changed and contain memory locations from before: " <> showT xs <> "\n"
                             <> "Since this means that we cannot track what actually happens in the case of an unknown number of iterations,\n"
                             <> "this is not allowed.")
                            )
  --
  -- Check that if function arguments are mutated, then their containing pvars
  -- need to still point to them after the loop body. For details, see #232.
  meminfo <- use memVarInfo
  let containsMutatedFunctionArgument pmemstate =
        let pmemvars = getAllMemVarsOfMemState pmemstate
            changedArgMemVars = [mv | mv <- pmemvars
                                    , getValue mv mutsBefore             /= getValue mv mutsAfter
                                    , (_ifaInfo <$> getValue mv meminfo) == Just FunctionArgument
                                    ]
        in changedArgMemVars
  let ensureNotChangedIfMutatedFunctionArgument (pv,pmemstate_before) = do
        let mutatedArgMemVars = containsMutatedFunctionArgument pmemstate_before
        case length mutatedArgMemVars > 0 of
          False -> pure ()
          True  -> do let pmemstate_after = case getValue pv memsAfter of 
                                           Just a -> a
                                           Nothing -> undefined -- this should not happen since pv is in `memsBefore`
                      case pmemstate_before == pmemstate_after of
                        True  -> pure ()
                        False -> throwLocatedError (DemutationLoopError "Reassignment of variable containing mutated function arguments in loops is not allowed.")
                                                   (l :\\:
                                                    "The variable " <> showT pv <> " contains a reference to the following mutated function arguments: " <> showT mutatedArgMemVars <> "\n"
                                                   <> "If function arguments are mutated in a loop, then the variable which contains them is not allowed to be reassigned.\n"
                                                   <> "But this happened here, memory of the variable before the body: " <> showT pmemstate_before <> ", after: " <> showT pmemstate_after
                                                   )
  mapM_ ensureNotChangedIfMutatedFunctionArgument (getAllKeyElemPairs memsBefore)
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
                    ; (ma, ma')         -> internalError $ "Did not expect the mutctx to have no entry for: " <> showT v1
                    }
              mems_changed <- mapM isChanged single_mems
              return $ any (== True) mems_changed
            MemMoved _     -> return False
        --
        -- case 2: mem_after /= mem_before,
        --   then obviously something changed,
        --   so this is a capture
        Just v1 | otherwise -> return True

  captureMems <- filterM isChanged (getAllKeyElemPairs memsBefore)
  capturesBefore <- mapM (procVarAsTeVarInMutCtx memsBefore mutsBefore UnknownLoc) $ fst <$> captureMems
  capturesAfter  <- mapM (procVarAsTeVarInMutCtx memsAfter mutsAfter UnknownLoc)  $ fst <$> captureMems
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
  let demutated_loop = Extra (DemutLoop (newi1',newi2',newi3') capturesBefore capturesAfter ((UserTeVar iterVar, captureVar))
                             (Located l $ Extra (DemutBlock demutated_body_terms)))

  --
  ------------------------------------------------

  debug $ "----"
  debug $ "capture mems:\n"
  debug $ showT captureMems


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
  cond' <- moveTypeAsTerm_Loc l =<< elaboratePureValue scname cond

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
      (MutatingFunctionEndValue retloc,_) -> demutationError ("Ifs cannot contain `return` statements.") retloc
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
          (MutatingFunctionEndValue retloc,_) -> demutationError ("Ifs cannot contain `return` statements.") retloc
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
  debug $ "[Demutating Phi]: Coequalizing of mutctx:"
  debug $ "                  mctx1:  " <> indentAfterFirstWith "                          " (showT mutCtxAfter1)
  debug $ "                  mctx2:  " <> indentAfterFirstWith "                          " (showT mutCtxAfter2)
  debug $ "                  result: " <> indentAfterFirstWith "                          " (showT mutCtxAfter)


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
      (proj1,proj2) -> demutationError "Found an if with branches of value-type, in such ifs mutation is not allowed." l

    --
    -- error case: mixed branches
    --
    branchTypes -> demutationError ("Found an if where the branch types differ: " <> showT branchTypes) l


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
  (argTerms, mutVars) <- elaborateMutList l "subgrad" scname [(MutatedArg , t1), (NotMutatedArg Pure , t2)]
  case argTerms of
    [newT1, newT2] -> demutTLetStatement l PureLet mutVars (Located l (MutSubGrad newT1 newT2))
    _ -> internalError ("Wrong number of terms after elaborateMutList")

elaborateMut scname (Located l (ScaleGrad scalar grads)) = do
  (argTerms, mutVars) <- elaborateMutList l "scalegrad" scname [(NotMutatedArg Pure , scalar), (MutatedArg , grads)]
  case argTerms of
    [newT1, newT2] -> demutTLetStatement l PureLet mutVars (Located l (ScaleGrad newT1 newT2))
    _ -> internalError ("Wrong number of terms after elaborateMutList")

elaborateMut scname (Located l (MutClipM c t)) = do
  (argTerms, mutVars) <- elaborateMutList l "clip" scname [(MutatedArg , t)]
  case argTerms of
    [newT] -> demutTLetStatement l PureLet mutVars (Located l (MutClipM c newT))
    _ -> internalError ("Wrong number of terms after elaborateMutList")

elaborateMut scname (Located l (MutConvertM c t)) = do
  (argTerms, mutVars) <- elaborateMutList l "norm_convert" scname [(MutatedArg , t)]
  case argTerms of
    [newT] -> demutTLetStatement l PureLet mutVars (Located l (MutConvertM c newT))
    _ -> internalError ("Wrong number of terms after elaborateMutList")

elaborateMut scname (Located l (MutGauss t1 t2 t3 t4)) = do
  (argTerms, mutVars) <- elaborateMutList l "gauss" scname [(NotMutatedArg Pure , t1), (NotMutatedArg Pure , t2), (NotMutatedArg Pure , t3), (MutatedArg , t4)]
  case argTerms of
    [newT1, newT2, newT3, newT4] -> demutTLetStatement l PureLet mutVars (Located l (Gauss newT1 newT2 newT3 newT4))
    _ -> internalError ("Wrong number of terms after elaborateMutList")

elaborateMut scname (Located l (MutLaplace t1 t2 t3)) = do
  (argTerms, mutVars) <- elaborateMutList l "laplace" scname [(NotMutatedArg Pure , t1), (NotMutatedArg Pure , t2), (MutatedArg , t3)]
  case argTerms of
    [newT1, newT2, newT3] -> demutTLetStatement l PureLet mutVars (Located l (Laplace newT1 newT2 newT3))
    _ -> internalError ("Wrong number of terms after elaborateMutList")

elaborateMut scname (Located l (MutUndiscM t1)) = do
  (argTerms, mutVars) <- elaborateMutList l "convert" scname [(MutatedArg , t1)]
  case argTerms of
    [newT1] -> demutTLetStatement l PureLet mutVars (Located l (MutUndiscM newT1))
    _ -> internalError ("Wrong number of terms after elaborateMutList")


elaborateMut scname (Located l (InternalMutate t1)) = do
  (argTerms, mutVars) <- elaborateMutList l "internal_mutate" scname [(MutatedArg , t1)]
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
elaborateMut scname (Located l (Undisc t1))               = elaborateNonMut1 scname l Undisc t1
elaborateMut scname (Located l (Size t1))                 = elaborateNonMut1 scname l Size t1
elaborateMut scname (Located l (Length t1))               = elaborateNonMut1 scname l Length t1
elaborateMut scname (Located l (ZeroGrad t1))             = elaborateNonMut1 scname l ZeroGrad t1
elaborateMut scname (Located l (SumGrads t1 t2))          = elaborateNonMut2 scname l SumGrads t1 t2
elaborateMut scname (Located l (SubGrad t1 t2))           = elaborateNonMut2 scname l SubGrad t1 t2
elaborateMut scname (Located l (Sample t1 t2 t3))         = elaborateNonMut3 scname l Sample t1 t2 t3
elaborateMut scname (Located l (InternalExpectConst t1))  = elaborateNonMut1 scname l InternalExpectConst t1
elaborateMut scname (Located l (Clone t1))                = elaborateNonMut1 scname l Clone t1
elaborateMut scname (Located l (ClipM c t1))              = elaborateNonMut1 scname l (ClipM c) t1
elaborateMut scname (Located l (ConvertM c t1))           = elaborateNonMut1 scname l (ConvertM c) t1
elaborateMut scname (Located l (UndiscM  t1))             = elaborateNonMut1 scname l UndiscM t1
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
elaborateMut scname term@(Located l (Choice t1))        = throwLocatedError (UnsupportedError ("When mutation-elaborating:\n" <> showPretty term)) l
elaborateMut scname term@(Located l (Loop t1 t2 t3 t4)) = throwLocatedError (UnsupportedError ("When mutation-elaborating:\n" <> showPretty term)) l
elaborateMut scname term@(Located l (TProject t1 t2))   = throwLocatedError (UnsupportedError ("When mutation-elaborating:\n" <> showPretty term)) l
elaborateMut scname term@(Located l (Arg x a b))        = throwLocatedError (UnsupportedError ("When mutation-elaborating:\n" <> showPretty term)) l
elaborateMut scname term@(Located l (Ret t1))           = throwLocatedError (UnsupportedError ("When mutation-elaborating:\n" <> showPretty term)) l


elaborateMut scname term@_    = throwLocatedError (UnsupportedError ("When mutation-elaborating:\n" <> showPretty term)) (getLocation term)


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
  (newT1) <- moveTypeAsTerm_Loc l =<< elaboratePureValue scname (t1)
  return (Value Pure (Located l (ctr newT1)))


elaborateHelper2 :: Scope
                    -> SourceLocExt
                    -> (LocDemutDMTerm -> LocDemutDMTerm -> MoveType)
                    -> LocProcDMTerm -> LocProcDMTerm
                    -> MTC TermType
elaborateHelper2 scname l ctr t1 t2 = do
  (newT1) <- moveTypeAsTerm_Loc l =<< elaboratePureValue scname ((t1))
  (newT2) <- moveTypeAsTerm_Loc l =<< elaboratePureValue scname ((t2))
  return (Value Pure (Located l (ctr newT1 newT2)))


elaborateHelper3 :: Scope
                    -> SourceLocExt
                    -> (LocDemutDMTerm -> LocDemutDMTerm -> LocDemutDMTerm -> MoveType)
                    -> LocProcDMTerm -> LocProcDMTerm -> LocProcDMTerm
                    -> MTC TermType
elaborateHelper3 scname l ctr t1 t2 t3 = do
  (newT1) <- moveTypeAsTerm_Loc l =<< elaboratePureValue scname t1
  (newT2) <- moveTypeAsTerm_Loc l =<< elaboratePureValue scname t2
  (newT3) <- moveTypeAsTerm_Loc l =<< elaboratePureValue scname t3
  return (Value Pure (Located l (ctr newT1 newT2 newT3)))


elaborateHelper4 :: Scope
                    -> SourceLocExt
                    -> (LocDemutDMTerm -> LocDemutDMTerm -> LocDemutDMTerm -> LocDemutDMTerm -> MoveType)
                    -> LocProcDMTerm -> LocProcDMTerm -> LocProcDMTerm -> LocProcDMTerm
                    -> MTC TermType
elaborateHelper4 scname l ctr t1 t2 t3 t4 = do
  (newT1) <- moveTypeAsTerm_Loc l =<< elaboratePureValue scname t1
  (newT2) <- moveTypeAsTerm_Loc l =<< elaboratePureValue scname t2
  (newT3) <- moveTypeAsTerm_Loc l =<< elaboratePureValue scname t3
  (newT4) <- moveTypeAsTerm_Loc l =<< elaboratePureValue scname t4
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
    pdt' <- moveTypeAsTerm_Loc UnknownLoc =<< elaboratePureValue scname pdt
    return $ BBVecLike jt pdt'
  BBMatrix jt pdt1 pdt2 -> do
    pdt1' <- moveTypeAsTerm_Loc UnknownLoc =<< elaboratePureValue scname pdt1
    pdt2' <- moveTypeAsTerm_Loc UnknownLoc =<< elaboratePureValue scname pdt2
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
  mapM (\x -> setImmutTypeOverwritePrevious scname (getLocation body) x Pure) [a | (a ::- _) <- args]
  -- ##
  -- END NO.
  --
  -- Allocate new memory for the arguments.
  let arghint (x ::- _) = Just x
  argmvs <- mapM (\hint -> allocateMem scname hint (MemVarInfo FunctionArgument (getLocation body))) (arghint <$> args)

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
    logForce $ "memCtx:\n" <> showT memctx
    logForce $ ""
    logForce $ "mutCtx:\n" <> showT mutctx
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
        toTeVar (Split slocs as, (t:ts)) = throwLocatedError
          (DemutationSplitMutatingArgumentError $ "While demutating a function definition, encountered the case that an argument memory location was split. This is not allowed.")
          (let (arg,tlocs) = t in SourceQuote (
            [(tl,"mutation of an argument (currently under the name of " <> quote (showPretty arg) <> ") occurs here") | tl <- tlocs]
            <> [(sl,quote (showPretty arg) <> " is split here") | sl <- slocs]
          ))
        toTeVar (Split slocs as, []) = do
          -- if a var was split, we check recursively if
          -- its parts have been mutated.
          let f a = do
                      partTerms <- toTeVar =<< getMemVarMutationStatus a
                      case partTerms of
                        Just parts -> throwLocatedError (DemutationSplitMutatingArgumentError "Part of a split function argument was mutated. This is not allowed.")
                                    (let (parg,ptlocs) = parts in SourceQuote
                                     ([(sl,"a function argument is split here") | sl <- slocs]
                                     <> [(pl,"the part " <> quote (showPretty parg) <> " of that argument is mutated here") | pl <- ptlocs]
                                     )
                                    )
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
      debug $ "[elaborateLambda] pure function. move type: " <> showT as
      debug $ "   movedVars: " <> showT (movedVarsOfMoveType_Loc as) <> ", mutated_argmvs: " <> showT mutated_argmvs
      --
      memTypesOfMove <- mapM (expectNotMoved l) (movedVarsOfMoveType_Loc as)
      let memVarsOfMove = join memTypesOfMove >>= getAllMemVars
      --
      case memVarsOfMove `intersect` argmvs of
        [] -> pure ()
        pvs ->   demutationError "Found a function which passes through a reference given as input. This is not allowed."
                        (l :\\:
                         "The passed through memory references are: " <> showPretty pvs
                        )
      --
      -- make sure that no self-aliasing occurs
      let dups = findDuplicatesWith (\a -> a) memVarsOfMove
      case dups of
        [] -> pure ()
        dups -> demutationError "Found a function whose result value contains multiple references to the same memory location. This is not allowed."
                   (l :\\:
                    ("There are multiple references to all of the following locations: " <> showPretty (nub dups))
                   )
      --
      return $ (Pure, Extra $ DemutBlock new_body_terms)


    --
    -- case II: not allowed
    --
    (PureValue as, xs) -> do
        let makeEdits (x,locs) = [(l, "argument " <> quote (showPretty x) <> " last mutated here.") | l <- locs]

        let edits = (getLocation body,"missing a 'return' statement") : (xs >>= makeEdits)

        demutationError ("Found a function which is mutating, but does not have a 'return'. This is not allowed.")
          (
            SourceQuote edits :\\:
            ("The mutated arguments are: " <> showPretty (fst <$> xs))
          )
    --
    -- case III: not allowed
    --
    (MutatingFunctionEndValue retloc, []) -> demutationError ("Found a function which is not mutating, but has a 'return'. This is not allowed.")
                                                (SourceQuote
                                                [ (getLocation body, "does not mutate any of its arguments")
                                                , (retloc, "should be removed")
                                                ]
                                                )

    --
    -- case IV: mutating function
    --
    (MutatingFunctionEndValue _, mvs) -> do
      let s1 = "Auto generated return tuple (or single value) of mutating function"
      let last_tuple = case fst <$> mvs of
              [v] -> Var (v)
              vs  -> Tup [(Located (RelatedLoc s1 l) (Var v)) | v <- vs]
      return (Mutating mut_states, Extra (DemutBlock ((Located (downgradeToRelated s1 l) (last_tuple)) : new_body_terms)))

    (NoLastValue, _) -> demutationError "Found a function which has no last value, this is not allowed." l



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

elaborateMutList :: SourceLocExt -> Text -> Scope -> [(MutationArgumentType , LocProcDMTerm)] -> MTC ([LocDemutDMTerm] , [ProcVar])
elaborateMutList loc f scname mutargs = do
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
            -- say that this variable is being mutated (VAT)
            setImmutType MutationWrite scname l x Pure

            -- the elaborated value of x
            -- (this needs to be done before `markMutated` is called)
            x' <- (procVarAsTeVar x loc)

            -- get the memvar of this tevar from the memctx
            -- and say that the memory location is mutated
            markMutated x loc (DMPersistentMessage
                               ("When checking that the argument" :<>: Quote arg :<>: "passed to function" :<>: Quote f :<>: "in a mutable argument position contains a single memory location.":\\:
                                loc
                               ))

            return ((Located l (Var (x'))), (Located l (SingleMove x)), Just x)

          -- if argument is not a var, throw error
          _ -> throwLocatedError (DemutationError "Only variables can be used in a mutating-argument position of a function call.")
                (l :\\:
                 ("When calling the mutating function " <> quote f <> " found the term " <> quote (showPretty arg) <> " as argument in a mutable-argument-position.")
                )

      checkArg (NotMutatedArg reqty , arg) = do
        -- if the argument is given in an immutable position,
        -- we allow to use the full immut checking
        (itype , movetype) <- elaborateValue scname arg

        -- we require the argument to be of the right type
        case itype == reqty of
          True -> pure ()
          False -> throwLocatedError (DemutationError "Wrong function argument type in non-mutating position")
                     (loc :\\:
                      ("While checking the argument " <> showPretty arg <> " of the function " <> f <> ":\n"
                      <> "Expected it to have demutation type " <> quote (showPretty reqty)
                      <> "But found type " <> quote (showPretty itype)))

        movetype' <- moveTypeAsTerm_Loc (loc) movetype

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

  let showvarcounts ((name,count):rest) = " - variable `" <> showT name <> "` occurs " <> showT count <> " times." <> "\n"
                                            <> showvarcounts rest
      showvarcounts [] = ""

  -- make sure that such variables do not occur
  case wrongVarCounts of
    [] -> return ()
    xs -> throwLocatedError (DemutationNonAliasedMutatingArgumentError "Occurence of same variable in multiple mutating argument positions.")
                       (loc :\\:
                        ("The function '" <> f <> "' is called with the following vars in mutating positions:\n\n"
                        <> showvarcounts mutvarcounts <> "\n"
                        <> "But it is not allowed to have the same variable occur multiple times "))

  return (newArgs, mutVars)


