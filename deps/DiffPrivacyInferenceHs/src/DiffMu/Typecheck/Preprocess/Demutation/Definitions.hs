
{-# LANGUAGE TemplateHaskell #-}

{- |
Description: Basic definitions for the demutation preprocessing step.

This includes:
 - Mutation types
 - Variable access types
 - Move types
 - Term types
 - Memory states
 - Monadic state which tracks these during demutation
-}
module DiffMu.Typecheck.Preprocess.Demutation.Definitions where

import DiffMu.Prelude -- hiding (TeVar)
import DiffMu.Abstract
import DiffMu.Core
import DiffMu.Core.TC
import DiffMu.Core.Logging
import DiffMu.Abstract.Data.Permutation
import DiffMu.Typecheck.Preprocess.Common
import DiffMu.Typecheck.Preprocess.TopLevel

import qualified Data.HashMap.Strict as H
import qualified Data.HashSet as HS

import qualified Data.Text as T
import Data.Foldable

import Debug.Trace

import qualified Prelude as P
import qualified Data.Char as Char
import DiffMu.Abstract (throwUnlocatedError)
default (Text,Int)


--------------------------------------------------------------------------------------
-- Prelude
--------------------------------------------------------------------------------------

fst3 (a,b,c) = a

demutationError err loc = throwLocatedError (DemutationError err) loc


--------------------------------------------------------------------------------------
-- Demutation Type
--------------------------------------------------------------------------------------


data IsMutated = Mutated | NotMutated
  deriving (Generic, Show, Eq)

data IsLocalMutation = LocalMutation | NotLocalMutation
  deriving (Show, Eq)

data MutationArgumentType = MutatedArg | NotMutatedArg ImmutType

--
-- NOTE: We later sort `VarAccessType`s,
-- and we do not want that the `IsLocalMutation`
-- content influences this sort --- we need to know
-- which comes first.
--
-- Hence this type is "contractible".
--
instance Ord IsLocalMutation where
  a <= b = True

-- But we need a comparison anyways:
le_ilm :: IsLocalMutation -> IsLocalMutation -> Bool
le_ilm LocalMutation _ = True
le_ilm NotLocalMutation LocalMutation = False
le_ilm NotLocalMutation NotLocalMutation = True

onlyLocallyMutatedVariables :: [(ProcVar,IsLocalMutation)] -> Bool
onlyLocallyMutatedVariables xs = [v | (v, NotLocalMutation) <- xs] == []



data ImmutType = Pure | Mutating [IsMutated] | PureBlackBox
  deriving (Show,Eq)

instance ShowPretty ImmutType where
  showPretty Pure = "Pure"
  showPretty (Mutating args) = "Mutating (" <> intercalateS ", " (f <$> args) <> ") -> ()"
    where f Mutated = "mut"
          f NotMutated = "pure"
  showPretty PureBlackBox = "Blackbox"



---------------------------------------------------
-- These types describe which variable names
-- are in the RHS and must be moved on tlet/slet assignment
-- See #171 #172
data MoveType =
  TupleMove [LocMoveType]
  | SingleMove ProcVar
  | RefMove DemutDMTerm
  | NoMove DemutDMTerm
  | PhiMove LocDemutDMTerm (LocMoveType,LocDemutDMTerm) (LocMoveType,LocDemutDMTerm)
  deriving (Eq, Show)

instance ShowPretty MoveType where
  showPretty = showT

type LocMoveType = Located MoveType


data TermType =
  Value ImmutType LocMoveType
  | Statement SourceLocExt DemutDMTerm MoveType
  | StatementWithoutDefault SourceLocExt DemutDMTerm
  | MutatingFunctionEnd SourceLocExt

data LastValue =
   PureValue LocMoveType
   | MutatingFunctionEndValue SourceLocExt
   | NoLastValue

data PhiBranchType =
  ValueBranch SourceLocExt [LocDemutDMTerm] LocMoveType
  | StatementBranch SourceLocExt [LocDemutDMTerm]
  deriving (Show)

--------------------------------------------------
-- memory state
--
-- Tracking memory locations for demutation.
-- This mirrors the `MoveType` above, but with `MemVar`
-- instead of `ProcVar`.
--
-- See #185.
--

data MemType = TupleMem [MemType] | SingleMem MemVar | RefMem MemVar
  deriving (Eq, Show, Ord)

data MemState = MemExists [MemType] | MemMoved [SourceLocExt]
  deriving (Show)

data MemAssignmentType = AllocNecessary | PreexistingMem

type MemCtx = Ctx ProcVar MemState


data IsSplit = Split [SourceLocExt] [MemVar] | NotSplit
  deriving (Show,Eq)

data TeVarMutTrace = TeVarMutTrace (Maybe ProcVar) IsSplit [(TeVar,[SourceLocExt])] -- (every tevar also carries the locations where it was created as result of a mutation)
  deriving (Show,Eq)

newtype Scope = Scope [ScopeVar]
  deriving (Eq, Show)

type MutCtx = Ctx MemVar (Scope, TeVarMutTrace)

instance Eq MemState where
  (==) (MemMoved _) (MemMoved _) = True
  (==) (MemExists as) (MemExists bs) = sort (nub as) == sort (nub bs)
  (==) _ _ = False



--------------------------------------------------------
-- monoid instance for isMutated

instance Monad m => SemigroupM m IsMutated where
  (NotMutated) ⋆ b = pure b
  Mutated ⋆ b = pure Mutated
instance Monad m => MonoidM m IsMutated where
  neutral = pure NotMutated
instance Monad m => CheckNeutral m IsMutated where
  checkNeutral (NotMutated) = pure True
  checkNeutral (Mutated) = pure False

instance Semigroup IsMutated where
  (<>) = (⋆!)

instance Monoid IsMutated where
  mempty = neutralId


--------------------------------------------------------------------------------------
-- Memory info
--------------------------------------------------------------------------------------

data IsFunctionArgument = FunctionArgument | NotFunctionArgument
  deriving (Eq,Show)

data MemVarInfo = MemVarInfo
  {
    _ifaInfo :: IsFunctionArgument
  , _lastAssignmentLocInfo :: SourceLocExt
  }
$(makeLenses ''MemVarInfo)

type MemVarInfoCtx = Ctx MemVar MemVarInfo

--------------------------------------------------------------------------------------
-- Variable Access Type
--------------------------------------------------------------------------------------

-- These are generated while parsing the code
data VarAccessAction = ReadAction | WriteAction IsFLetDefined WriteKind
  deriving (Show,Eq)

-- These are carried in the state
data VarAccessState =
  VABasicAccess IsFLetDefined SourceLocExt
  | VAMultiWriteAccess IsFLetDefined (SourceLocExt,[(SourceLocExt,WriteKind)])
  | VAGlobalReadAccess (SourceLocExt,SourceLocExt)
  deriving (Show,Eq)

getDefinitionLocation :: VarAccessState -> SourceLocExt
getDefinitionLocation (VABasicAccess _ l) = l
getDefinitionLocation (VAMultiWriteAccess _ (l,_)) = l
getDefinitionLocation (VAGlobalReadAccess (l,_)) = l

data IsFLetDefined = NotFLetDefined | FLetDefined
  deriving (Show,Eq)

data WriteKind = MutationWrite | ReassignmentWrite
  deriving (Show,Eq)

class SemanticConcept x where
  noun :: x -> Text
  progressive :: x -> Text
  past :: x -> Text

instance SemanticConcept WriteKind where
  noun MutationWrite = "mutation"
  noun ReassignmentWrite = "reassignment"

  progressive MutationWrite = "mutating"
  progressive ReassignmentWrite = "reassigning"

  past MutationWrite = "mutated"
  past ReassignmentWrite = "reassigned"


makeUpper :: Text -> Text
makeUpper t = case T.unpack t of
  [] -> t
  (t:ts) -> T.pack (Char.toUpper t : ts)

asStyle = \case
  FLetDefined -> "function-style"
  NotFLetDefined -> "assignment-style"


-- type ImVarAccessCtx = Ctx ProcVar ()
type VarAccessCtx = Ctx ProcVar ([Scope], VarAccessState, ImmutType)


isIndependent :: Scope -> [Scope] -> Bool
isIndependent (Scope new) = all (\(Scope old) -> and [not (old `isSuffixOf` new), not (new `isSuffixOf` old)])

computeVarAccessType :: ProcVar -> ([Scope],VarAccessState) -> (Scope,VarAccessAction,SourceLocExt) -> MTC VarAccessState
--
-- if we have an independent location, the new vastate is always "basic"
computeVarAccessType var (a,vas) (b,ReadAction,loc)    | b `isIndependent` a = throwLocatedError (DemutationDefinitionOrderError var) loc
computeVarAccessType var (a,vas) (b,WriteAction f _,loc) | b `isIndependent` a = return (VABasicAccess f loc)
--
-- if the location is not independent, we compute the new vastate
computeVarAccessType var (a,VABasicAccess f l)       (b,ReadAction,loc)      | b `elem` a        = return (VABasicAccess f l)
computeVarAccessType var (a,VABasicAccess f l)       (b,ReadAction,loc)      | otherwise         = return (VAGlobalReadAccess (l,loc))
computeVarAccessType var (a,VABasicAccess f l)       (b,WriteAction g w,loc) | b `elem` a
                                                                             && f == g           = return (VAMultiWriteAccess f (l,[(loc,w)]))
computeVarAccessType var (a,VABasicAccess f l)       (b,WriteAction g w,loc) | b `elem` a
                                                                             && f /= g           =
                                                                               throwLocatedError (DemutationVariableAccessTypeError
                                                                                                  "A variable name cannot be used for function-style and assignment-style statements at the same time.")
                                                                                                 (let def = l in SourceQuote
                                                                                                 [(def, quote (showPretty var) <> " defined here with " <> asStyle f <> " statement")
                                                                                                 ,(loc, "attempting to use a " <> asStyle g <> " statement for " <> quote (showPretty var))
                                                                                                 ]
                                                                                                 )
computeVarAccessType var (a,VABasicAccess f l)       (b,WriteAction g w,loc) | otherwise         =
                                                                             throwLocatedError (DemutationVariableAccessTypeError
                                                                                                 (makeUpper (progressive w) <> " a variable in a different scope from where it was defined is not allowed."))
                                                                                                 (SourceQuote
                                                                                                  [ (l, quote (showPretty var) <> " defined here")
                                                                                                  , (loc, noun w <> " of " <> quote (showPretty var) <> " attempted here")
                                                                                                  ]
                                                                                                 )

computeVarAccessType var (a,VAMultiWriteAccess f l)  (b,ReadAction,loc)      | b `elem` a        = return (VAMultiWriteAccess f l)
computeVarAccessType var (a,VAMultiWriteAccess f l)  (b,ReadAction,loc)      | f == FLetDefined  = return (VAMultiWriteAccess f l)
computeVarAccessType var (a,VAMultiWriteAccess f l)  (b,ReadAction,loc)      | otherwise         =
                                                                               throwLocatedError (DemutationVariableAccessTypeError
                                                                                                  ("A variable which is reassigned or mutated after its definition cannot be read from a different scope."))
                                                                                                 (let (def,writes) = l in SourceQuote
                                                                                                  ([(def, quote (showPretty var) <> " defined here")
                                                                                                   ,(loc, "attempting to read " <> quote (showPretty var) <> " here")
                                                                                                   ]
                                                                                                   <> [(l, quote (showPretty var) <> " " <> past w <> " here") | (l,w) <- writes ]
                                                                                                  )
                                                                                                 )
computeVarAccessType var (a,VAMultiWriteAccess f l)  (b,WriteAction g w,loc) | (b `elem` a)
                                                                            && f == g           = return (VAMultiWriteAccess f (second ((loc,w):) l))
computeVarAccessType var (a,VAMultiWriteAccess f l)  (b,WriteAction g w,loc) | (b `elem` a)
                                                                            && f /= g           =
                                                                               throwLocatedError (DemutationVariableAccessTypeError
                                                                                                  "A variable name cannot be used for function-style and assignment-style statements at the same time.")
                                                                                                 (let (def,writes) = l in SourceQuote
                                                                                                 [(def, quote (showPretty var) <> " defined here with " <> asStyle f <> " statement")
                                                                                                 ,(loc, "attempting to use a " <> asStyle g <> " statement for " <> quote (showPretty var))
                                                                                                 ]
                                                                                                 )
computeVarAccessType var (a,VAMultiWriteAccess f l)  (b,WriteAction g w,loc) | otherwise        =
                                                                             throwLocatedError (DemutationVariableAccessTypeError
                                                                                                 (makeUpper (progressive w) <> " a variable in a different scope from where it was defined is not allowed."))
                                                                                                 (let (def,_) = l in SourceQuote
                                                                                                  [ (def, quote (showPretty var) <> " defined here")
                                                                                                  , (loc, noun w <> " of " <> quote (showPretty var) <> " attempted here")
                                                                                                  ]
                                                                                                 )
computeVarAccessType var (a,VAGlobalReadAccess l)    (b,ReadAction,loc)                         = return (VAGlobalReadAccess l)
computeVarAccessType var (a,VAGlobalReadAccess l)    (b,WriteAction g w,loc)                    =
                                                                             throwLocatedError (DemutationVariableAccessTypeError
                                                                                                 (makeUpper (progressive w) <> " a variable which is being read in a scope other than the one it is defined in is not allowed."))
                                                                                                 (let (def,other) = l in SourceQuote
                                                                                                  [ (def, quote (showPretty var) <> " defined here")
                                                                                                  , (other, "reading " <> quote (showPretty var) <> " in a different scope")
                                                                                                  , (loc, noun w <> " of " <> quote (showPretty var) <> " attempted here")
                                                                                                  ]
                                                                                                 )





--------------------------------------------------------------------------------------
-- The demutation monad
--------------------------------------------------------------------------------------

data MFull = MFull
  {
    _vaCtx :: VarAccessCtx
  , _memCtx :: MemCtx
  , _mutCtx :: MutCtx
  , _termVarsOfMut :: NameCtx
  , _scopeNames :: NameCtx
  , _memNames :: NameCtx
  , _memVarInfo :: MemVarInfoCtx
  , _topLevelInfo :: TopLevelInformation
  }


type MTC = LightTC Location_PrePro_Demutation MFull

$(makeLenses ''MFull)


-- new variables
newTeVarOfMut :: (MonadState MFull m) => Text -> Maybe ProcVar -> m (TeVar)
newTeVarOfMut hint original = termVarsOfMut %%= (first (\x -> GenTeVar x (UserTeVar <$> original)) . (newName GeneratedNamePriority hint))

newScopeVar :: (MonadState MFull m) => Text -> m (ScopeVar)
newScopeVar hint = scopeNames %%= (first ScopeVar . (newName GeneratedNamePriority hint))

appendNewScopeVar :: (MonadState MFull m) => Text -> Scope -> m Scope
appendNewScopeVar hint (Scope old) = do
  v <- newScopeVar hint
  return (Scope (v : old))

newMemVar :: (MonadState MFull m) => Either ProcVar Text -> MemVarInfo -> m (MemVar)
newMemVar (Left hint) mvi = do
  mv <- scopeNames %%= (first (MemVarForProcVar hint) . (newName GeneratedNamePriority ""))
  memVarInfo %= (setValue mv mvi)
  return mv
newMemVar (Right hint) mvi = do
  mv <- scopeNames %%= (first StandaloneMemVar . (newName GeneratedNamePriority hint))
  memVarInfo %= (setValue mv mvi)
  return mv

allocateMem :: Scope -> Maybe ProcVar -> MemVarInfo -> MTC (MemVar)
allocateMem scopename procvar mvi = do
  let hint = case procvar of
              Just a -> Left a
              Nothing -> Right "anon"
  mv <- newMemVar hint mvi
  mutCtx %= (setValue mv (scopename, TeVarMutTrace Nothing NotSplit []))
  return mv

cleanupMem :: Scope -> MTC ()
cleanupMem scname = mutCtx %= (\ctx -> f ctx)
  where
    f = fromKeyElemPairs . filter (\(_,(scname2,_)) -> scname2 /= scname) . getAllKeyElemPairs


instance Monad m => MonoidM m MemState where
    neutral = pure $ MemExists []

instance Monad m => CheckNeutral m MemState where
    checkNeutral a = return (a == (MemExists []))

instance Monad m => SemigroupM m MemState where
    (⋆) (MemMoved l1) (MemMoved l2) = pure (MemMoved (nub (l1 <> l2)))
    (⋆) (MemMoved l1) (MemExists _) = pure (MemMoved l1)
    (⋆) (MemExists _) (MemMoved l2) = pure (MemMoved l2)
    (⋆) (MemExists l1) (MemExists l2) = pure $ MemExists (nub (l1 ++ l2))

mergeMemCtx = (⋆!)


-----------------------------------------------------------------------------------------------------
-- Memory and VA actions
-----------------------------------------------------------------------------------------------------



--------------------------------------------------------------------------------------
-- Accessing the VA-Ctx in the MTC monad

markReassignedBase :: IsFLetDefined -> WriteKind -> Scope -> SourceLocExt -> ProcVar -> ImmutType -> MTC ()
markReassignedBase fletdef w scname loc tevar itype = do
  debug $ "[markReassignedBase]: called for " <> showT tevar <> " in " <> showT scname 

  vaCtx %=~ (markReassignedInScope scname tevar itype)

  newvatype <- getValue tevar <$> use vaCtx


  return ()

    -- The actual updating function
    where
      markReassignedInScope :: Scope -> ProcVar -> ImmutType -> VarAccessCtx -> MTC VarAccessCtx 
      markReassignedInScope scname tevar itype ctx =
        case getValue tevar ctx of
          Nothing -> return $ setValue tevar ([scname], VABasicAccess fletdef loc, itype) ctx
          Just (oldscname, oldvatype, olditype) -> do
            case olditype == itype of
              True -> do
                newvatype <- computeVarAccessType tevar (oldscname, oldvatype) (scname, WriteAction fletdef w, loc)
                debug $ "[markReassignedBase]: VA type for '" <> showT tevar <> "' changes from " <> showT oldvatype <> " to " <> showT newvatype
                return (setValue tevar (scname:oldscname, newvatype, olditype) ctx)
              False ->
                throwLocatedError
                  (DemutationError "Reassignments which change the mutation type of a variable are not allowed.")
                  (SourceQuote
                   [(getDefinitionLocation oldvatype, "definition of " <> quote (showPretty tevar) <> " with mutation type " <> quote (showPretty olditype))
                   ,(loc, "attempted reassignment of " <> quote (showPretty tevar) <> " with mutation type " <> quote (showPretty itype))
                   ]
                  )

markReassignedFLet :: Scope -> SourceLocExt -> ProcVar -> ImmutType -> MTC ()
markReassignedFLet scname loc var itype = do
  log $ "Marking flet mutated for " <> showT var
  markReassignedBase FLetDefined ReassignmentWrite scname loc var itype

--
-- Apply a mutation of `loc` locality to the `var`.
-- This might or might not change `loc`, depending on whether this variable
-- is already local or not-local.
-- The resulting locality is returned.
--
markReassigned :: WriteKind -> Scope -> SourceLocExt -> ProcVar -> ImmutType -> MTC ()
markReassigned w scname loc var itype = do
  log $ "Marking simple mutated for " <> showT var
  markReassignedBase NotFLetDefined w scname loc var itype


markRead :: Scope -> SourceLocExt -> ProcVar -> MTC ImmutType
markRead scname loc tevar = do
   debug $ "[markRead]: called for tevar" <> showT tevar <> " in " <> showT scname 
   let f v = vaCtx %=~ (markReadInScope scname v) 
        where
          markReadInScope :: Scope -> ProcVar -> VarAccessCtx -> MTC VarAccessCtx 
          markReadInScope scname tevar ctx =
            case getValue tevar ctx of
              Nothing -> throwLocatedError (DemutationDefinitionOrderError tevar) loc
              Just (oldscname, oldvatype, olditype) -> do
                newvatype <- computeVarAccessType tevar (oldscname, oldvatype) (scname, ReadAction, loc)
                return (setValue tevar (scname:oldscname,newvatype, olditype) ctx)

   f tevar

   val <- getValue tevar <$> use vaCtx 
   case val of
     Nothing -> internalError $ "Expected the procvar " <> showT tevar <> " to have an assignment because it was set just a moment ago."
     Just (_,_,itype) -> return itype

markReadMaybe :: Scope -> SourceLocExt -> Maybe ProcVar -> MTC (Maybe ImmutType)
markReadMaybe scname loc (Just x) = Just <$> markRead scname loc x
markReadMaybe scname loc Nothing = pure Nothing

markReadOverwritePrevious :: Scope -> SourceLocExt -> ProcVar -> ImmutType -> MTC ()
markReadOverwritePrevious scname loc var itype = vaCtx %%= (\scope -> ((), setValue var ([scname], VABasicAccess NotFLetDefined loc, itype) scope))


cleanupVACtxAfterScopeEnd :: VarAccessCtx -> MTC ()
cleanupVACtxAfterScopeEnd vaCtxBefore = do
  --
  -- if a procvar was not in the vactx before,
  -- it means that it is localnd thus should be removed.
  let restoreArg procvar = do
        case getValue procvar vaCtxBefore of
          Nothing       -> vaCtx %%= (\ctx -> ((), deleteValue procvar ctx))
          Just oldvalue -> pure ()
  --
  -- We do this for all vars in the current vactx
  vaCtxAfter <- use vaCtx
  mapM_ restoreArg (getAllKeys vaCtxAfter)



--------------------------------------------------------------------------------------

markMutated :: ProcVar -> SourceLocExt -> DMPersistentMessage MTC -> MTC TeVar
markMutated pv loc msg = do
  mv <- expectSingleMem msg =<< expectNotMoved loc pv
  tevar <- newTeVarOfMut (showT mv) (Just pv)
  let f ctx = do
        case getValue mv ctx of
          Nothing -> impossible $ "Wanted to mark the memvar " <> showT mv <> " as mutated, but it was not in the mutctx."
          Just (scvar, TeVarMutTrace pv split tevars) -> return $ setValue mv (scvar, TeVarMutTrace pv split ((tevar,[loc]):tevars)) ctx

  mutCtx %=~ f
  return tevar




--------------------------------------------------------------------------------
-- immuttype access
--------------------------------------------------------------------------------

expectImmutType :: Scope -> SourceLocExt -> ProcVar -> MTC ImmutType
expectImmutType = markRead

setImmutType :: WriteKind -> Scope -> SourceLocExt -> ProcVar -> ImmutType -> MTC ()
setImmutType = markReassigned

backupAndSetImmutType :: Scope -> SourceLocExt -> ProcVar -> ImmutType -> MTC (Maybe ImmutType)
backupAndSetImmutType scname loc procvar itype = do
  oldVal <- getValue procvar <$> use vaCtx
  case oldVal of
    Nothing          -> setImmutType ReassignmentWrite scname loc procvar itype >> return Nothing
    Just (_,_,itype) -> setImmutType ReassignmentWrite scname loc procvar itype >> return (Just itype)

setImmutTypeFLetDefined :: Scope -> SourceLocExt -> ProcVar -> ImmutType -> MTC ()
setImmutTypeFLetDefined = markReassignedFLet

setImmutTypeOverwritePrevious :: Scope -> SourceLocExt -> ProcVar -> ImmutType -> MTC ()
setImmutTypeOverwritePrevious = markReadOverwritePrevious


--------------------------------------------------------------------------------
-- memory access
--------------------------------------------------------------------------------



-- change last move Loc for memvars
setLastAssignmentLocMemVar :: SourceLocExt -> MemVar -> MTC ()
setLastAssignmentLocMemVar loc mv = do
  memVarInfo <%= changeValue mv (\(MemVarInfo a _) -> (MemVarInfo a loc))
  return ()

-- change last move Loc for memtypes
setLastAssignmentLocMem :: SourceLocExt -> MemType -> MTC ()
setLastAssignmentLocMem loc = \case
  TupleMem mts  -> mapM_ (setLastAssignmentLocMem loc) mts
  SingleMem mv  -> setLastAssignmentLocMemVar loc mv
  RefMem mv     -> setLastAssignmentLocMemVar loc mv



--
-- We have:
-- ```
-- Prelude> oneOfEach [[1,2], [10,20,30], [100]]
-- [[1,10,100],[1,20,100],[1,30,100],[2,10,100],[2,20,100],[2,30,100]]
-- ```
--
oneOfEach :: [[a]] -> [[a]]
oneOfEach (xs:yss) = let yss' = oneOfEach yss
                     in ([x:ys' | x <- xs, ys' <- yss'])
oneOfEach [] = [[]]



moveGetMem_Loc :: Scope -> SourceLocExt -> Maybe ProcVar-> LocMoveType -> MTC [MemType]
moveGetMem_Loc scname loc pv (Located _ mt) = moveGetMem scname loc pv mt

moveGetMem :: Scope -> SourceLocExt -> Maybe ProcVar -> MoveType -> MTC [MemType]
moveGetMem scname loc pv (NoMove te) = do
  mem <- allocateMem scname pv (MemVarInfo NotFunctionArgument loc)
  return [(SingleMem mem)]
moveGetMem scname loc pv (SingleMove a) = do
  memstate <- expectNotMoved loc a
  mapM (setLastAssignmentLocMem loc) memstate -- set last assignment loc for information purposes
  memCtx %= (setValue a (MemMoved [loc]))
  return (memstate)
moveGetMem scname loc pv (PhiMove _ (mt1,_) (mt2,_)) = do
  memt1 <- moveGetMem_Loc scname loc Nothing mt1
  memt2 <- moveGetMem_Loc scname loc Nothing mt2
  return (memt1 <> memt2)
moveGetMem scname loc pv (TupleMove as) = do
  mems <- mapM (moveGetMem_Loc scname loc Nothing) as
  return (TupleMem <$> oneOfEach mems)
moveGetMem scname loc pv (RefMove te) = do
  -- if we had a reference,
  -- allocate new memory for it
  memvar <- allocateMem scname pv (MemVarInfo NotFunctionArgument loc)
  pure $ [RefMem memvar]



setMem :: ProcVar -> [MemType] -> MTC () 
setMem x mt = do
  -- set the memory type for procvar `x`
  memCtx %= (setValue x (MemExists mt))

  -- set the owner of the SingleVars in `mt`
  let smt = [s | SingleMem s <- mt]
  let setOwner s = do
        mutCtx <%= changeValue s (\(scopeVar, TeVarMutTrace oldOwner split trace) -> (scopeVar, TeVarMutTrace (Just x) split trace))

  mapM_ setOwner smt

setMemMaybe :: Maybe ProcVar -> [MemType] -> MTC () 
setMemMaybe (Just x) mt = setMem x mt
setMemMaybe (Nothing) _ = pure ()


setMemTupleInManyMems :: SourceLocExt -> Scope -> [ProcVar] -> [MemType] -> MTC ()
setMemTupleInManyMems loc scname xs mems = mapM_ (setMemTuple loc scname xs) mems

setMemTuple :: SourceLocExt -> Scope -> [ProcVar] -> MemType -> MTC ()
setMemTuple loc scname xs (SingleMem a) = do
  -- we get the memory info of the input var
  mvictx <- use memVarInfo
  MemVarInfo ifa _ <- case getValue a mvictx of
        Nothing -> internalError $ "Expected the memvariable " <> showT a <> " to have an info entry."
        Just ifa -> return ifa

  -- We are deconstructing a tuple value,
  -- need to create memory locations for all parts
  let f (x) = do
        mx <- allocateMem scname (Just x) (MemVarInfo ifa loc) -- NOTE: We update the `lastAssignmentLoc` here for RHS!
        setMem x [SingleMem mx]
        return mx
  memvars <- mapM f xs

  -- furthermore we mark the rhs mem location as split
  rhs_mut <- getValue a <$> use mutCtx

  case rhs_mut of
    Nothing -> internalError $ "Expected the memory location " <> showT a <> " to have a mutation status."
    Just (scvar,TeVarMutTrace pv _ ts) -> mutCtx %= (setValue a (scvar, TeVarMutTrace pv (Split [loc] memvars) ts))

setMemTuple loc scname xs (RefMem a) = do
  mapM_ (\(x) -> setMemMaybe x ([RefMem a])) (Just <$> xs)

setMemTuple loc scname xs (TupleMem as) | length xs == length as = do
  let xas = zip xs as
  mapM_ (\(x, a) -> setMem x [a]) xas

setMemTuple loc scname xs (TupleMem as) | otherwise = demutationError ("Trying to assign a tuple where lengths do not match.")
                                                                      (loc :\\:
                                                                       ("The LHS has length " <> showT (length xs) <> ", while the RHS has length " <> showT (length as) <> ".") :\\:
                                                                       "" :\\:
                                                                       ("Debug info: the inferred memory state is: " <> showT xs <> " = " <> showT as)
                                                                      )

expectNotMoved :: SourceLocExt -> ProcVar -> MTC [MemType]
expectNotMoved loc tevar = do
  mc <- use memCtx
  case getValue tevar mc of
    Nothing          -> throwLocatedError (DemutationDefinitionOrderError $ tevar) (DMPersistentMessage @MTC loc)
    Just (MemMoved movedlocs) -> do
      let edits = (loc, "trying to access " <> quote (showPretty tevar)) :
                  [(l, "content of " <> quote (showPretty tevar) <> " is already moved away here") | l <- movedlocs]

      throwLocatedError (DemutationMovedVariableAccessError tevar) (SourceQuote edits)
                                      
    Just (MemExists a) -> pure a



-------------------------------------
-- accessing memories

getAllMemVars :: MemType -> [MemVar]
getAllMemVars (SingleMem a) = [a]
getAllMemVars (TupleMem a) = a >>= getAllMemVars
getAllMemVars (RefMem a) = [a]

getAllMemVarsOfMemState :: MemState -> [MemVar]
getAllMemVarsOfMemState (MemExists ms) = ms >>= getAllMemVars
getAllMemVarsOfMemState (MemMoved _) = []

expectSingleMem :: DMPersistentMessage MTC -> [MemType] -> MTC MemVar
expectSingleMem msg mts = do
  case mts of
    [mt] -> case mt of
              (SingleMem a) -> pure a
              mem@(TupleMem as) -> demutationError ("Encountered a value spanning multiple memory locations where a single location value was expected.")
                                       (msg :\\:
                                        ("The encountered memory type is " <> showT mem))
              mem@(RefMem as) -> demutationError ("Encountered a value which is a non-mutable reference to an element in a vector/matrix where a single memory location was expected.")
                                       (msg :\\:
                                        ("The encountered memory type is " <> showT mem))
    mts -> demutationError ("Encountered a value spanning multiple possible memory locations where a single location value was expected.")
                                       (msg :\\:
                                        ("The encountered memory type is " <> showT mts))




getMemVarMutationStatus :: MemVar -> MTC (IsSplit, [(TeVar,[SourceLocExt])])
getMemVarMutationStatus mv = do
  mctx <- use mutCtx
  case getValue mv mctx of
    Nothing -> internalError $ "Expected memory location to have a mutation status, but it didn't. MemVar: " <> showT mv
    Just (_, TeVarMutTrace _ split tvars) -> return (split,tvars)


coequalizeTeVarMutTrace :: TeVarMutTrace -> TeVarMutTrace -> WriterT ([LocDemutDMTerm],[LocDemutDMTerm]) MTC TeVarMutTrace
coequalizeTeVarMutTrace (TeVarMutTrace pv1 split1 ts1) (TeVarMutTrace pv2 split2 ts2) | and [ts1 == ts2, pv1 == pv2, split1 == split2] = pure $ TeVarMutTrace pv1 split1 ts1
coequalizeTeVarMutTrace (TeVarMutTrace pv1 split1 ts1) (TeVarMutTrace pv2 split2 ts2)  = do
  t3 <- newTeVarOfMut "phi" Nothing
  let makeProj (Just pv) []            = pure $ (Extra (DemutSLetBase PureLet (t3) (notLocated $ Var (UserTeVar pv))), [])
      makeProj Nothing   []            = lift $ throwUnlocatedError $ DemutationError $ "While demutating phi encountered a branch where a proc-var-less memory location is mutated. This cannot be done."
      makeProj _         ((t,locs):ts) = pure $ (Extra (DemutSLetBase PureLet (t3) (notLocated $ Var (t))), locs)

  (proj1,locs1) <- makeProj pv1 ts1 
  (proj2,locs2) <- makeProj pv2 ts2

  lift $ debug $ "Coequalizing MutTraces:\n"
  lift $ debug $ "  proj1: " <> showT proj1
  lift $ debug $ "  proj2: " <> showT proj2

  -- we check whether the muttraces belong to the same procvars
  case pv1 == pv2 of
    --
    -- if they don't then this memory location cannot be used anymore after the if
    False -> return $ TeVarMutTrace Nothing NotSplit ([])
    --
    -- if they do, we can actually coequalize
    True -> do
      tell ([notLocated proj1],[notLocated proj2])

      let pv3 = pv1

      split3 <- case (split1,split2) of
                  (NotSplit, NotSplit) -> pure NotSplit
                  (NotSplit, Split l a) -> pure (Split l a)
                  (Split l a, NotSplit) -> pure (Split l a)
                  (Split l1 a, Split l2 b) -> pure (Split (l1 <> l2) (a <> b))

      pure $ TeVarMutTrace pv3 split3 ((t3,locs1<>locs2) : ts1 <> ts2)



instance SemigroupM (WriterT ([LocDemutDMTerm],[LocDemutDMTerm]) MTC) TeVarMutTrace where
  (⋆) = coequalizeTeVarMutTrace
instance MonoidM (WriterT ([LocDemutDMTerm],[LocDemutDMTerm]) MTC) TeVarMutTrace where
  neutral = pure $ TeVarMutTrace Nothing NotSplit []
instance CheckNeutral (WriterT ([LocDemutDMTerm],[LocDemutDMTerm]) MTC) TeVarMutTrace where
  checkNeutral _ = pure False

instance SemigroupM (WriterT ([LocDemutDMTerm],[LocDemutDMTerm]) MTC) Scope where
  (⋆) a b | a == b    = pure a
  (⋆) a b | otherwise = lift $ throwUnlocatedError $ DemutationError $ "While demutating phi, encountered two branches where the scopevars of a memvar differ. This is not allowed."
instance MonoidM (WriterT ([LocDemutDMTerm],[LocDemutDMTerm]) MTC) Scope where
  neutral = lift $ internalError $ "There is no neutral element for scopevars"

instance CheckNeutral (WriterT ([LocDemutDMTerm],[LocDemutDMTerm]) MTC) Scope where
  checkNeutral _ = pure False

coequalizeMutCtx :: MutCtx -> MutCtx -> MTC (MutCtx, ([LocDemutDMTerm], [LocDemutDMTerm]))
coequalizeMutCtx muts1 muts2 = runWriterT (muts1 ⋆ muts2)



--------------------------------------------------------------------------
-- Creating TeVars from MemVars
--


getLastAssignedLocs :: MemType -> MTC [SourceLocExt]
getLastAssignedLocs mt = do
  mvinfo <- use memVarInfo
  let mvs = getAllMemVars mt
  let f mv = case getValue mv mvinfo of
               Nothing -> []
               Just mvi -> [_lastAssignmentLocInfo mvi]
  return (f =<< mvs)

--
-- | Create a tevar for a procvar.
--    If procvar contains a memory location which is
--    a `SingleMem` and is mutatedse the newest variable
--    name from the `mutCtx`. Else create a tvar based on the
--    input name `mv`.
--
--    Since there are multiple memory types associated to
--    a procvar, they are dealt with as follows:
--    There are two valid possibilities:
--    1. all memory types do not contain mutated variables
--    2. all memory types are single varnd all are mutated,
--       with last tevar being the same
procVarAsTeVar :: ProcVar -> SourceLocExt -> MTC TeVar
procVarAsTeVar pv loc = do
  mts <- expectNotMoved loc pv
  --
  -- all memory types which contain mutated vars
  let getMutatedName x = do
        (_,mmut) <- getMemVarMutationStatus x
        case mmut of
          []     -> return []
          (x:xs) -> return [x]
  mut_mts <- join <$> mapM getMutatedName (getAllMemVars =<< mts)
  --
  -- if we have no mutations, we are done
  case fst <$> mut_mts of
    []     -> pure (UserTeVar pv)
    --
    -- if there are mutations, we need
    -- to make sure that all tevars are the same
    (x:xs) -> case all (== x) xs of
      False -> do
        let makeMessage (i, mt) = do
              locs <- getLastAssignedLocs mt
              return [(l, quote (showPretty pv) <> " assigned in execution branch " <> showPretty i) | l <- locs]

        messages <- (mapM makeMessage (zip [1..] mts))
        let messages' = (loc,quote (showPretty pv) <> " is used here"):join messages

        demutationError ("Illegal variable assignment combination.")
                 ("The variable " :<>: Quote pv :<>: " is being assigned different memory locations in different execution branches." :\\:
                 SourceQuote messages' :\\:
                 ("This is not allowed. A possible fix could be to write `" <> showPretty pv <> " = clone(...)` instead.") :\\:
                 "" :\\:
                 ("Debug Info: Inferred memory type is:" <> showT mts)
                 )

      True  -> pure x

procVarAsTeVarInMutCtx :: MemCtx -> MutCtx -> SourceLocExt -> ProcVar -> MTC TeVar
procVarAsTeVarInMutCtx tempMemCtx tempMutCtx msg pv = do
  oldMutCtx <- use mutCtx
  oldMemCtx <- use memCtx
  mutCtx .= tempMutCtx
  memCtx .= tempMemCtx
  val <- procVarAsTeVar pv msg
  mutCtx .= oldMutCtx
  memCtx .= oldMemCtx
  return val

moveTypeAsTerm_Loc :: SourceLocExt -> LocMoveType -> MTC LocDemutDMTerm
moveTypeAsTerm_Loc msg = mapM (moveTypeAsTerm msg)

moveTypeAsTerm :: SourceLocExt -> MoveType -> MTC DemutDMTerm
moveTypeAsTerm msg = \case
  TupleMove mts -> do
    terms <- mapM (moveTypeAsTerm_Loc msg) mts
    pure $ (Tup terms)
  SingleMove pv -> do tv <- procVarAsTeVar pv msg ; pure $ Var $ (tv)
  PhiMove cond (_,tt1) (_,tt2) -> return (Extra (DemutPhi cond tt1 tt2))
  RefMove pdt   -> pure pdt
  NoMove pdt    -> pure pdt


movedVarsOfMoveType_Loc :: LocMoveType -> [ProcVar]
movedVarsOfMoveType_Loc = movedVarsOfMoveType . getLocated

movedVarsOfMoveType :: MoveType -> [ProcVar]
movedVarsOfMoveType = \case
  TupleMove mts -> mts >>= movedVarsOfMoveType_Loc
  SingleMove pv -> return pv
  PhiMove cond (mt1,_) (mt2,_) -> movedVarsOfMoveType_Loc mt1 <> movedVarsOfMoveType_Loc mt2
  RefMove pdt -> []
  NoMove pdt -> []

termTypeAsTerm :: SourceLocExt -> TermType -> MTC LocDemutDMTerm
termTypeAsTerm msg = \case
  Value it mt -> moveTypeAsTerm_Loc msg mt
  Statement l pdt mt -> do
    mt' <- moveTypeAsTerm msg mt
    pure $ Located l $ Extra $ DemutBlock [Located l pdt, Located l mt']
  StatementWithoutDefault l pdt -> pure $ Located l $ Extra $ DemutBlock [Located l pdt]
  MutatingFunctionEnd l       -> pure $ Located l $ Extra $ DemutBlock []


