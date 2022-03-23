
{-# LANGUAGE UndecidableInstances #-}


module DiffMu.Abstract.Class.Constraint where

import DiffMu.Prelude
import DiffMu.Abstract.Class.IsT
import DiffMu.Abstract.Class.Log
import DiffMu.Abstract.Class.Term
import DiffMu.Abstract.Data.Error
import DiffMu.Abstract.Data.ErrorReporting
import DiffMu.Core.Logging
-- import DiffMu.Abstract.Class.MonadTerm
import Debug.Trace

default (Text)

data SolvingMode = SolveExact | SolveAssumeWorst | SolveGlobal | SolveFinal | SolveSpecial
  deriving (Eq)

instance Show SolvingMode where
  show SolveExact = "exact"
  show SolveAssumeWorst = "worst"
  show SolveGlobal = "global"
  show SolveFinal = "final"
  show SolveSpecial = "special"

instance Monad m => Normalize m SolvingMode where
  normalize _ = pure


-- instance FreeVars SVarOf SolvingMode where

-- instance Ord SolvingMode where
--   SolveExact <= a = True
--   SolveAssumeWorst <= SolveExact = False
--   SolveAssumeWorst <= SolveAssumeWorst = True

class TCConstraint c where
  constr :: a -> c a
  runConstr :: c a -> a

  insideConstr :: (Monad t) => (a -> t a) -> c a -> t (c a)
  insideConstr f c = constr <$> f (runConstr c)

class TCConstraint c => Solve (isT :: (* -> *) -> Constraint) c a where
  solve_ :: Dict ((IsT isT t)) -> SolvingMode -> Symbol -> c a -> t ()

class MonadNormalize t where
  normalizeState :: NormalizationType -> t ()

data Solvable  (extraConstr :: * -> Constraint) (extraContentConstr :: * -> Constraint) isT where
  Solvable :: (Solve isT c a, (HasNormalize isT a), Show (c a), Typeable c, Typeable a, extraContentConstr a, extraConstr (c a)) => c a -> Solvable extraConstr extraContentConstr isT

-- solve' :: (Solve isT c a, IsT isT t, Normalize (t) a) => c a -> t ()
solve :: (Monad (t), IsT isT t) => SolvingMode -> Symbol -> (Solvable eC eC2 isT) -> t ()
solve mode name (Solvable (c :: c a) :: Solvable eC eC2 isT) = f Proxy
  where f :: (Monad (t), IsT isT t) => Proxy (t) -> t ()
        f (_ :: Proxy (t)) = (insideConstr normalizeExact c >>= solve_ @isT Dict mode name)


instance (isT t, Monad (t)) => Normalize (t) (Solvable eC eC2 isT) where
  normalize nt (Solvable (c :: c a)) = (Solvable @isT <$> insideConstr (normalize @(t) nt) c)

instance Show (Solvable eC eC2 isT) where
  show (Solvable c) = show c

instance ShowPretty (Solvable eC eC2 isT) where
  showPretty = show

data CloseConstraintSetResult = ConstraintSet_WasEmpty | ConstraintSet_WasNotEmpty

class (Monad t) => MonadConstraint isT t | t -> isT where
-- class (IsT isT t) => MonadConstraint v isT t e | t -> isT where
  type ContentConstraintOnSolvable t :: * -> Constraint
  type ConstraintOnSolvable t :: * -> Constraint
  type ConstraintBackup t
  addConstraint :: (Normalize t a, ShowPretty a, Show a) => Solvable (ConstraintOnSolvable t) (ContentConstraintOnSolvable t) isT -> a -> t Symbol
  getUnsolvedConstraintMarkNormal :: [SolvingMode] -> t (Maybe (Symbol , Solvable (ConstraintOnSolvable t) (ContentConstraintOnSolvable t) isT, SolvingMode, DMPersistentMessage t))
  dischargeConstraint :: Symbol -> t ()
  failConstraint :: Symbol -> t ()
  updateConstraint :: Symbol -> Solvable (ConstraintOnSolvable t) (ContentConstraintOnSolvable t) isT -> t ()
  openNewConstraintSet :: t ()
  mergeTopConstraintSet :: t CloseConstraintSetResult
  logPrintConstraints :: t ()
  logPrintSubstitutions :: t ()
  getConstraintsByType :: (Typeable c, Typeable a) => Proxy (c a) -> t [(Symbol, c a)]
  getConstraintMessage :: Symbol -> t (DMPersistentMessage t)
  getConstraint :: Symbol -> t (Solvable (ConstraintOnSolvable t) (ContentConstraintOnSolvable t) isT, DMPersistentMessage t)
  getAllConstraints :: t [(Symbol, Solvable (ConstraintOnSolvable t) (ContentConstraintOnSolvable t) isT)]
  clearSolvingEvents :: t [String]

inheritanceMessageFromName name = do
    (c,msg) <- getConstraint name
    return
      (("Inherited from the constraint:" :: Text) :\\:
       ("  " :: Text) :<>: c :\\:
       msg
      )

addConstraintNoMessage solvable = addConstraint solvable ()
addConstraintFromName name solvable = do
    (c,msg) <- getConstraint name
    addConstraint solvable
      (("Inherited from the constraint:" :: Text) :\\:
       ("  " :: Text) :<>: c :\\:
       msg
      )

addConstraintFromNameMaybe (Just name) = addConstraintFromName name
addConstraintFromNameMaybe (Nothing)   = addConstraintNoMessage




(==!) :: (MessageLike t msg, MonadConstraint isT t, Solve isT IsEqual (a,a), (HasNormalize isT a), Show (a), Typeable a, IsT isT t, ContentConstraintOnSolvable t (a,a), ConstraintOnSolvable t (IsEqual (a,a))) => a -> a -> msg -> t ()
(==!) a b msg = addConstraint (Solvable (IsEqual (a,b))) msg >> pure ()

-- An abbreviation for adding a less equal constraint.
(≤!) :: (MessageLike t msg, MonadConstraint isT t, Solve isT IsLessEqual (a,a), (HasNormalize isT a), Show (a), Typeable a, IsT isT t, ContentConstraintOnSolvable t (a,a), ConstraintOnSolvable t (IsLessEqual (a,a))) => a -> a -> msg -> t ()
(≤!) a b msg = addConstraint (Solvable (IsLessEqual (a,b))) msg >> pure ()


-- Basic constraints
newtype IsEqual a = IsEqual a
  deriving (Show)

instance TCConstraint IsEqual where
  constr = IsEqual
  runConstr (IsEqual c) = c


---- Less Equal (subtyping)
newtype IsLessEqual a = IsLessEqual a
  deriving (Show)

instance TCConstraint IsLessEqual where
  constr = IsLessEqual
  runConstr (IsLessEqual c) = c

---- Less (for sensitivities)
newtype IsLess a = IsLess a
  deriving (Show)

instance TCConstraint IsLess where
  constr = IsLess
  runConstr (IsLess c) = c

---- Sups
newtype IsSupremum a = IsSupremum a deriving Show

instance TCConstraint IsSupremum where
  constr = IsSupremum
  runConstr (IsSupremum c) = c

---- Infimum
newtype IsInfimum a = IsInfimum a deriving Show

instance TCConstraint IsInfimum where
  constr = IsInfimum
  runConstr (IsInfimum c) = c

---- Choices
newtype IsChoice a = IsChoice a deriving Show

instance TCConstraint IsChoice where
  constr = IsChoice
  runConstr (IsChoice c) = c

---- Functions/Privacy Functions
newtype IsFunction a = IsFunction a deriving Show

instance TCConstraint IsFunction where
  constr = IsFunction
  runConstr (IsFunction c) = c


----------------------------------------------------------
-- functions for Constraint


-- Iterates over all constraints which are currently in a "changed" state, and tries to solve them.
-- Returns if no "changed" constraints remains.
-- An unchanged constraint is marked "changed", if it is affected by a new substitution.
-- A changed constraint is marked "unchanged" if it is read by a call to `getUnsolvedConstraintMarkNormal`.
solveAllConstraints :: forall isT t eC e. (MonadDMError e t, MonadImpossible t, MonadLog t, MonadConstraint isT t, MonadNormalize t, IsT isT t) => NormalizationType -> [SolvingMode] -> t ()
solveAllConstraints nt modes = withLogLocation "Constr" $ do

  -- get events which came before us
  oldEvents <- clearSolvingEvents
  case oldEvents of
    [] -> pure ()
    xs -> do
      log $ "[Solver]: Before solving all constraints, the following events have accumulated unnoticed:"
      log $ intercalate "\n" (fmap ("           - " <>) xs)
      log ""


  normalizeState nt
  openConstr <- getUnsolvedConstraintMarkNormal modes

  case openConstr of
    Nothing -> return ()
    Just (name, constr, mode, constr_desc) -> do
      -- debug $ "[Solver]: Notice: BEFORE solving (" <> show mode <> ") " <> show name <> " : " <> show constr
      -- logPrintConstraints
      -- logPrintSubstitutions

      catchAndPersist (solve mode name constr) $ \msg -> do
        dischargeConstraint name
        let msg' = "The constraint" :<>: name :<>: ":" :<>: constr :\\:
                  "could not be solved:"
                  :-----:
                  constr_desc
                  :-----:
                  msg
        return ((),msg')
      -- catchError (solve mode name constr) $ \(WithContext err ctx) -> do
      --   crit <- isCritical err
      --   case crit of
      --     True -> throwError err
      --     False -> do
      --       let changeMsg :: DMPersistentMessage t -> DMPersistentMessage t
      --           changeMsg (DMPersistentMessage msg) = DMPersistentMessage $ 
      --             "The constraint" :<>: name :<>: ":" :<>: constr
      --             :\\:
      --             "could not be solved:"
      --             :\\:
      --             msg
      --       persistentError (changeMsg (getPersistentErrorMessage err))
      --       dischargeConstraint name

      -- debug $ "[Solver]: Notice: AFTER solving (" <> show mode <> ") " <> show name <> " : " <> show constr

      -- check whether constraint disappeared
      allCs <- getAllConstraints
      let newConstrValue = filter (\(n',val) -> n' == name) allCs
      bDischarged <- case newConstrValue of
        []        -> pure True
        [(_,val)] -> pure False
        _ -> impossible "Found multiple constraints with the same name."

      -- check for events which happened
      events <- clearSolvingEvents

      -- print if something notable happened
      case (bDischarged, events) of
        (False,[]) -> pure ()
        (b,xs) -> do
          log $ "[Solver]: solving (" <> show mode <> ") " <> show name <> " : " <> show constr
          log $ intercalate "\n" (fmap ("             - " <>) xs)
          log $ "          => " <> if b then green "Discharged" else yellow "Wait/Update"

      solveAllConstraints nt modes

solvingAllNewConstraints :: (MonadDMError e t, MonadImpossible t, MonadLog t, MonadConstraint isT t, MonadNormalize t, IsT isT t) => NormalizationType -> [SolvingMode] -> t a -> t (CloseConstraintSetResult, a)
solvingAllNewConstraints nt modes f = withLogLocation "Constr" $ do
  log ""
  log "============ BEGIN solve all new constraints >>>>>>>>>>>>>>>>"
  openNewConstraintSet
  logPrintConstraints
  res <- f
  solveAllConstraints nt modes
  log "============ AFTER solving all new constraints >>>>>>>>>>>>>>>>"
  logPrintConstraints
  closeRes <- mergeTopConstraintSet
  log "============ AFTER merging constraint sets >>>>>>>>>>>>>>>>"
  logPrintConstraints
  log "============ END solve all new constraints <<<<<<<<<<<<<<<<"
  return (closeRes, res)


solveAndNormalize :: forall a isT t eC e. (MonadDMError e t, MonadImpossible t, MonadLog t, MonadConstraint isT t, MonadNormalize t, IsT isT t, Normalize t a, Show a) => NormalizationType -> [SolvingMode] -> a -> t a
solveAndNormalize nt modes value = f 4 value
  where
    f :: Int -> a -> t a
    f n a0 | n <= 0 = impossible "Solving & normalizing needed more than 4 iterations. Cancelling."
    f n a0          = do

      -- get all constraint names
      allCs0 <- getAllConstraints
      let allNames0 = fst <$> allCs0

      solveAllConstraints nt modes
      debug $ "================================================"
      debug $ "Solved constraints as far as possible."
      debug $ "Now normalizing type."
      a1 <- normalize nt a0
      debug $ "Old type: " <> show a0
      debug $ "New type: " <> show a1

      allCs1 <- getAllConstraints
      let allNames1 = fst <$> allCs1

      case allNames0 == allNames1 of
        True  -> return a1
        False -> f (n-1) a1




