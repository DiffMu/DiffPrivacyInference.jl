{-# LANGUAGE UndecidableInstances #-}

{- |
Description: System for generic constraint solving.

Consists of:
  1. A class `TCConstraint` for specifying new constraint types
     as functors isomorphic to the identity functor.
  2. A class `Solvable` for specifying how a given constraint type
     can be solved in a given class of monads.
  3. A class `MonadConstraint` for monads which provide primitives for
     constraint solving: creating, updating, discharging, getting constraints.
-}
module DiffMu.Abstract.Class.Constraint where

import DiffMu.Prelude
import DiffMu.Abstract.Class.IsT
import DiffMu.Abstract.Class.Log
import DiffMu.Abstract.Class.Term
import DiffMu.Abstract.Data.Error
import DiffMu.Core.Logging
import Debug.Trace
import qualified Data.Text as T

default (Text)

---------------------------------------------------------------------------------
-- Solving Mode
---------------------------------------------------------------------------------
data SolvingMode = SolveExact | SolveRecreateSupremum | SolveAssumeWorst | SolveGlobal | SolveFinal | SolveSpecial
  deriving (Eq)

instance Show SolvingMode where
  show SolveExact = "exact"
  show SolveRecreateSupremum = "recreate_supremum" -- NOTE: this is only to be used in monadic graph search
  show SolveAssumeWorst = "worst"
  show SolveGlobal = "global"
  show SolveFinal = "final"
  show SolveSpecial = "special"
  
instance ShowPretty SolvingMode where
    showPretty = T.pack . show

instance Monad m => Normalize m SolvingMode where
  normalize _ = pure



---------------------------------------------------------------------------------
-- TCConstraint & Solvable
---------------------------------------------------------------------------------
class TCConstraint c where
  constr :: a -> c a
  runConstr :: c a -> a

  insideConstr :: (Monad t) => (a -> t a) -> c a -> t (c a)
  insideConstr f c = constr <$> f (runConstr c)

class TCConstraint c => Solve (isT :: (* -> *) -> Constraint) c a where
  solve_ :: Dict ((IsT isT t)) -> SolvingMode -> IxSymbol -> c a -> t ()

data Solvable  (extraConstr :: * -> Constraint) (extraContentConstr :: * -> Constraint) isT where
  Solvable :: (Solve isT c a, (HasNormalize isT a), Show (c a), ShowPretty (c a), Eq (c a), Typeable c, Typeable a, extraContentConstr a, extraConstr (c a)) => c a -> Solvable extraConstr extraContentConstr isT

solve :: (Monad (t), IsT isT t) => SolvingMode -> IxSymbol -> (Solvable eC eC2 isT) -> t ()
solve mode name (Solvable (c :: c a) :: Solvable eC eC2 isT) = f Proxy
  where f :: (Monad (t), IsT isT t) => Proxy (t) -> t ()
        f (_ :: Proxy (t)) = (insideConstr normalizeExact c >>= solve_ @isT Dict mode name)


instance (isT t, Monad (t)) => Normalize (t) (Solvable eC eC2 isT) where
  normalize nt (Solvable (c :: c a)) = (Solvable @isT <$> insideConstr (normalize @(t) nt) c)

instance Show (Solvable eC eC2 isT) where
  show (Solvable c) = show c

instance Eq (Solvable eC eC2 isT) where
  (Solvable (ca :: c a)) == (Solvable (db :: d b)) = 
    let case0 = testEquality (typeRep @(c a)) (typeRep @(d b))
    in case case0 of
      Just Refl -> ca == db
      Nothing   -> False

instance (ShowPretty a, ShowPretty b) => ShowPretty (a :=: b) where
  showPretty (a :=: b) = showPretty a <> " :=: " <> showPretty b


instance ShowPretty (Solvable eC eC2 isT) where
  showPretty (Solvable c) = showPretty c

instance ShowLocated (Solvable eC eC2 isT) where
  showLocated = pure . showPretty

data CloseConstraintSetResult = ConstraintSet_WasEmpty | ConstraintSet_WasNotEmpty


---------------------------------------------------------------------------------
-- `MonadConstraint` class
---------------------------------------------------------------------------------
class MonadNormalize t where
  normalizeState :: NormalizationType -> t ()

class (Monad t) => MonadConstraint isT t | t -> isT where
  type ContentConstraintOnSolvable t :: * -> Constraint
  type ConstraintOnSolvable t :: * -> Constraint
  type ConstraintBackup t
  addConstraint :: (MessageLike t a) => Solvable (ConstraintOnSolvable t) (ContentConstraintOnSolvable t) isT -> a -> t IxSymbol
  getUnsolvedConstraintMarkNormal :: [SolvingMode] -> t (Maybe (IxSymbol , Solvable (ConstraintOnSolvable t) (ContentConstraintOnSolvable t) isT, SolvingMode, DMPersistentMessage t))
  nubConstraints :: t ()
  dischargeConstraint :: IxSymbol -> t ()
  markFailedConstraint :: IxSymbol -> t ()
  failConstraint :: IxSymbol -> t ()
  updateConstraint :: IxSymbol -> Solvable (ConstraintOnSolvable t) (ContentConstraintOnSolvable t) isT -> t ()
  openNewConstraintSet :: t ()
  mergeTopConstraintSet :: t CloseConstraintSetResult
  logPrintConstraints :: t ()
  logPrintSubstitutions :: t ()
  getConstraintsByType :: (Typeable c, Typeable a) => Proxy (c a) -> t [(IxSymbol, c a)]
  getConstraintMessage :: IxSymbol -> t (DMPersistentMessage t)
  getConstraint :: IxSymbol -> t (Solvable (ConstraintOnSolvable t) (ContentConstraintOnSolvable t) isT, DMPersistentMessage t)
  getAllConstraints :: t [(IxSymbol, Solvable (ConstraintOnSolvable t) (ContentConstraintOnSolvable t) isT)]
  clearSolvingEvents :: t [Text]





---------------------------------------------------------------------------------
-- Using the `MonadConstraint` interface
---------------------------------------------------------------------------------

inheritanceMessageFromName name = do
    (c,msg) <- getConstraint name
    return
      (("Inherited from the constraint: " :: Text) :\\->:
       (c :\\:
       msg
       )
      )

addConstraintNoMessage :: MonadConstraint isT t => Solvable (ConstraintOnSolvable t) (ContentConstraintOnSolvable t) isT -> t IxSymbol
addConstraintNoMessage solvable = addConstraint solvable ()

addConstraintFromName :: (isT m, MonadConstraint isT m) => IxSymbol -> Solvable (ConstraintOnSolvable m) (ContentConstraintOnSolvable m) isT -> m IxSymbol
addConstraintFromName name solvable = do
    msg <- inheritanceMessageFromName name
    addConstraint solvable msg

addConstraintFromNameMaybe :: (isT m, MonadConstraint isT m) => Maybe IxSymbol -> Solvable (ConstraintOnSolvable m) (ContentConstraintOnSolvable m) isT -> m IxSymbol
addConstraintFromNameMaybe (Just name) = addConstraintFromName name
addConstraintFromNameMaybe (Nothing)   = addConstraintNoMessage


-- | Iterates over all constraints which are currently in a "changed" state, and tries to solve them.
--   Returns if no "changed" constraints remains.
--   An unchanged constraint is marked "changed", if it is affected by a new substitution.
--   A changed constraint is marked "unchanged" if it is read by a call to `getUnsolvedConstraintMarkNormal`.
solveAllConstraints :: forall isT t eC e. (MonadDMError e t, MonadImpossible t, MonadLog t, MonadConstraint isT t, MonadNormalize t, IsT isT t) => NormalizationType -> [SolvingMode] -> t ()
solveAllConstraints nt modes = withLogLocation "Constr" $ do

  -- get events which came before us
  oldEvents <- clearSolvingEvents
  case oldEvents of
    [] -> pure ()
    xs -> do
      log $ "[Solver]: Before solving all constraints, the following events have accumulated unnoticed:"
      log $ intercalateS "\n" (fmap ("           - " <>) xs)
      log ""


  -- normalize state
  normalizeState nt

  -- get the first constraint to solve
  openConstr <- getUnsolvedConstraintMarkNormal modes

  case openConstr of
    Nothing -> return ()
    Just (name, constr, mode, constr_desc) -> do
      -- debug $ "[Solver]: Notice: BEFORE solving (" <> show mode <> ") " <> show name <> " : " <> show constr
      -- logPrintConstraints
      -- logPrintSubstitutions

      catchAndPersist (solve mode name constr) $ \msg -> do
        markFailedConstraint name
        let msg' = "The constraint" :<>: name :<>: ":" :<>: constr :\\:
                  "could not be solved:"
                  :-----:
                  constr_desc
                  :-----:
                  msg
        return ((),msg')

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
          log $ "[Solver]: solving (" <> showT mode <> ") " <> showT name <> " : " <> showPretty constr
          log $ intercalateS "\n" (fmap ("             - " <>) xs)
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


solveAndNormalize :: forall a isT t eC e. (MonadDMError e t, MonadImpossible t, MonadLog t, MonadConstraint isT t, MonadNormalize t, IsT isT t, Normalize t a, ShowPretty a) => NormalizationType -> [SolvingMode] -> a -> t a
solveAndNormalize nt modes value = f 4 value
  where
    f :: Int -> a -> t a
    f n a0 | n <= 0 = impossible "Solving & normalizing needed more than 4 iterations. Cancelling."
    f n a0          = do

      -- remove duplicate constraints
      nubConstraints

      -- get all constraint names
      allCs0 <- getAllConstraints
      let allNames0 = fst <$> allCs0

      solveAllConstraints nt modes
      debug $ "================================================"
      debug $ "Solved constraints as far as possible."
      debug $ "Now normalizing type."
      a1 <- normalize nt a0
      debug $ "Old type: " <> showPretty a0
      debug $ "New type: " <> showPretty a1

      allCs1 <- getAllConstraints
      let allNames1 = fst <$> allCs1

      case allNames0 == allNames1 of
        True  -> return a1
        False -> f (n-1) a1




