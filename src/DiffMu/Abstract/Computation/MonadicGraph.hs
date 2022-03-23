
module DiffMu.Abstract.Computation.MonadicGraph where

import DiffMu.Prelude
import DiffMu.Abstract.Computation.INC
import DiffMu.Abstract.Class.Constraint
import DiffMu.Abstract.Class.IsT
import DiffMu.Abstract.Class.Log
import DiffMu.Abstract.Class.Unify
import DiffMu.Abstract.Data.Error

import Debug.Trace


-- Since our nodes/edges live in a monad, the source/target of an edge need not necessarily be *really* equal, for the edge to having to be considered as reflexive.
-- Thus we add this as annotation.
data EdgeType = IsReflexive Structurality | NotReflexive

type Structurality = (MatchForcing, MatchForcing)
data MatchForcing = IsMatchForcing | NotMatchForcing

pattern IsStructural = (IsMatchForcing,IsMatchForcing)
pattern IsLeftStructural = (IsMatchForcing,NotMatchForcing)
pattern IsRightStructural = (NotMatchForcing,IsMatchForcing)
pattern NotStructural = (NotMatchForcing,NotMatchForcing)

-- A reflexive edge is structural if matching on one side already is enough to know that
-- we got the correct edge.
-- For example, the (a₀ -> b₀ ⊑ a₁ -> b₁) rule/edge is structural, because an arrow is
-- only subtype of an arrow.
-- On the other hand, the rule (Const s₀ a₀ ⊑ Const s₁ a₁) is not structural, because
-- in the case of checking (Const s₀ a₀ ⊑ b) even though we matched on the left hand side,
-- it is still possible that the rule (Const s₀ a₀ ⊑ NonConst a₀) is the one which actually
-- should be used.
-- data Structurality = IsStructural | NotStructural

newtype EdgeFamily m a b = EdgeFamily (a -> m (INCRes () b), b -> m (a,a))

data Edge m a where
  SingleEdge :: m (a,a) -> Edge m a
  MultiEdge :: Eq b => (a -> INCRes () b) -> (b -> m (a,a)) -> Edge m a

newtype GraphM m a = GraphM (EdgeType -> [Edge m a])

data ErrorRelevance = IsGraphRelevant | NotGraphRelevant
  deriving (Show)

data IsShortestPossiblePath = IsShortestPossiblePath | NotShortestPossiblePath

instance Show IsShortestPossiblePath where
  show IsShortestPossiblePath = "shortest possible"
  show NotShortestPossiblePath = "not shortest possible"

type PathState a = ((a,a),IsShortestPossiblePath)

oppositeGraph :: forall m a. Monad m => GraphM m a -> GraphM m a
oppositeGraph (GraphM graph) = GraphM (opp graph)
  where oppositeEdge :: Edge m a -> Edge m a
        oppositeEdge (SingleEdge x) = SingleEdge ((\(a,b) -> (b,a)) <$> x)
        oppositeEdge (MultiEdge pre fam) = MultiEdge pre ((\x -> (\(a,b) -> (b,a)) <$> x) . fam)

        opp :: (EdgeType -> [Edge m a]) -> (EdgeType -> [Edge m a])
        opp f (NotReflexive) = oppositeEdge <$> f NotReflexive
        opp f (IsReflexive (sl,sr)) = oppositeEdge <$> f (IsReflexive (sr,sl))

-- findPathM :: forall s m e a. (Show e, Show a, MonadError e m, MonadState s m, MonoidM m a, CheckNeutral m a) => (e -> ErrorRelevance) -> GraphM m a -> (a,a) -> m (INCRes (e m) (a,a))
findPathM :: forall s m isT e a msg. (MessageLike m msg, Show (e m), Show a, Eq a, MonadConstraint isT m, IsT isT m, Normalize m a, MonadNormalize m, MonadDMError e m, MonadState s m, MonadImpossible m, MonadLog m, Unify e m a, CheckNeutral m a) => (e m -> ErrorRelevance) -> GraphM m a -> (a,a) -> msg -> m (INCRes (e m) (PathState a))
findPathM relevance (GraphM g) (start,goal) msg | start == goal = return $ Finished ((start,goal),IsShortestPossiblePath)
findPathM relevance (GraphM g) (start,goal) msg | otherwise     =
  let -- both (Finished a) (Finished b) | a == b = Finished a
      -- both (Fail e) _                         = Fail e
      -- both _ (Fail e)                         = Fail e
      -- both _ _                                = Wait

      -- atLeastOne (Finished a) Wait = Finished a
      -- atLeastOne Wait (Finished b) = Finished b
      -- atLeastOne (Finished a) (Finished b) | a == b = Finished a
      -- atLeastOne (Fail e) _                         = Fail e
      -- atLeastOne _ (Fail e)                         = Fail e
      -- atLeastOne _ _                                = Wait

      tryFastMatch x (Finished a) (Finished b) | a == b = Finished a
      tryFastMatch (IsMatchForcing,_) (Finished a) Wait = Finished a
      tryFastMatch (_,IsMatchForcing) Wait (Finished b) = Finished b
      tryFastMatch x (Fail e) _                         = Fail e
      tryFastMatch x _ (Fail e)                         = Fail e
      tryFastMatch _ _ _                                = Wait

      checkSingle getIdx a x =
        do ia <- getIdx a
           case ia of
             Finished c -> x c
             Fail _ -> return (Fail MultiEdgeIndexFailed)
             Wait -> return Wait
             Partial _ -> return Wait

      -- we check the neutrality of a and b
      -- And wait either - only if both are not neutral
      --          or     - if at least one is not neutral
      -- checkPair op getIdx a b x = do
      --   ia <- getIdx a
      --   ib <- getIdx b
      --   case (op ia ib) of
      --     Finished c -> x c
      --     Fail _ -> return (Fail MultiEdgeIndexFailed)
      --     Wait -> return Wait
      --     Partial _ -> return Wait

      checkPair op getIdx a b x = withLogLocation "MndGraph" $ do
        ia <- getIdx a
        ib <- getIdx b
        case (op ia ib) of
          Finished c -> do
            debug $ "Checkpair[path] on " <> show (a,b) <> " successfull. => Continuing path computation."
            x c
          Fail _ -> do
            debug $ "Checkpair[path] on " <> show (a,b) <> " failed. => We are failing as well."
            return (Fail MultiEdgeIndexFailed)
          Wait -> do
            debug $ "Checkpair[path] on " <> show (a,b) <> " returned Wait."
            return Wait
          Partial _ -> do
            debug $ "Checkpair[path] on " <> show (a,b) <> " returned a Partial. => We wait"
            return Wait


      checkByStructurality s getIdx a b x = checkPair (tryFastMatch s) getIdx a b x
      -- checkByStructurality NotStructural getIdx a b x = checkPair both       getIdx a b x


      f_refl :: Eq b => Structurality -> EdgeFamily m a b -> PathState a -> m (INCRes (e m) (PathState a))
      f_refl s (EdgeFamily (getIdx,edge)) ((start,goal),isShortest) =
        checkByStructurality s getIdx start goal $ \idx -> do
          debug $ "[pathfinding from refl] trying to find path" <> show (start, goal)
          (n₀, n₁) <- edge idx
          n₀'' <- unify msg start n₀
          n₁'' <- unify msg n₁ goal
          debug $ "[pathfinding from refl] got path " <> show ((n₀'', n₁''),isShortest)
          return (Finished ((n₀'', n₁''),isShortest))

      fromLeft :: Eq b => EdgeFamily m a b -> PathState a -> m (INCRes (e m) (PathState a))
      fromLeft (EdgeFamily (getIdx,edge)) ((start,goal),_) =
        checkByStructurality NotStructural getIdx start goal $ \idx -> do
          debug $ "[pathfinding from Left] trying to find path" <> show (start, goal)
          (n₀,n₁) <- edge idx
          n₀'' <- unify msg start n₀
          debug $ "[pathfinding from Left] got partial path. Next we want: " <> show ((n₁, goal),NotShortestPossiblePath)
          return (Partial ((n₁, goal),NotShortestPossiblePath))

      fromRight :: Eq b => EdgeFamily m a b -> PathState a -> m (INCRes (e m) (PathState a))
      fromRight (EdgeFamily (getIdx,edge)) ((start,goal),_) =
        checkByStructurality NotStructural getIdx start goal $ \idx -> do
          debug $ "[pathfinding from Right] trying to find path" <> show (start, goal)
          (n₀,n₁) <- edge idx
          n₁'' <- unify msg n₁ goal
          debug $ "[pathfinding from Right] got partial path. Next we want: " <> show ((start, n₀),NotShortestPossiblePath)
          return (Partial ((start, n₀),NotShortestPossiblePath))

      catchRelevant :: forall a b. (a -> m (INCRes (e m) a)) -> (a -> m (INCRes (e m) a))
      catchRelevant f a =
        catchError (f a) $ \e -> do
          -- log $ "caught error: " <> show e
          -- log $ "  => relevance: " <> show (relevance e)
          case relevance e of
            IsGraphRelevant -> return (Fail (UserError e))
            NotGraphRelevant -> throwOriginalError e


      checkNeutrality a = do
        na <- checkNeutral a
        case na of
          True -> return Wait
          False -> return $ Finished ()

      checkNeutrality' getIdx a = do
        na <- checkNeutral a
        case na of
          True -> return Wait
          False -> return (getIdx a)

      withFamily :: forall x. (forall b. Eq b => EdgeFamily m a b -> x) -> Edge m a -> x
      withFamily f (SingleEdge edge)       = f (EdgeFamily (checkNeutrality, \() -> edge))
      withFamily f (MultiEdge getIdx edge) = f (EdgeFamily (checkNeutrality' getIdx, edge))


      reflComp s = [catchRelevant (withFamily (f_refl s) a)  | a <- g (IsReflexive s)]

      computations = join [reflComp (s,t) | s <- [IsMatchForcing,NotMatchForcing], t <- [IsMatchForcing,NotMatchForcing]]
                  <> [catchRelevant (withFamily fromLeft a)   | a <- g NotReflexive]
                  <> [catchRelevant (withFamily fromRight a)  | a <- g NotReflexive]

  in withLogLocation "MndGraph" $ evalINC (INC computations) ((start,goal),IsShortestPossiblePath)

type SupState a = ((a,a) :=: a, IsShortestPossiblePath)

findSupremumM :: forall s m isT e a msg. (MessageLike m msg, Show (e m), Show a, Eq a, MonadDMError e m, MonadConstraint isT m, IsT isT m, Unify e m (a), Normalize m a, MonadNormalize m, MonadState s m, MonadImpossible m, MonadLog m, CheckNeutral m a) => (e m -> ErrorRelevance) -> GraphM m a -> SupState a -> msg -> m (INCRes (e m) ((a,a) :=: a))
findSupremumM relevance (GraphM graph) ((a,b) :=: x,isShortestSup) msg =
  let
    -------------
    -- This is copy paste from above

      tryFastMatch x (Finished a) (Finished b) | a == b = Finished a
      tryFastMatch (IsMatchForcing,_) (Finished a) Wait = Finished a
      tryFastMatch (_,IsMatchForcing) Wait (Finished b) = Finished b
      tryFastMatch x (Fail e) _                         = Fail e
      tryFastMatch x _ (Fail e)                         = Fail e
      tryFastMatch _ _ _                                = Wait


      both (Finished a) (Finished b) | a == b = Finished a
      both (Fail e) _                         = Fail e
      both _ (Fail e)                         = Fail e
      both _ _                                = Wait

      -- atLeastOne (Finished a) Wait = Finished a
      -- atLeastOne Wait (Finished b) = Finished b
      -- atLeastOne (Finished a) (Finished b) | a == b = Finished a
      -- atLeastOne (Fail e) _                         = Fail e
      -- atLeastOne _ (Fail e)                         = Fail e
      -- atLeastOne _ _                                = Wait

      checkPair op getIdx a b x = withLogLocation "MndGraph" $ do
        ia <- getIdx a
        ib <- getIdx b
        case (op ia ib) of
          Finished c -> do
            debug $ "Checkpair[supremum] on " <> show (a,b) <> " successfull. => Continuing supremum computation."
            x c
          Fail _ -> do
            debug $ "Checkpair[supremum] on " <> show (a,b) <> " failed. => We are failing as well."
            return (Fail MultiEdgeIndexFailed)
          Wait -> do
            debug $ "Checkpair[supremum] on " <> show (a,b) <> " returned Wait."
            return Wait
          Partial _ -> do
            debug $ "Checkpair[supremum] on " <> show (a,b) <> " returned a Partial. => We wait"
            return Wait


      -- checkByStructurality IsStructural  getIdx a b x = checkPair atLeastOne getIdx a b x
      -- checkByStructurality NotStructural getIdx a b x = checkPair both       getIdx a b x

      catchRelevant :: forall a b. (a -> m (INCRes (e m) a)) -> (a -> m (INCRes (e m) a))
      catchRelevant f a =
        catchError (f a) $ \e -> do
          -- log $ "caught error: " <> show e
          -- log $ "  => relevance: " <> show (relevance e)
          case relevance e of
            IsGraphRelevant -> return (Fail (UserError e))
            NotGraphRelevant -> throwOriginalError e
      checkNeutrality a = do
        na <- checkNeutral a
        case na of
          True -> return Wait
          False -> return $ Finished ()

      checkNeutrality' getIdx a = do
        na <- checkNeutral a
        case na of
          True -> return Wait
          False -> return (getIdx a)

      withFamily :: forall x. (forall b. Eq b => EdgeFamily m a b -> x) -> Edge m a -> x
      withFamily f (SingleEdge edge)       = f (EdgeFamily (checkNeutrality, \() -> edge))
      withFamily f (MultiEdge getIdx edge) = f (EdgeFamily (checkNeutrality' getIdx, edge))

   -- end copy paste
   -------------

      fromLeft :: Eq b => EdgeType -> EdgeFamily m a b -> ((a,a) :=: a) -> m (INCRes (e m) ((a,a) :=: a))
      fromLeft edgeType (EdgeFamily (getIdx,edge)) ((start₀,start₁) :=: goal) =
        checkPair both getIdx start₀ start₁ $ \idx -> do
          openNewConstraintSet
          ((n₀, n₁)) <- edge idx
          n₀'' <- unify msg start₀ n₀
          (rpath) <- findPathM relevance (GraphM graph) (start₁,n₁) msg
          debug $ "fromLeft: trying to solve sup" <> show (start₀,start₁) <> " = " <> show goal
          debug $ "for that, find path: " <> show (start₁,n₁) <> "\nGot: " <> show rpath
          case rpath of
            Wait -> return Wait
            Fail e -> case edgeType of
                        -- If have a reflexive edge, and failed, then we do not continue
                        IsReflexive _  -> return $ Fail e
                        -- If we mereley had a non-reflexive edge, we try again with the target of that edge
                        NotReflexive -> traceShow ("=> [Left] Finding path " <> show (start₁,n₁) <> " failed. Now computing sup " <> show (n₁, start₁, goal)) (findSupremumM relevance (GraphM graph) (((n₁, start₁) :=: goal),NotShortestPossiblePath) msg)
            Partial x -> logForce ("Waiting because got partial:\n" <> show x) >> return Wait
            Finished ((a₀,a₁),isShortestPath) -> do
              debug "Since finding path successfull, solving leftover constraints."
              debug "============ BEFORE solving all new constraints >>>>>>>>>>>>>>>>"
              solveAllConstraints ExactNormalization [SolveExact]
              debug "============ AFTER solving all new constraints >>>>>>>>>>>>>>>>"
              logPrintConstraints
              closedRes <- mergeTopConstraintSet
              case closedRes of
                ConstraintSet_WasNotEmpty ->
                  case (edgeType,isShortestSup,isShortestPath) of
                    (IsReflexive (IsMatchForcing, _), IsShortestPossiblePath, IsShortestPossiblePath) -> do
                      debug "Constraint set was not empty. But the paths leading to it were only reflexive edges. Thus we commit this sup result."
                      goal' <- unify msg goal a₁
                      debug $ " we have:\nsup(" <> show (n₀'', a₀) <> " = " <> show goal'
                      return $ Finished ((n₀'' , a₀) :=: goal')
                    _ -> do
                      logForce "Waiting because constraint set not empty! (And paths not shortest.)" >> return Wait
                ConstraintSet_WasEmpty -> do
                  debug "Constraint set was empty! Thus we found the supremum."
                  debug $ "After unification with the goal" <> show goal <> " =! " <> show a₁
                  goal' <- unify msg goal a₁
                  debug $ " we have:\nsup(" <> show (n₀'', a₀) <> " = " <> show goal'
                  return $ Finished ((n₀'' , a₀) :=: goal')

      fromRight :: Eq b => EdgeType -> EdgeFamily m a b -> ((a,a) :=: a) -> m (INCRes (e m) ((a,a) :=: a))
      fromRight edgeType (EdgeFamily (getIdx,edge)) ((start₀,start₁) :=: goal) =
        checkPair both getIdx start₀ start₁ $ \idx -> do
          openNewConstraintSet
          (n₀, n₁) <- edge idx
          n₀'' <- unify msg start₁ n₀
          (rpath) <- findPathM relevance (GraphM graph) ((start₀,n₁)) msg
          debug $ "fromRight: trying to solve sup" <> show (start₀,start₁) <> " = " <> show goal
          debug $ "for that, find path: " <> show (start₀,n₁) <> "\nGot: " <> show rpath
          case rpath of
            Wait -> return Wait
            Fail e -> case edgeType of
                        -- If have a reflexive edge, and failed, then we do not continue
                        IsReflexive _  -> return $ Fail e
                        -- If we mereley had a non-reflexive edge, we try again with the target of that edge
                        NotReflexive -> do
                          log ("=> [Right] Finding path " <> show (start₀,n₁) <> " failed. Now computing sup " <> show (start₀, n₁, goal))
                          (findSupremumM relevance (GraphM graph) (((start₀, n₁) :=: goal),NotShortestPossiblePath) msg)
            Partial x -> return Wait
            Finished ((a₀,a₁),isShortestPath) -> do
              debug "Since finding path successfull, solving leftover constraints."
              debug "============ BEFORE solving all new constraints >>>>>>>>>>>>>>>>"
              solveAllConstraints ExactNormalization [SolveExact]
              debug "============ AFTER solving all new constraints >>>>>>>>>>>>>>>>"
              logPrintConstraints
              closedRes <- mergeTopConstraintSet
              case closedRes of
                ConstraintSet_WasNotEmpty ->
                  case (edgeType,isShortestSup,isShortestPath) of
                    (IsReflexive (IsMatchForcing, _), IsShortestPossiblePath, IsShortestPossiblePath) -> do
                      debug "Constraint set was not empty. But the paths leading to it were only reflexive edges. Thus we commit this sup result."
                      goal' <- unify msg goal a₁
                      debug $ " we have:\nsup(" <> show (a₀ , n₀'') <> " = " <> show goal'
                      return $ Finished ((a₀ , n₀'') :=: goal')
                    _ -> do
                      logForce "Waiting because constraint set not empty! (And paths not shortest.)" >> return Wait
                ConstraintSet_WasEmpty -> do
                  debug "Constraint set was empty! Thus we found the supremum."
                  debug $ "After unification with the goal" <> show goal <> " =! " <> show a₁
                  goal' <- unify msg goal a₁
                  debug $ " we have:\nsup(" <> show (a₀ , n₀'') <> " = " <> show goal'
                  return $ Finished ((a₀ , n₀'') :=: goal')

      reflCompLeft s  = [catchRelevant (withFamily (fromLeft (IsReflexive s)) a)   | a <- graph (IsReflexive s)]
      reflCompRight s = [catchRelevant (withFamily (fromRight (IsReflexive s)) a)  | a <- graph (IsReflexive s)]

      reflComputations =    join [reflCompLeft (s,t) | s <- [IsMatchForcing,NotMatchForcing], t <- [IsMatchForcing,NotMatchForcing]]
                     <> join [reflCompRight (s,t) | s <- [IsMatchForcing,NotMatchForcing], t <- [IsMatchForcing,NotMatchForcing]]
      stepComputations = [catchRelevant (withFamily (fromLeft (NotReflexive)) a)  | a <- graph (NotReflexive)]
                     <> [catchRelevant (withFamily (fromRight NotReflexive) a)  | a <- graph (NotReflexive)]


  in withLogLocation "MndGraph" $ do
    -- step zero: backup our state, for if the quick path check gives a partial,
    -- we have to rewind!
    state0 <- get

    -- first, we check if there are even paths a -> x and b -> x
    pathLeft  <- findPathM relevance (GraphM graph) (a,x) msg
    pathRight <- findPathM relevance (GraphM graph) (b,x) msg

    case (pathLeft,pathRight) of
      -- if one of the paths fails, then the supremum cannot exist,
      -- thus we can fail as well
      (Fail e, _) -> return $ Fail e
      (_, Fail e) -> return $ Fail e

      -- if both found paths are shortest possible,
      -- then we actually now that the supremum is already found
      (Finished ((a' , x0) , IsShortestPossiblePath), Finished ((b' , x1) , IsShortestPossiblePath)) -> do
        x <- unify msg x0 x1
        return (Finished ((a' , b') :=: x))

      -- but if we have to wait, or the paths were found, but not shortest, we
      -- simply do the actual supremum computation
      _  -> do
        -- since our args may have been updated, first normalize them
        wantedSup <- normalizeExact ((a,b) :=: x)
        reflResult <- evalINC (INC reflComputations) wantedSup
        case reflResult of
          Wait      -> put state0 >> return Wait -- In these two cases we rewind to before the quick path check,
          Partial a -> put state0 >> return Wait -- because we do not want constraints/substitutions from that to affect our state
          Finished a -> return (Finished a)
          -- only if all reflexive edges fail, then we can look at the non-reflexive ones
          Fail e -> evalINC (INC stepComputations) ((a,b) :=: x)

findInfimumM :: forall s m isT e a msg. (MessageLike m msg, Show (e m), Show a, Eq a, MonadDMError e m, MonadConstraint isT m, IsT isT m, Unify e m (a), Normalize m a, MonadNormalize m, MonadState s m, MonadImpossible m, MonadLog m, CheckNeutral m a) => (e m -> ErrorRelevance) -> GraphM m a -> ((a,a) :=: a) -> msg -> m (INCRes (e m) ((a,a) :=: a))
findInfimumM relevance graph z = findSupremumM relevance (oppositeGraph graph) (z,IsShortestPossiblePath)
