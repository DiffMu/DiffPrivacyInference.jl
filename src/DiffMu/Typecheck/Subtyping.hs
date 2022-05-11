
{- |
Description: Definition of the subtyping system.

This involves code for solving questions of subtyping, as well as infimum/supremum.
For generic graph search the computation is done using `DiffMu.Abstract.Computation.MonadicGraph`.
But there are also further mechanisms for resolving such constraints:
 - Diamond contraction
 - Cycle contraction
 - Top/Bottom evaluation
-}
module DiffMu.Typecheck.Subtyping where

import DiffMu.Prelude
import DiffMu.Abstract
import DiffMu.Core.Definitions
import DiffMu.Core.Context
import DiffMu.Core.Logging
import DiffMu.Core.TC
import DiffMu.Core.Symbolic
import DiffMu.Core.Unification
import DiffMu.Typecheck.Constraint.Definitions


import qualified Data.HashMap.Strict as H

import Debug.Trace

import qualified Prelude as P


default (Text)

---------------------------------------------------------------------
-- "Non strict subtyping"

-- helper functions used below in defining the subtyping graph.
getFun :: DMMain -> INCRes () [DMTypeOf FunKind :@ Maybe [JuliaType]]
getFun (Fun xs) = Finished xs
getFun (TVar _) = Wait
getFun _ = Fail (UserError ())

getTupSize :: DMTypeOf NoFunKind -> INCRes () Int
getTupSize (DMTup xs) = Finished (length xs)
getTupSize (TVar a) = Wait
getTupSize _ = Fail (UserError ())

-- The subtyping graph for our type system.
subtypingGraph :: forall e t k. (SingI k, Typeable k, MonadDMTC t) => IxSymbol -> EdgeType -> [Edge t (DMTypeOf k)]
subtypingGraph name =
  let 
      -- An abbreviation for adding a subtyping constraint.
      (⊑!) :: forall k. (SingI k, Typeable k, MonadDMTC t) => DMTypeOf k -> DMTypeOf k -> t ()
      (⊑!) a b = addConstraintFromName name (Solvable (IsLessEqual (a,b))) >> pure ()

      case0 = testEquality (typeRep @k) (typeRep @MainKind)
      case1 = testEquality (typeRep @k) (typeRep @FunKind)
      case2 = testEquality (typeRep @k) (typeRep @NoFunKind)
      case3 = testEquality (typeRep @k) (typeRep @NumKind)
      case4 = testEquality (typeRep @k) (typeRep @BaseNumKind)
      case5 = testEquality (typeRep @k) (typeRep @IRNumKind)
      case6 = testEquality (typeRep @k) (typeRep @ClipKind)
      case7 = testEquality (typeRep @k) (typeRep @NormKind)
      case8 = testEquality (typeRep @k) (typeRep @ConstnessKind)
  in case (case0,case1,case2,case3,case4,case5,case6,case7,case8) of
    -- Main Kind
    (Just Refl, _, _, _, _, _, _, _, _) ->
      \case { IsReflexive NotStructural
              -> []
            ; IsReflexive IsStructural
              -> [ SingleEdge $ do
                     a0 <- newVar
                     a1 <- newVar
                     a0 ⊑! a1
                     return (NoFun a0, NoFun a1),

                   -- we do not have subtyping for arrows
                   MultiEdge getFun $ \a -> do
                     return (Fun a, Fun a)
                 ]
            ; _
              -> []
            }
    -- Fun Kind
    (_,Just Refl, _, _, _, _, _, _, _) ->
      \case { IsReflexive IsStructural -> []
            ; _ -> []}
    -- NoFunKind
    (_,_, Just Refl, _, _, _, _, _, _) ->
      \case { IsReflexive IsStructural
            -> [
                 (SingleEdge $
                   do a₀ <- newVar
                      a₁ <- newVar
                      a₀ ⊑! a₁
                      return (Numeric a₀, Numeric a₁))
                 , (MultiEdge getTupSize $ \n ->
                   do
                     let f () = do a <- newVar
                                   b <- newVar
                                   a ⊑! b
                                   return (a, b)

                     args <- mapM f (take n $ repeat ())
                     let (args₀, args₁) = unzip args
                     return (DMTup args₀, DMTup args₁)
                     )
                 , SingleEdge $
                   do clp₀ <- newVar
                      nrm₀ <- newVar
                      nrm₁ <- newVar
                      clp₁ <- newVar
                      n <- newVar
                      m <- newVar
                      a₀ <- newVar
                      a₁ <- newVar
                      a₀ ⊑! a₁
                      nrm₀ ⊑! nrm₁
                      clp₀ ⊑! clp₁
                      return ((DMMat nrm₀ clp₀ n m a₀), (DMMat nrm₁ clp₁ n m a₁))
                 , SingleEdge $
                   do clp₀ <- newVar
                      nrm₀ <- newVar
                      nrm₁ <- newVar
                      clp₁ <- newVar
                      n <- newVar
                      a₀ <- newVar
                      a₁ <- newVar
                      a₀ ⊑! a₁
                      nrm₀ ⊑! nrm₁
                      clp₀ ⊑! clp₁
                      return ((DMVec nrm₀ clp₀ n a₀), (DMVec nrm₁ clp₁ n a₁))
                 , SingleEdge $
                   do m <- newVar
                      return ((DMModel m), (DMModel m))
                 , SingleEdge $
                   do nrm₀ <- newVar
                      clp₀ <- newVar
                      nrm₁ <- newVar
                      clp₁ <- newVar
                      m <- newVar
                      a₀ <- newVar
                      a₁ <- newVar
                      a₀ ⊑! a₁
                      nrm₀ ⊑! nrm₁
                      clp₀ ⊑! clp₁
                      return ((DMGrads nrm₀ clp₀ m a₀), (DMGrads nrm₁ clp₁ m a₁))
                 , SingleEdge $ return (DMBool, DMBool)
                 ]
            ; IsReflexive NotStructural -> []
            ; _ -> []
            }

    -- Num Kind
    (_,_, _, Just Refl, _, _, _, _, _) ->
      \case { IsReflexive IsStructural
              -> [
                    -- SingleEdge $ return ((Num DMData NonConst), (Num DMData NonConst))
                    SingleEdge $ do
                      a₀ <- newVar
                      a₁ <- newVar
                      a₀ ⊑! a₁
                      c₀ <- newVar
                      c₁ <- newVar
                      c₀ ⊑! c₁
                      return (Num a₀ c₀, Num a₁ c₁)
                 ]
            ; IsReflexive IsLeftStructural -> []
            ; IsReflexive IsRightStructural -> []
            ; NotReflexive -> []
            ; _ -> []
            }

    -- BaseNum Kind
    (_,_, _, _, Just Refl, _, _, _, _) ->
      \case { IsReflexive IsStructural
              -> [ SingleEdge $ return (DMData, DMData)
                 , SingleEdge $ do
                     a <- newVar
                     b <- newVar
                     a ⊑! b
                     return (IRNum a, IRNum b)
                 ]
            ; _ -> []
            }

    -- IRNum Kind
    (_,_, _, _, _, Just Refl, _, _, _) ->
      \case { IsReflexive IsRightStructural
              -> [
                   SingleEdge $ return (DMInt, DMInt)
                 ]
            ; IsReflexive IsLeftStructural
              -> [
                   SingleEdge $ return (DMReal, DMReal)
                 ]
            ; NotReflexive
              -> [ SingleEdge $ return (DMInt, DMReal)
                 ]
            ; _ -> []
            }
    -- kind = clip
    (_, _, _, _, _, _, Just Refl, _, _) ->
      \case { IsReflexive IsStructural
              -> [ SingleEdge $ return (U, U)
                 , SingleEdge $ do
                     a <- newVar
                     b <- newVar
                     a ⊑! b
                     return (Clip a, Clip b)
                 ]
            ; _ -> []
            }

    -- kind = norm
    (_, _, _, _, _, _, _, Just Refl, _) ->
      \case { IsReflexive IsStructural
              -> [ SingleEdge $ return (L1, L1)
                 , SingleEdge $ return (L2, L2)
                 , SingleEdge $ return (LInf, LInf)
                 ]
            ; _ -> []
            }
            
    -- constness kind
    (_, _, _, _, _, _, _, _, Just Refl) ->
      \case { IsReflexive IsStructural
              -> [ ]
            ; IsReflexive IsLeftStructural
              -> [
                   SingleEdge $
                   do 
                      return (NonConst, NonConst)
                 ]
            ; IsReflexive IsRightStructural
               -> [SingleEdge $
                   do s₀ <- newVar
                      return (Const s₀, Const s₀)
               ]
            ; NotReflexive
              -> [ SingleEdge $
                   do s₀ <- newVar
                      return (Const s₀, NonConst)
                 ]
            ; _ -> []
            }

    (_, _, _, _, _, _, _, _, _) -> \_ -> []



convertSubtypingToSupremum :: forall k t. (SingI k, Typeable k, IsT MonadDMTC t) => IxSymbol -> (DMTypeOf k, DMTypeOf k) -> t ()
convertSubtypingToSupremum = convertSubtypingToSupInf (\(a,b,c) msg -> addConstraint (Solvable (IsSupremum ((a,b) :=: c))) msg) (\(a,b) -> (a,b))

convertSubtypingToInfimum :: forall k t. (SingI k, Typeable k, IsT MonadDMTC t) => IxSymbol -> (DMTypeOf k, DMTypeOf k) -> t ()
convertSubtypingToInfimum = convertSubtypingToSupInf (\(a,b,c) msg -> addConstraint (Solvable (IsInfimum ((a,b) :=: c))) msg) (\(a,b) -> (b,a))

type MaybeInversionFunc k = (DMTypeOf k, DMTypeOf k) -> (DMTypeOf k, DMTypeOf k)
type SupInfCreationFunc t k = forall msg. MessageLike t msg => (DMTypeOf k, DMTypeOf k, DMTypeOf k) -> msg -> t IxSymbol

-- If we have a bunch of subtyping constraints {β ≤ α, γ ≤ α, δ ≤ α} then it
-- are allowed to turn this into a supremum constraint, i.e. "sup{β,γ,δ} = α"
-- in the case that α does not appear in any other constraints except as lower bound of
-- subtyping constraints. 
convertSubtypingToSupInf :: forall k t. (SingI k, Typeable k, IsT MonadDMTC t) => SupInfCreationFunc t k -> MaybeInversionFunc k -> IxSymbol -> (DMTypeOf k, DMTypeOf k) -> t ()
convertSubtypingToSupInf createConstr invert name (l,u) = do
  case invert (l,u) of
    (lower, TVar upper) -> do
    -- case testEquality (typeRep @k) (typeRep @ConstnessKind) of
    --   Just Refl -> pure ()
    --   _ -> do
        logForce $ "[SubToSupInf]: Trying conversion for " <> showT (invert (lower, TVar upper))

        -- all (subtyping) constraints that contain upper
        allCsWithUpper <- filterWithSomeVars [(SomeK upper)] <$> getAllConstraints
        allSubWithUpper <- filterWithSomeVars [(SomeK upper)] <$> fmap (second runConstr) <$> getConstraintsByType (Proxy @(IsLessEqual (DMTypeOf k, DMTypeOf k)))

        case ((length allSubWithUpper) == (length allCsWithUpper)) of
          False -> (logForce "[SubToSupInf]: => other constraints are in the way!") >> return () -- upper is involved in other constraints that are not LessEqual constraints, so this simplification is not allowed
          True -> do
              allSubtypings <- getConstraintsByType (Proxy @(IsLessEqual (DMTypeOf k, DMTypeOf k)))
              let invSubtypings = second (\(IsLessEqual a) -> IsLessEqual (invert a)) <$> allSubtypings
              -- TODO: We are actually not allowed to do this always, but only if there is nothing which could be broken...
              -- all subtyping constraints δ ≤ upper for some δ
              let (names, lowers) = unzip [(name', lower') | (name', IsLessEqual (lower', TVar upper')) <- invSubtypings,
                                          name' /= name,
                                          upper' == upper]

              messages <- mapM getConstraintMessage names

              -- for the list [β, γ, δ] create supremum constraints sup{β,γ} = u and sup{u,δ} = upper for a new TVar u
              -- as we only have two-argument sup constraints. also discharge the involved subtyping constraints.
              let makeChain lowers = case lowers of
                      [] -> return ()
                      (l:[]) -> do
                                  dischargeConstraint name
                                  mapM dischargeConstraint names
                                  -- addConstraint (Solvable (IsSupremum ((lower, l) :=: TVar upper)))
                                  createConstr (lower, l, TVar upper)
                                    ("Supremum recreated for the following constraints:" :\\:
                                    messages
                                    )
                                  logForce "Something very suspicious is happening, at least make sure that this is really the correct approach."
                                  logForce ("What happens is that we convert the subtyping constraint of " <> showT (lower, TVar upper) <> " into the supremum " <> showT ((lower, l) :=: TVar upper))
                                  logForce "Whyever that is supposed to be correct..."
                                  return ()
                      (l1:l2:ls) -> do
                                  u <- newVar
                                  -- addConstraint (Solvable (IsSupremum ((l1, l2) :=: u)))
                                  createConstr (l1, l2, u)
                                    ("Supremum recreated for the following constraints:" :\\:
                                    messages
                                    )
                                  makeChain (u:ls)
                                  return ()

              makeChain lowers
              return ()
    _ -> pure ()

-- The actual solving is done here.
-- this simply uses the `findPathM` function from Abstract.Computation.MonadicGraph
-- We return True if we could do something about the constraint
--    return False if nothing could be done
solveSubtyping :: forall t k. (SingI k, Typeable k, IsT MonadDMTC t) => IxSymbol -> (DMTypeOf k, DMTypeOf k) -> t ()
solveSubtyping name (_, DMAny) = dischargeConstraint name
solveSubtyping name path@(a,b) = withLogLocation "Subtyping" $ do

  -- Here we define which errors should be caught while doing our hypothetical computation.
  let relevance (UnificationError _ _)      = IsGraphRelevant
      relevance (UnsatisfiableConstraint _) = IsGraphRelevant
      relevance _                           = NotGraphRelevant

  -- traceM $ "Starting subtyping solving of " <> show path
  let graph = subtypingGraph @t
  -- traceM $ "I have " <> show (length (graph (IsReflexive NotStructural))) <> " candidates."

  -- Executing the computation
  msg <- inheritanceMessageFromName name
  enterNonPersisting 
  (res) <- findPathM @(Full (DMPersistentMessage t)) (\(WithContext e _ ) -> relevance e) (GraphM (graph name)) path msg
  exitNonPersisting 

  -- We look at the result and if necessary throw errors.
  case res of
    Finished a     -> do
      log $ "Subtyping computation of " <> showT path <> " finished with result " <> showT res <> ". Discharging constraint " <> showT name
      dischargeConstraint @MonadDMTC name
    Partial (a,_)  -> do
      log $ "Subtyping computation of " <> showT path <> " gave partial result " <> showT res <> ". Updating constraint " <> showT name
      updateConstraint name (Solvable (IsLessEqual a))
    Wait           -> do
      log $ "Subtyping computation of " <> showT path <> " returned `Wait`. Keeping constraint as is."
      npath <- normalizeExact path
      log $ "(With normalizations applied the constraint is now " <> showT npath <> " ; it should be the same as the input.)"
      -- convertSubtypingToSupremum name path -- in this case we try to change this one into a sup
    Fail e         -> do

      let msg2 = case getUnificationFailingHint @t (path) of
                   Just hint -> DMPersistentMessage (hint :\\: msg)
                   Nothing -> DMPersistentMessage msg
      throwError (WithContext (UnsatisfiableConstraint (show (fst path) <> " ⊑ " <> show (snd path))) (msg2))


data ContractionAllowed = ContractionAllowed | ContractionDisallowed


getBottoms :: forall k. (SingI k, Typeable k) => [DMTypeOf k]
getBottoms =
  case testEquality (typeRep @k) (typeRep @IRNumKind) of
     Just Refl -> [DMInt]
     _ -> []

getTops :: forall k. (SingI k, Typeable k) => [DMTypeOf k]
getTops =
  case testEquality (typeRep @k) (typeRep @IRNumKind) of
     Just Refl -> [DMReal]
     _ -> case testEquality (typeRep @k) (typeRep @ConstnessKind) of
            Just Refl -> [NonConst]
            _ -> []

type TypeGraph k = H.HashMap (DMTypeOf k) [DMTypeOf k]

getCurrentConstraintSubtypingGraph :: forall t k. (SingI k, Typeable k, IsT MonadDMTC t) => t (TypeGraph k)
getCurrentConstraintSubtypingGraph = do

  ctrs_relevant <- fmap (second runConstr) <$> getConstraintsByType (Proxy @(IsLessEqual (DMTypeOf k, DMTypeOf k)))
  ctrs_relevant_max <- fmap (second runConstr) <$> getConstraintsByType (Proxy @(IsSupremum ((DMTypeOf k, DMTypeOf k) :=: DMTypeOf k)))
  ctrs_relevant_min <- fmap (second runConstr) <$> getConstraintsByType (Proxy @(IsInfimum ((DMTypeOf k, DMTypeOf k) :=: DMTypeOf k)))

  let subFromSub (_,(a,b)) = [(a,b)]
  let subFromMax (_,((a,b) :=: c)) = [(a,c),(b,c)]
  let subFromMin (_,((a,b) :=: c)) = [(c,a),(c,b)]

  let edges = (ctrs_relevant >>= subFromSub)
              <> (ctrs_relevant_max >>= subFromMax)
              <> (ctrs_relevant_min >>= subFromMin)

  -- we build a graph of subtype relations, represented by adjacency lists stored in a hash map
  -- nodes are types that appear in <=, Inf or Sup constraints, edges are suptype relations
  -- for every node we also add edges from the bottom types (if existent for kind k) an to the top types.
  let addEdge :: H.HashMap (DMTypeOf k) [DMTypeOf k] -> (DMTypeOf k, DMTypeOf k) -> H.HashMap (DMTypeOf k) [DMTypeOf k]
      addEdge graph (s, e) = let
            tops = getTops @k
            -- add edges [s -> t for t in tops] and edge s -> e.
            graph'  = case H.lookup s graph of
                               Nothing -> H.insert s (e:tops) graph
                               Just sc -> H.insert s (e:sc) graph -- tops were added already in this case

            -- also add edges [e -> t for t in tops].
            graph'' = case H.lookup e graph' of
                               Nothing | not (null tops) -> H.insert e tops graph'
                               _ -> graph' -- if e has outgoing edges already, they were added above and tops are in.
         in graph''


  let graph = foldl addEdge H.empty edges
  let graph' = foldl addEdge graph [(b, e) | b <- getBottoms @k, e <- (H.keys graph)] -- add edges from bottoms to all other nodes.
  return graph'



-- all paths in the graph of length <= N connecting a0 and a1
allPathsN :: Int -> TypeGraph k -> (DMTypeOf k, DMTypeOf k) -> Maybe [[DMTypeOf k]]
allPathsN _ _ (a0,a1) | a0 == a1  = Just [[a0,a1]]
allPathsN 0 _ (a0,a1) = Nothing
allPathsN n graph (a0,a1) =
  let succ = case H.lookup a0 graph of -- successors of a0
                      Nothing -> []
                      Just s -> s
      smallerPaths = [allPathsN (n - 1) graph (b,a1) | b <- succ] -- all maybe-paths of length N-1 from successors to a1
      goodPaths = concat [p | Just p <- smallerPaths] -- the ones that actually exist
  in case goodPaths of
    [] -> Nothing
    ps -> Just [(a0:p) | p <- ps]


-- all paths in the graph connecting a0 and a1.
allPaths :: TypeGraph k -> (DMTypeOf k, DMTypeOf k) -> Maybe [[DMTypeOf k]]
allPaths graph (a0,a1) = allPathsN ((H.size graph) - 1) graph (a0,a1)


traceNot a x = x

-- given two vertices in the subtype relation graph, find all vertices that have an incoming
-- edge from both of them.
completeDiamondDownstream :: (SingI k, Typeable k) => TypeGraph k -> (DMTypeOf k, DMTypeOf k) -> [(DMTypeOf k, [DMTypeOf k])]
completeDiamondDownstream graph (a0,a1) =
  let graph'      = traceNot ("graph: " <> show graph) graph
      -- all one-edge long paths from any graph vertex from both a0 and a1, or Nothing if none exist
      doublePaths = [(allPathsN 1 graph (a0, x), allPathsN 1 graph (a1, x), x) | x <- (H.keys graph)]
      doublePaths' = traceNot ("doublePaths: " <> show doublePaths) doublePaths
      -- all x that actually have an edge.
      goodPaths   = [(x,concat (el1 <> el2)) | (Just el1, Just el2, x) <- doublePaths']
      goodPaths' = traceNot ("goodPaths: " <> show goodPaths) goodPaths
  in goodPaths'

-- given two vertices in the subtype relation graph, find all vertices that have an outgoing
-- edge from both of them.
completeDiamondUpstream :: (SingI k, Typeable k) => TypeGraph k -> (DMTypeOf k, DMTypeOf k) -> [(DMTypeOf k, [DMTypeOf k])]
completeDiamondUpstream graph (a0,a1) =
  let graph'      = traceNot ("graph: " <> show graph) graph
      -- all one-edge long paths from any graph vertex to both a0 and a1, or Nothing if none exist
      doublePaths = [(allPathsN 1 graph (x, a0), allPathsN 1 graph (x, a1), x) | x <- (H.keys graph)]
      doublePaths' = traceNot ("doublePaths: " <> show doublePaths) doublePaths
      -- all x that actually have an edge.
      goodPaths   = [(x,concat (el1 <> el2)) | (Just el1, Just el2, x) <- doublePaths']
      goodPaths' = traceNot ("goodPaths: " <> show goodPaths) goodPaths
  in goodPaths'


--
-- This function checks if it is allowed to contract the
-- diamond given by tvars in `contrTypes`, where `a` and `b`
-- are the input and output edges, respectively.
--
-- There are certain conditions which need to hold for variables in
-- `contrTypes`, such that contraction is allowed
--
-- The variable `center` is the one which is the center of the contraction,
-- for this one, no conditions apply. It needs to be `elem` contrTypes,
-- and may even only work if `a == center` or `b == center`.
checkContractionAllowed :: forall t k. (SingI k, Typeable k, IsT MonadDMTC t) => [(DMTypeOf k)] -> (DMTypeOf k, DMTypeOf k) -> DMTypeOf k -> t ContractionAllowed
checkContractionAllowed contrTypes (TVar a, TVar b) (center) = do
  debug $ "[CheckContractionAllowd]: Called for (" <> showT a <> " ==> " <> showT b <> "), center: " <> showT center <> ", contrTypes: " <> showT contrTypes
  let acceptOnlyVar (TVar a) = Just a
      acceptOnlyVar _        = Nothing

      -- We check that all types which we want to contract are type variables
      -- if this returns `Just [xs]` then all types were actually vars
      -- We do exclude the center from this check.
      contrVars' = mapM acceptOnlyVar (contrTypes \\ [center])

  -- The actual case distinction
  case contrVars' of
    Nothing -> do
      debug "  ^^^^ Contraction not allowed because the candidate list contains types which are not TVars."
      return ContractionDisallowed
    (Just contrVars') -> do
      let contrVars = (SomeK <$> contrVars')

      ctrs_all_ab <- filterWithSomeVars contrVars <$> getAllConstraints
      ctrs_relevant <- filterWithSomeVars contrVars <$> fmap (second runConstr) <$> getConstraintsByType (Proxy @(IsLessEqual (DMTypeOf k, DMTypeOf k)))
      ctrs_relevant_max <- filterWithSomeVars contrVars <$> fmap (second runConstr) <$> getConstraintsByType (Proxy @(IsSupremum ((DMTypeOf k, DMTypeOf k) :=: DMTypeOf k)))
      ctrs_relevant_min <- filterWithSomeVars contrVars <$> fmap (second runConstr) <$> getConstraintsByType (Proxy @(IsInfimum ((DMTypeOf k, DMTypeOf k) :=: DMTypeOf k)))

      -- First we check that the only constraints containing contrVars are
      -- {subtyping,sup,inf} constraints
      let m = length ctrs_all_ab
          n = length ctrs_relevant P.+ length ctrs_relevant_max P.+ length ctrs_relevant_min
      case m == n of
        False -> do
          debug "  ^^^^ Contraction not allowed because constraints which are not subtyping/inf/sup constraints exist for the contrVars (=contrTypes\\{center})"
          return ContractionDisallowed
        True -> do
          -- Get all subtyping pairs
          let subFromSub (_,(a,b)) = [(a,b)]
          let subFromMax (_,((a,b) :=: c)) = [(a,c),(b,c)]
          let subFromMin (_,((a,b) :=: c)) = [(c,a),(c,b)]

          let subs = (ctrs_relevant >>= subFromSub)
                    <> (ctrs_relevant_max >>= subFromMax)
                    <> (ctrs_relevant_min >>= subFromMin)

          debug $ "  ^^^^ subtyping pairs are: " <> showT subs

          --
          -- NOTE: In the following, we only deal with edges here which are relevant,
          --       i.e. contain some of the contraction-variables
          --
          -- Next we check that all subtyping edges are good
          -- i.e., an edge is good if one of the following cases appears:
          let isGood (x,y) =
                or
                  [ -- the edge attaches to the center
                    or [x == center , y == center]

                    -- the edge is fully part of the diamond to be contracted
                  , and [x `elem` (contrTypes), y `elem` (contrTypes)]

                    -- the edge attaches to the input of the diamond, and in it's own input
                    -- does not reference any contraction-variables
                  , and [y == TVar a, freeVars x `intersect` contrVars == []]

                    -- the edge attaches to the output of the diamond, and in it's own output
                    -- does not reference any contraction-variables
                  , and [x == TVar b, freeVars y `intersect` contrVars == []]
                  ]

          let edgesWithGoodness = [(a,b,isGood (a,b)) | (a,b) <- subs]
          case find (\(a,b,good) -> not good) edgesWithGoodness of
            Just (a,b,_) -> do
              debug $ "  ^^^^ Contraction not allowed because the edge " <> showT (a,b) <> " is not good."
              return ContractionDisallowed
            Nothing -> do
              debug $ "  ^^^^ Contraction allowed because all edges are good."
              return ContractionAllowed

checkContractionAllowed _ _ _ = return ContractionDisallowed


-- We can solve `IsLessEqual` constraints for DMTypes.
-- NOTE: IsLessEqual is interpreted as a subtyping relation.
instance (SingI k, Typeable k) => Solve MonadDMTC IsLessEqual (DMTypeOf k, DMTypeOf k) where
  solve_ Dict SolveRecreateSupremum name (IsLessEqual (a,b)) = convertSubtypingToSupremum name (a,b) >> convertSubtypingToInfimum name (a,b)
  solve_ Dict SolveSpecial name (IsLessEqual (a,b)) = return ()
  solve_ Dict SolveExact name (IsLessEqual (a,b)) = solveSubtyping name (a,b)
  solve_ Dict SolveGlobal name (IsLessEqual path) = collapseSubtypingCycles path
  solve_ Dict SolveAssumeWorst name (IsLessEqual (a,b)) = return ()
  solve_ Dict SolveFinal name (IsLessEqual (a,b))  | a `elem` getBottoms = dischargeConstraint name
  solve_ Dict SolveFinal name (IsLessEqual (a,b))  | b `elem` getTops    = dischargeConstraint name
  solve_ Dict SolveFinal name (IsLessEqual (a,b))  | otherwise = do
    -- if we are in solve final, we try to contract the edge
        debug $ "Computing LessEqual: " <> showT (a,b)
        alloweda <- checkContractionAllowed [a,b] (a,b) a
        allowedb <- checkContractionAllowed [a,b] (a,b) b
        case (alloweda , allowedb) of
          (ContractionAllowed, _) -> unify "diamond contraction" a b >> return ()
          (_, ContractionAllowed) -> unify "diamond contraction" a b >> return ()
          _ -> return ()

(≤!) :: (SingI k, Typeable k, MessageLike t msg, IsT MonadDMTC t) => DMTypeOf k -> DMTypeOf k -> msg -> t ()
(≤!) a b msg = addConstraint (Solvable (IsLessEqual (a,b))) msg >> pure ()


instance (SingI k, Typeable k) => ShowPretty (IsLessEqual (DMTypeOf k, DMTypeOf k)) where
    showPretty (IsLessEqual (a,b)) = showPretty a <> " ⊑ " <> showPretty b
        



--------------------------------------------
-- wrapper for computing supremum
solveSupremum :: forall t k. (SingI k, Typeable k, IsT MonadDMTC t) => GraphM t (DMTypeOf k) -> IxSymbol -> ((DMTypeOf k, DMTypeOf k) :=: DMTypeOf k) -> t ()
solveSupremum graph name ((a,b) :=: x) = callMonadicGraphSupremum graph name ((a,b) :=: x)

--------------------------------------------
-- wrapper for computing infimum
solveInfimum :: forall t k. (SingI k, Typeable k, IsT MonadDMTC t) => GraphM t (DMTypeOf k) -> IxSymbol -> ((DMTypeOf k, DMTypeOf k) :=: DMTypeOf k) -> t ()
solveInfimum graph name ((a,b) :=: x) = callMonadicGraphSupremum (oppositeGraph graph) name ((a,b) :=: x)


----------------------------------------------------------------------------------------
-- solvers for special cases
-------------------
-- supremum
solveSupremumSpecial :: forall t k. (SingI k, Typeable k, IsT MonadDMTC t) => GraphM t (DMTypeOf k) -> IxSymbol -> ((DMTypeOf k, DMTypeOf k) :=: DMTypeOf k) -> t ()
-- if one input is equal to the output we can skip the supremum computation,
-- then we only have to create a subtyping constraint
solveSupremumSpecial graph name ((a,b) :=: x) | a == x = do
  msg <- inheritanceMessageFromName name
  (b ≤! x) msg
  dischargeConstraint name

solveSupremumSpecial graph name ((a,b) :=: x) | b == x = do
  msg <- inheritanceMessageFromName name
  (a ≤! x) msg
  dischargeConstraint name

solveSupremumSpecial graph name ((a,b) :=: x) | elem a (getBottoms @k) = do
  msg <- inheritanceMessageFromName name
  unify msg b x
  dischargeConstraint name

solveSupremumSpecial graph name ((a,b) :=: x) | elem b (getBottoms @k) = do
  msg <- inheritanceMessageFromName name
  unify msg a x
  dischargeConstraint name

solveSupremumSpecial graph name ((a,b) :=: x) | otherwise = return ()

-------------------
-- infimum
solveInfimumSpecial :: forall t k. (SingI k, Typeable k, IsT MonadDMTC t) => GraphM t (DMTypeOf k) -> IxSymbol -> ((DMTypeOf k, DMTypeOf k) :=: DMTypeOf k) -> t ()
solveInfimumSpecial graph name ((a,b) :=: x) | a == x = do
  msg <- inheritanceMessageFromName name
  (x ≤! b) msg
  dischargeConstraint name

solveInfimumSpecial graph name ((a,b) :=: x) | b == x = do
  msg <- inheritanceMessageFromName name
  (x ≤! a) msg
  dischargeConstraint name

solveInfimumSpecial graph name ((a,b) :=: x) | elem a (getTops @k) = do
  msg <- inheritanceMessageFromName name
  unify msg b x
  dischargeConstraint name

solveInfimumSpecial graph name ((a,b) :=: x) | elem b (getTops @k) = do
  msg <- inheritanceMessageFromName name
  unify msg a x
  dischargeConstraint name

solveInfimumSpecial graph name ((a,b) :=: x) | otherwise = return ()



--------------------------------------------
-- The actual solving is done here.
-- we call the `findSupremumM` function from Abstract.Computation.MonadicGraph
callMonadicGraphSupremum :: forall t k. (SingI k, Typeable k, IsT MonadDMTC t) => GraphM t (DMTypeOf k) -> IxSymbol -> ((DMTypeOf k, DMTypeOf k) :=: DMTypeOf k) -> t ()
callMonadicGraphSupremum graph name ((a,b) :=: x) = do

  -- Here we define which errors should be caught while doing our hypothetical computation.
  let relevance (UnificationError _ _)      = IsGraphRelevant
      relevance (UnsatisfiableConstraint _) = IsGraphRelevant
      relevance _                           = NotGraphRelevant

  -- traceM $ "Starting subtyping solving of " <> show path
  -- let graph = subtypingGraph @t
  -- traceM $ "I have " <> show (length (graph (IsReflexive NotStructural))) <> " candidates."

  -- Executing the computation
  msg <- inheritanceMessageFromName name
  enterNonPersisting
  res <- findSupremumM @(Full (DMPersistentMessage t)) (\(WithContext e _) -> relevance e) (graph) ((a,b) :=: x, IsShortestPossiblePath) msg
  exitNonPersisting

  -- We look at the result and if necessary throw errors.
  case res of
    Finished a -> dischargeConstraint @MonadDMTC name
    Partial a  -> updateConstraint name (Solvable (IsSupremum a))
    Wait       -> return ()
    Fail e     -> do
      let msg2 = case getUnificationFailingHint @t ((a,b)) of
                   Just hint -> DMPersistentMessage (hint :\\: msg)
                   Nothing -> DMPersistentMessage msg
      throwError (WithContext (UnsatisfiableConstraint ("sup(" <> show (a) <> ", " <> show b <> ") = " <> show x)) (msg2))
      -- throwUnlocatedError (UnsatisfiableConstraint ("sup(" <> show (a) <> ", " <> show b <> ") = " <> show x <> "\n\n"
      --                    <> "Got the following errors while search the subtyping graph:\n"
      --                    <> show e))


unifyAll :: (Typeable k, IsT MonadDMTC t, MessageLike t msg) => msg -> [DMTypeOf k] -> t ()
unifyAll _ ([]) = return ()
unifyAll _ (x:[]) = return ()
unifyAll msg (x:y:vars) = do
  unify msg x y
  unifyAll msg (y:vars)

-- TODO: Check whether this does the correct thing.
instance (SingI k, Typeable k) => Solve MonadDMTC IsSupremum ((DMTypeOf k, DMTypeOf k) :=: DMTypeOf k) where
  solve_ Dict SolveRecreateSupremum name (IsSupremum ((a,b) :=: y)) = pure ()
  solve_ Dict SolveExact name (IsSupremum ((a,b) :=: y)) = solveSupremum (GraphM (subtypingGraph name)) name ((a,b) :=: y)
  solve_ Dict SolveSpecial name (IsSupremum ((a,b) :=: y)) = solveSupremumSpecial (GraphM (subtypingGraph name)) name ((a,b) :=: y)

  solve_ Dict SolveGlobal name (IsSupremum ((a,b) :=: y)) = do
    collapseSubtypingCycles (a,y)
    collapseSubtypingCycles (b,y)

  solve_ Dict SolveFinal name (IsSupremum ((a,b) :=: y)) = do
    debug $ "Computing supremum (final solving mode): " <> showT ((a,b) :=: y)
    msg <- inheritanceMessageFromName name
    let msg' = "Diamond contraction (from supremum)" :\\: msg

    graph <- getCurrentConstraintSubtypingGraph
    let contrCandidates = completeDiamondUpstream graph (a,b)
    let f (x,contrVars) = do

              debug $ "Trying to contract from " <> showT (x,y) <> " with contrVars: " <> showT contrVars
              allowedy <- checkContractionAllowed (y:contrVars) (x,y) y
              allowedx <- checkContractionAllowed (y:contrVars) (x,y) x
              case (allowedy, allowedx) of
                (ContractionAllowed, _) -> unifyAll msg' (y:contrVars) >> return True
                (_, ContractionAllowed) -> unifyAll msg' (y:contrVars) >> return True
                _ -> return False

    let g f [] = return ()
        g f (x:xs) = do
          res <- f x
          case res of
            True -> return ()
            False -> g f xs

    g f contrCandidates

  solve_ Dict SolveAssumeWorst name (IsSupremum ((a,b) :=: y)) = return ()


-- TODO: Check whether this does the correct thing.
instance (SingI k, Typeable k) => Solve MonadDMTC IsInfimum ((DMTypeOf k, DMTypeOf k) :=: DMTypeOf k) where
  solve_ Dict SolveRecreateSupremum name (IsInfimum ((a,b) :=: y)) = pure ()
  solve_ Dict SolveExact name (IsInfimum ((a,b) :=: x)) = solveInfimum (GraphM (subtypingGraph name)) name ((a,b) :=: x)
  solve_ Dict SolveSpecial name (IsInfimum ((a,b) :=: x)) = solveInfimumSpecial (GraphM (subtypingGraph name)) name ((a,b) :=: x)
  solve_ Dict SolveGlobal name (IsInfimum ((a,b) :=: x)) = do
    collapseSubtypingCycles (x,a)
    collapseSubtypingCycles (x,b)

  solve_ Dict SolveFinal name (IsInfimum ((a,b) :=: x)) = do
    debug $ "Computing infimum (final solving): " <> showT ((a,b) :=: x)

    msg <- inheritanceMessageFromName name
    let msg' = "Diamond contraction (from infimum)" :\\: msg

    graph <- getCurrentConstraintSubtypingGraph

    let contrCandidates = completeDiamondDownstream graph (a,b)
    let f (y,contrVars) = do

              debug $ "Trying to contract from " <> showT (x,y) <> " with contrVars: " <> showT contrVars
              allowedx <- checkContractionAllowed (x:contrVars) (x,y) x
              allowedy <- checkContractionAllowed (x:contrVars) (x,y) y
              case (allowedx , allowedy) of
                (ContractionAllowed, _) -> unifyAll msg' (x:contrVars) >> return True
                (_, ContractionAllowed) -> unifyAll msg' (x:contrVars) >> return True
                _ -> return False

    let g f [] = return ()
        g f (x:xs) = do
          res <- f x
          case res of
            True -> return ()
            False -> g f xs

    g f contrCandidates

    solveInfimum (GraphM (subtypingGraph name)) name ((a,b) :=: x)

  solve_ Dict SolveAssumeWorst name (IsInfimum ((a,b) :=: x)) = return ()

-- find all cyclic subtyping constraints, that is, chains of the form
-- a <= b <= c <= a
-- where for every constraint Sup(a,b) = c we also add additional a <= c and b <= c constraints (likewise for Inf).
-- all types in such a chain can be unified.
collapseSubtypingCycles :: forall k t. (SingI k, Typeable k, IsT MonadDMTC t) => (DMTypeOf k, DMTypeOf k) -> t ()
collapseSubtypingCycles (start, end) = withLogLocation "Subtyping" $ do
  debug $ ("~~~~ collapsing cycles of " <> showT (start,end))
  graph <- getCurrentConstraintSubtypingGraph

  debug $ ("~~~~ graph is " <> showT graph)--(H.insert end (start:[start]) H.empty))

  -- find all paths from the ssucc to the start node, hence cycles that contain the start-end-edge
  let cycles = concat (allPaths graph (end, start))

  debug $ ("~~~~ found cycles " <> showT cycles <> " unifying with " <> showT end <> "\n")

  -- unify all types in all cycles with the end type
  unifyAll "Subtyping cycles collapse" (concat cycles)

  return ()
