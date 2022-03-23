
module DiffMu.Abstract.Computation.INC where

import DiffMu.Prelude
import DiffMu.Abstract.Class.Log

import Debug.Trace

-- data INCStep = Continue | Finish
data INCError e =
  UserError e
  | MultiEdgeIndexFailed
  | AllBranchesFailed [INCError e]
  deriving Show

-- INC Result
data INCRes e a = Finished a | Partial a | Wait | Fail (INCError e)
  deriving Show

-- incremental, nondeterministic computation
newtype INC m e a = INC [(a -> m (INCRes e a))]

evalINC :: forall s m e a. (MonadLog m, MonadState s m, Show a, Show e) => INC m e a -> a -> m (INCRes e a)
evalINC (steps) start = withLogLocation "INC" $ do
  info $ "Beginning incremental computation on:\n  " <> show start
  let logsteps (INC steps) = debug $ "I have " <> show (length steps) <> " candidates."
  logsteps steps

  state₀ <- get
  let f :: INC m e a -> [(s, INCRes e a)] -> m [(s, INCRes e a)]
      f (INC []) acc = pure acc
      f (INC (x : xs)) acc = do
        put state₀
        res <- x start
        state₁ <- get
        f (INC xs) (acc <> [(state₁, res)])
  results <- f steps []

  debug "Got the following results after first application:"
  debug $ show (snd <$> results)

  let finished = [(s,a) | (s, Finished a) <- results]
  let partial  = [(s,a) | (s, Partial a) <- results]
  let errors   = [e     | (_, Fail e) <- results]


  case finished of

    -- 1. If one computation finished, take that, commit state, and return.
    ((s,a):_) -> put s >> return (Finished a)

    [] ->
      -- 2. If all computations failed, collect their errors, and fail.
      if length errors == length results
        then put state₀ >> return (Fail (AllBranchesFailed errors))

        else case partial of
               -- 3. If no partial results could be achieved, then return a `wait`
               [] -> put state₀ >> return Wait

               -- 4. In case there is only one partial result, and the rest were errors, we can commit its state, and simply continue our computation with that.
               -- NOTE: This branch is probably only very rarely taken.
               [(s,a)] | (length errors == length results - 1) -> do
                 put s
                 res <- evalINC steps a
                 case res of
                   Finished a -> return (Finished a)
                   Partial a  -> return (Partial a)
                   Wait       -> return (Partial a) -- If the recursive computation did not give us new results, we still take our current one.
                   Fail e     -> return (Fail e)

               -- 5. If there were multiple partial results, or, some of them were `Wait`s, we do a recursive search with each one.
               _ -> do
                 let g (s,a) = do
                       put s
                       res <- evalINC steps a
                       s₁ <- get
                       return (s₁, res)
                 results <- mapM g partial

                 -- We do a similar case distinction here, but we now only care about finished and failed
                 let finished = [(s,a) | (s, Finished a) <- results]
                 let errors    = [e     | (_, Fail e) <- results]

                 case finished of

                   -- 5.1. If one computation finished, take that, commit state, and return.
                   ((s,a):_) -> put s >> return (Finished a)

                   [] -> if length errors == length results

                       -- 5.2. If all computations failed, collect their errors, and fail.
                       then put state₀ >> return (Fail (AllBranchesFailed errors))

                       -- 5.3. Else, this means that we only have some partial results, and some fails. We cannot conclude anything from that, so we wait.
                       else put state₀ >> return Wait





