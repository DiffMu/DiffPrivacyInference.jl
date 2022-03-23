
module DiffMu.Typecheck.Constraint.IsFunctionArgument where

import DiffMu.Prelude
import DiffMu.Abstract
import DiffMu.Core.Logging
import DiffMu.Core.Definitions
import DiffMu.Core.Context
import DiffMu.Core.TC
import DiffMu.Core.Symbolic
import DiffMu.Core.Unification
import DiffMu.Typecheck.JuliaType
import Algebra.PartialOrd
import DiffMu.Typecheck.Constraint.CheapConstraints
import DiffMu.Typecheck.Constraint.IsJuliaEqual

import Debug.Trace

import qualified Data.HashSet as HS
import qualified Data.HashMap.Strict as H
import Data.HashMap.Strict (HashMap)
import qualified Data.POSet as PO
import Data.POSet (POSet)

import Debug.Trace
import qualified Data.HashMap.Strict as H


---------------------------------------------------------------------
-- "Strict subtyping" of function calls
--
-- For each given argument of a function call, we create an IsFunctionArgument constraint on the type the
-- called function expects that argument to have. in case of arguments that are themselves functions,
-- we need to do choice resolution later, making sure all the choices that the callee expects its argument
-- to have are actually present with the given argument. we create such a constraint upon checking
-- function application, with the callee being the expected type and the given being a function type from
-- the arguments the callee is applied to to a type variable that will be determined upon resultion of the
-- constraint.

newtype IsFunctionArgument a = IsFunctionArgument a deriving Show

instance TCConstraint IsFunctionArgument where
  constr = IsFunctionArgument
  runConstr (IsFunctionArgument c) = c

-- first is expected argument type, second is given argument type
solveIsFunctionArgument :: IsT MonadDMTC t => Symbol -> (DMTypeOf MainKind, DMTypeOf MainKind) -> t ()

-- if the expected argument and given argument are both functions / collections of functions, we add an
-- IsChoice constraint 
solveIsFunctionArgument name (Fun xs, Fun ys) = do
    
  -- the choices the given argument function has
  let wantedFunctions :: [DMTypeOf FunKind]
      wantedFunctions = [f | (f :@ _) <- ys]
  -- the choices the callee function expects the argument function to have
  let existingFunctions :: [([JuliaType], (DMTypeOf FunKind, [DMTypeOf FunKind]))]
      existingFunctions = [(jts , (f, [])) | (f :@ Just jts) <- xs]

  case [f | (f :@ Nothing) <- xs] of
    [] -> do
      -- replace the IFA constraint by an IsChoice constraint   
      addConstraintFromName name (Solvable (IsChoice ((H.fromListWith (\_ _ -> error "Duplicate Method!") existingFunctions), wantedFunctions)))
      dischargeConstraint name
      return ()

    -- if there were functions without annotation, error out
    xs -> internalError $ "Encountered functions without a required julia type annotation as the argument to a function:\n" <> show xs

-- the callee does not expect any specific type, so we can just unify.
solveIsFunctionArgument name (TVar a, Fun xs) = addSub (a := Fun xs) >> dischargeConstraint name >> pure ()

-- if we expect a non-function, the given argument must be a non-function.
solveIsFunctionArgument name (NoFun a1, b) = do
  unifyFromName name (NoFun a1) b
  dischargeConstraint name

-- if the given argument is a non-function, we must expect some non-function type.
solveIsFunctionArgument name (b, NoFun a1) = do
  unifyFromName name b (NoFun a1)
  dischargeConstraint name

-- if both sides are variables or ∧ terms of variables
-- then we cannot do anything yet, since we do not know whether we have function terms inside, or not.
solveIsFunctionArgument name (_, _) = return ()


------------------------------------------------------------------------------------------------------
-- IsChoice constraints
--
-- these are created from IsFunctionArgument constraints for function calls where the argument is
-- itself a function. that means all methods required by the callee (bc the argument function is called
-- with certain arguments inside) must be present in the argument function.

-- map Julia signature to method and the list of function calls that went to this method.
type ChoiceHash = HashMap [JuliaType] (DMTypeOf FunKind, [DMTypeOf FunKind])

-- hash has the existing methods, list has the required methods.
instance Solve MonadDMTC IsChoice (ChoiceHash, [DMTypeOf FunKind]) where
  solve_ Dict _ name (IsChoice arg) = solveIsChoice name arg

-- see if the constraint can be resolved. might update the IsCHoice constraint, do nothing, or discharge.
-- might produce new IsFunctionArgument constraints for the arguments.
solveIsChoice :: forall t. IsT MonadDMTC t => Symbol -> (ChoiceHash, [DMTypeOf FunKind]) -> t ()
solveIsChoice name (provided, required) = do
   -- remove all choices from the "required" list that have a unique match in the "provided" hashmap.
   -- when a choice is resolved, the corresponding counter in the hashmap is incremented by one.
   let matchArgs ::  ChoiceHash -> [DMTypeOf FunKind] -> t (ChoiceHash, [DMTypeOf FunKind])
       matchArgs curProv curReq = do
          case curReq of
             [] -> return (curProv, [])
             (τs : restReq) -> do -- go through all required methods
                 debug $ "[IFA]: called on " <> show τs
                 case τs of
                      TVar _ -> do -- it was a tvar
                              (resP, resR) <- (matchArgs curProv restReq) -- can't resolve TVar choice, keep it and recurse.
                              return (resP, (τs : resR))
                      _ -> do
                         -- get methods that could be a match, and free TVars in the args while we're at it
                         (candidates, hasFreeVars) <- getMatchCandidates τs curProv

                         -- if there is no free tyepevars in τs arguments, throw out methods that are more general than others
                         -- if we don't know all types we cannot do this, as eg for two methods
                         -- (Int, Int) => T
                         -- (Real, Number) => T
                         -- and arg types (TVar, DMInt), both methods are in newchoices, but if we later realize the TVar
                         -- is a DMReal, the first one does not match even though it's less general.
                         -- filter Fun arguments, as the all have the same type "Function" in julia/
                         let candidates' = case hasFreeVars of
                               -- if no tvars are in the args
                               True  -> keepLeastGeneral candidates
                               -- else we do not change them
                               False -> candidates

                         debug $ "[IFA]: candidates before: " <> show candidates
                         debug $ "[IFA]: candidates after:  " <> show candidates'

                         case and ((length candidates' == length curProv),(length candidates' > 1)) of
                            -- no choices were discarded, the constraint could not be simplified.
                            True -> do
                                       (resP, resR) <- (matchArgs curProv restReq) -- can't resolve choice, keep it and recurse.
                                       return (resP, (τs : resR))

                            -- some choices were discarded, so we can continue
                            False -> do
                               case H.toList candidates' of
                                   -- only one left, we can pick that one yay
                                   -- even if there is free TVars, we don't have to add subtype constraints for the user-given signature,
                                   -- as it was encoded in the Arr type of the choice, so its arg types can only be refinements.
                                  [(sign, (cτ, matches))] -> do
                                     -- append the match to the list of calls that matched this method.
                                     let resP = H.insert sign (cτ, (τs : matches)) curProv -- append match to match list
                                     res <- matchArgs resP restReq -- discard entry by recursing without τs
                                     return res

                                  _ -> do -- more than one left, need to wait.
                                     (resP, resR) <- (matchArgs curProv restReq) -- can't resolve choice, keep it and recurse.
                                     return (resP, (τs : resR))

   (newdict, newcs) <- matchArgs provided required -- get new dict and list of yet unresolved choices.

   -- discard or update constraint.
   case newcs of
        [] -> do -- complete resolution! set counters, discard.
                debug $ "[IFA]: Done, newdict is:"
                debug $ show newdict
                mapM (resolveChoiceHash name) (H.toList newdict)
                dischargeConstraint name
        cs | (length required > length newcs) -> do
                -- still not all choices resolved, just kick the resolved ones out of the constraint.
                -- the kicked out ones are already included in their method's list in newdict.
                updateConstraint name (Solvable (IsChoice (newdict, newcs)))
        _ -> do
                return ()

   return ()


resolveChoiceHash :: forall t. IsT MonadDMTC t => Symbol -> ([JuliaType], (DMTypeOf FunKind, [DMTypeOf FunKind])) -> t ()
resolveChoiceHash name (sign, (method, [])) = pure () -- no matches were found for this method.
resolveChoiceHash name (sign, (method, matches)) = do
   let resolveAnn :: (DMTypeOf FunKind) -> t (DMMain, [DMMain])
       resolveAnn match = case (match, method) of
                                 (matchxs :->: τmatch, methxs :->: τmeth) -> do
                                    mapM (\(x, y) -> (unifyFromName name) (sndAnn x) (sndAnn y)) (zip matchxs methxs) -- unify sensitivities
                                    return (τmatch, [t | (t :@ _) <- matchxs])
                                 (matchxs :->*: τmatch, methxs :->*: τmeth) -> do
                                    mapM (\((_:@x), (_:@y)) -> (unifyFromName name) x y) (zip matchxs methxs) -- unify privacies
                                    return (τmatch, [t | (t :@ _) <- matchxs])
                                 -- this is the case where checkPriv was called on the application of a -> arrow.
                                 (matchxs :->*: τmatch, methxs :->: τmeth) -> do
                                     msg <- inheritanceMessageFromName name
                                     throwError (WithContext (NoChoiceFoundError $ "Found application of a sensitivity function "
                                                                  <> show method <> " where a private value was expected") (DMPersistentMessage msg))
                                 (matchxs :->: τmatch, methxs :->*: τmeth) -> do
                                     msg <- inheritanceMessageFromName name
                                     throwError (WithContext (NoChoiceFoundError $ "Found application of a privacy function "
                                                                  <> show method <> " where a senstivity value was expected") (DMPersistentMessage msg))
                                 _ -> impossible $ "reached impossible case in resolving choices: " <> show (match, method)

   methsigs <- mapM resolveAnn matches -- set sensitivities of all matches and get their dmtype signatures
   let argtypes = transpose (map snd methsigs) -- get per-argument list instead of per-match list
   let (methxs, methr) = case method of
           (xs :->: r) ->  ([t | (t :@ _) <- xs], r)
           (xs :->*: r) -> ([t | (t :@ _) <- xs], r)
   -- given the list of all types that the matches tried to input into an argument of the method,
   -- creates the necessary constraints to make sure they fit and also fit the julia type annotation.
   -- we use the supremum of all input types, so we can input terms of const types with different values
   -- without getting contradicting constraints as long as the number types match
   let addC :: forall t. IsT MonadDMTC t => ([DMMain], DMMain, JuliaType) -> t ()
       addC ([], _, _) = pure ()
       addC ((a:as), m, ann) = do
           s <- foldM (supremumFromName name) a as -- get supremum of all things the current argument was applied to

           addConstraintFromName name (Solvable (IsFunctionArgument (s, m))) -- make sure it fits the type requred by the method
           msg <- inheritanceMessageFromName name
           addJuliaSubtypeConstraint s ann msg -- make sure it fits the given julia signature

   mapM addC (zip3 argtypes methxs sign) -- do it for the arguments

   --
   -- NOTE: In the following, we would like to to make an `infimum` on the output types
   --       of the choices, because we do supremum on the input types and do the dual kind of makes sense.
   --       But then it breaks cases where we need to know the const output type of a function.
   --       Instead we do unification here, this should behave like infimum in most cases anyways,
   --       it is only slightly stronger (inf{Const,NonConst} is possible, while unification is not).
   --
   let (r:rs) = map fst methsigs -- do the same for the return type
   s <- foldM (unifyFromName name) r rs
   addConstraintFromName name (Solvable (IsFunctionArgument (methr, s)))

   return ()

-- remove dict entries whose signature is supertype of some other signature.
-- this is only reasonable if the dmtype signature we're trying to match has no free variables,
-- bc then the minimal matching method is picked.
keepLeastGeneral :: ChoiceHash -> ChoiceHash
keepLeastGeneral cs =
  -- make a poset from the (julia-)subtype relations of the given signatures
  -- convert to JuliaSignature so we use our custom `leq`
  let pos :: POSet JuliaSignature
      pos = foldr PO.insert PO.empty (map JuliaSignature (HS.toList (H.keysSet cs))) 
      -- pick the ones that are not supertypes of any of the others
      mins = PO.lookupMin pos

      mins' = [(k, cs H.! k) | JuliaSignature k <- mins]
  in
      H.fromListWith (\_ _ -> error "Duplicate Method!") mins'


-- kick out all methods in provided that would not match τsτ.
getMatchCandidates :: forall t. IsT MonadDMTC t => DMTypeOf FunKind -> ChoiceHash -> t (ChoiceHash, Bool)
getMatchCandidates τsτ provided = do
   (candidates, hasFreeVars) <- case τsτ of
      (args :->: _)  -> do
                        -- remove all methods that definitely don't match this signature
                        let cand = (H.filterWithKey (\s c -> choiceCouldMatch (fstAnn <$> args) s) provided)
                        -- filter all argument types that would be "Function" in julia...
                        let argsNoJFun = [(τa, ann) | (τa :@ ann) <- args, noJuliaFunction τa]
                        -- ... and get the free typevars of the rest.
                        let free = and (null . freeVars @_ @TVarOf <$> argsNoJFun)
                        debug $ "[IFA]: `getMatchCandidates` on " <> show τsτ
                        debug $ "[IFA]: (via " <> show argsNoJFun <> ")"
                        debug $ "[IFA]: => free vars is: " <> show free
                        return (cand, free)
      (args :->*: _) -> do -- same as for the above case.
                        let cand = (H.filterWithKey (\s c -> choiceCouldMatch (fstAnn <$> args) s) provided)
                        let argsNoJFun = [(τa, ann) | (τa :@ ann) <- args, noJuliaFunction τa]
                        let free = and (null . freeVars @_ @TVarOf <$> argsNoJFun)
                        debug $ "[IFA]: `getMatchCandidates` on " <> show τsτ
                        debug $ "[IFA]: (via " <> show argsNoJFun <> ")"
                        debug $ "[IFA]: => free vars is: " <> show free
                        return (cand, free)
      _ -> throwUnlocatedError (ImpossibleError ("Invalid type for Choice: " <> show τsτ))

   if H.null candidates
      then throwUnlocatedError (NoChoiceFoundError $ "No matching choice for " <> show τsτ <> " found in " <> show provided)
      else return (candidates, hasFreeVars)


-- determine whether a function with the given dmtype signature could match a method with the given juliatype signature.
choiceCouldMatch :: [DMTypeOf MainKind] -> [JuliaType] -> Bool
choiceCouldMatch args cs =
   case length args == length cs of
        False -> False
        True -> -- get all julia types that the arg dmtype could be (this can be several, e.g. for Numeric TVar)
                -- check if any of them is a (julia) subtype of the required julia type form the annotation
                -- if so, the arguments could (but dont have to) match the choice
                let couldMatch t c = or ((`leq` c) <$> juliatypes t) -- check if the arg possibly is a julia subtype of c
                in (and (zipWith couldMatch args cs)) -- check if all args are julia subtypes of their cs


-- return False if this type would become a "Function" if converted to a julia type
noJuliaFunction :: DMTypeOf MainKind -> Bool
noJuliaFunction τ = (juliatypes τ /= [JTFunction])




------------------------------------------------------------------------------------------------------
--compute fixed vars of the constraints

-- get the typevar which appears on the right hand side of the topmost arrow.
getFunctionReturnVar :: DMTypeOf k -> [SomeK TVarOf]
getFunctionReturnVar (Fun fs) = mconcat (getFunctionReturnVar . fstAnn <$> fs)
getFunctionReturnVar (as :->: (TVar a)) = [SomeK a]
getFunctionReturnVar (as :->*: (TVar a)) = [SomeK a]
getFunctionReturnVar _ = mempty

getNoFunVars :: DMMain -> [SomeK TVarOf]
getNoFunVars (NoFun a) = freeVars a
getNoFunVars _ = mempty

instance FixedVars TVarOf (IsFunctionArgument (DMTypeOf MainKind, DMTypeOf MainKind)) where
  -- TODO: Is this calculation of fixed vars correct?
  fixedVars (IsFunctionArgument (existingFuns, wantedFuns)) = getFunctionReturnVar wantedFuns <> getNoFunVars existingFuns <> getNoFunVars wantedFuns

instance Solve MonadDMTC IsFunctionArgument (DMTypeOf MainKind, DMTypeOf MainKind) where
  solve_ Dict _ name (IsFunctionArgument (a,b)) = solveIsFunctionArgument name (a,b)


instance FixedVars TVarOf (IsChoice (ChoiceHash, [DMTypeOf FunKind])) where
  -- TODO: Is this calculation of fixed vars correct?
  fixedVars (IsChoice (_, wantedFuns)) = mconcat (getFunctionReturnVar <$> wantedFuns)
