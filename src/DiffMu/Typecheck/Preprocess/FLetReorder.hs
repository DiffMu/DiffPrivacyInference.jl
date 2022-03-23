
module DiffMu.Typecheck.Preprocess.FLetReorder where

import DiffMu.Prelude
import DiffMu.Core
import DiffMu.Core.Logging
import DiffMu.Abstract.Data.Error
import DiffMu.Abstract.Class.Log
import DiffMu.Typecheck.Preprocess.Common

import qualified Data.HashMap.Strict as H

import qualified Data.Text as T

import Debug.Trace

default (Text)

type FLetTC = LightTC Location_PrePro_FLetReorder ()

findDuplicates :: Eq a => [a] -> [a]
findDuplicates = findDuplicates' []
  where
    findDuplicates' :: Eq a => [a] -> [a] -> [a]
    findDuplicates' good [] = []
    findDuplicates' good (a:as) = case a `elem` good of
      False -> findDuplicates' (a:good) as
      True  -> a : findDuplicates' (good) as

collectAllFLets :: LocDMTerm -> FLetTC LocDMTerm
collectAllFLets (Located l (FLet var def rest)) = do
  FindFLetsResult defs rest' <- findFLets var rest [l]
  let alldefs = ((l,def):defs)

  -- we derive the julia type from the term, appending the corresponding julia types to their definitions
  allsigs <- mapM (getJuliaSig . getLocated . snd) alldefs

  -- we search for duplicate signatures,
  -- if there are any, we throw an error
  case findDuplicates allsigs of
    [] -> pure ()
    xs -> throwUnlocatedError $ FLetReorderError $ "The function `" <> show var <> "` has more than one definition for the following signatures: " <> show xs <> "\nThis means that the earlier definitions are going to have no effect, and as a precaution this is not allowed."

  -- let alldefsWithJuliaSig = zip allsigs alldefs
      -- we thread the elements through a hashmap => if we have terms with the same juliatype,
      -- the second one overwrites the first one
  --     alldefsWithJuliaSig' = H.elems (H.fromList alldefsWithJuliaSig)
  -- logForce $ "-----------------"
  -- logForce $ "for var " <> show var <> " found the signatures:"
  -- logForce $ show alldefsWithJuliaSig
  -- logForce $ "after removing duplicates, we have: "
  -- logForce $ show alldefsWithJuliaSig'

  updatedAllDefs <- mapM (\(l,x) -> collectAllFLets x >>= \y -> return (l,y)) alldefs
  updatedRest <- collectAllFLets rest'
  return $ expandFLets var updatedAllDefs updatedRest
collectAllFLets (Located l (SLet var def rest)) = Located l <$> (SLet var <$> (collectAllFLets def) <*> (collectAllFLets rest))
collectAllFLets (Located l (TLet var def rest)) = Located l <$> (TLet var <$> (collectAllFLets def) <*> (collectAllFLets rest))
collectAllFLets (Located l (Extra e))  = pure $ Located l $ Extra undefined

collectAllFLets rest = recDMTermMSameExtension_Loc collectAllFLets rest


expandFLets :: TeVar -> [(SourceLocExt, LocDMTerm)] -> LocDMTerm -> LocDMTerm
expandFLets var [] rest = rest
expandFLets var ((l_d,d):defs) rest = Located l_d $ FLet var d (expandFLets var defs rest)

type JuliaSig = [JuliaType]

data FindFLetsResult = FindFLetsResult
  {
    otherDefinitions :: [(SourceLocExt, LocDMTerm)]
  , restOfTerm :: LocDMTerm
  }

requireEmptyResult :: TeVar -> [SourceLocExt] -> FindFLetsResult -> FLetTC FindFLetsResult
requireEmptyResult target l res@(FindFLetsResult [] _) = return res
requireEmptyResult target l res@(FindFLetsResult others _) = throwError $ (WithContext (FLetReorderError $ "Non-sequential implementations for " <> show target)
                                                                           (DMPersistentMessage (l :\\:
                                                                                                 "" :\\:
                                                                                                 "Found multiple implementations for the function" :<>: target :<>: "which are not strictly next to each other" :\\:
                                                                                                 "" :\\:
                                                                                                 "The Julia runtime reorders all implementations of a function in a given scope to be at the location of the first implementation." :\\:
                                                                                                 "To mitigate any confusion about the order of statements, we do not allow implementations to be non-sequential." :\\:
                                                                                                 "" :\\:
                                                                                                 "Please put all definitions of" :<>: target :<>: "next to each other."
                                                                                                )))

findFLets :: TeVar -> LocDMTerm -> [SourceLocExt] -> FLetTC FindFLetsResult
findFLets target (Located l (FLet var def rest)) ls | target == var = do FindFLetsResult others rest' <- findFLets target rest (l:ls)
                                                                         return $ FindFLetsResult ((l,def):others) rest'
findFLets target (Located l (FLet var def rest)) ls | otherwise     = do FindFLetsResult others rest' <- requireEmptyResult target (l:ls) =<< findFLets target rest (ls)
                                                                         return $ FindFLetsResult (others) (Located l (FLet var def rest'))
findFLets target (Located l (SLet var def rest)) ls = do FindFLetsResult others rest' <- requireEmptyResult target (l:ls) =<< findFLets target rest (ls)
                                                         return $ FindFLetsResult (others) (Located l $ SLet var def rest')
findFLets target (Located l (TLet var def rest)) ls = do FindFLetsResult others rest' <- requireEmptyResult target (l:ls) =<< findFLets target rest (ls)
                                                         return $ FindFLetsResult (others) (Located l $ TLet var def rest')
findFLets target (Located l (BBLet var args rest)) ls = do FindFLetsResult others rest' <- requireEmptyResult target (l:ls) =<< findFLets target rest (ls)
                                                           return $ FindFLetsResult (others) (Located l $ BBLet var args rest')
findFLets target t ls = return $ FindFLetsResult [] t


getJuliaSig ::  ISing_DMLogLocation l => DMTerm -> LightTC l s JuliaSig
getJuliaSig (Lam as _ _) = pure $ map sndA as
getJuliaSig (LamStar as _ _) = pure $ map (fst . sndA) as
getJuliaSig _ = impossible "Expected a lam/lamstar inside an flet."

