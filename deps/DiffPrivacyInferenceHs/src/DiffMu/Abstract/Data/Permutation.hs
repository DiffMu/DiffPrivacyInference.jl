
{- |
Description: Helper functions for permuations.
-}
module DiffMu.Abstract.Data.Permutation where

import DiffMu.Prelude
import qualified Prelude as P

-- apply the permutation given by the integer list
permute :: [Int] -> [a] -> [a]
permute (i:is) as = as !! i : permute is as
permute [] as = []


-- for every element in as, we find the position
-- at which it is in bs
--
-- this means that we have `permute (getPermutation as bs) as == bs`
getPermutation :: forall m a. (MonadInternalError m, Eq a, Show a) => [a] -> [a] -> m [Int]
getPermutation xs ys = mapM (findPos ys) xs
  where
    findPos :: [a] -> a -> m Int
    findPos (b:bs) a | a == b    = pure 0
    findPos (b:bs) a | otherwise = (1 P.+) <$> findPos bs a
    findPos []     a             = internalError $ "While searching for a permutation to map "
                                                   <> showT xs <> " ↦ " <> showT ys
                                                   <> ", could not find the element " <> showT a
                                                   <> "in the second list."



-- apply the dropping permutation given by the integer list
permuteWithDrop :: [Maybe Int] -> [a] -> [a]
permuteWithDrop (Just i:is) as = as !! i : permuteWithDrop is as
permuteWithDrop (Nothing:is) as = permuteWithDrop is as
permuteWithDrop [] as = []

-- for every element in as, we find the position
-- at which it is in bs. If the element does not exist, we mark this position with `Nothing`
--
-- this means that we have `permuteWithDrop (getPermutationWithDrop as bs) as == bs`
getPermutationWithDrop :: forall a. (Eq a, Show a) => [a] -> [a] -> [Int]
getPermutationWithDrop xs ys = let xs' = fmap (findPos xs) ys
                               in [x | Just x <- xs']
  where
    findPos :: [a] -> a -> Maybe Int
    findPos (b:bs) a | a == b    = pure 0
    findPos (b:bs) a | otherwise = (1 P.+) <$> findPos bs a
    findPos []     a             = Nothing


