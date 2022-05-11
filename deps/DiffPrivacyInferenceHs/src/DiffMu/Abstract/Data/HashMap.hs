
{- |
Description: A custom class for hashmap-like containers.
-}
module DiffMu.Abstract.Data.HashMap where

import DiffMu.Prelude

import qualified Data.HashMap.Strict as H

instance Normalize t v => Normalize t (H.HashMap k v) where
  normalize nt map = mapM (normalize nt) map


class DictKey k => DictLikeM t k v d | d -> k v where
  setValueM :: k -> v -> d -> t d
  getValueM :: k -> d -> t (Maybe v)
  deleteValueM :: k -> d -> t d

instance DictKey a => DictKey (Maybe a)
instance DictKey String

class DictKey k => DictLike k v d | d -> k v where
  setValue :: k -> v -> d -> d
  getValue :: k -> d -> Maybe v
  deleteValue :: k -> d -> d
  emptyDict :: d
  isEmptyDict :: d -> Bool
  getAllKeys :: d -> [k]
  getAllElems :: d -> [v]
  getAllKeyElemPairs :: d -> [(k,v)]
  fromKeyElemPairs :: [(k,v)] -> d

instance (DictKey k) => DictLike k v (H.HashMap k v) where
  setValue v m (h) = (H.insert v m h)
  deleteValue v (h) = (H.delete v h)
  getValue k (h) = h H.!? k
  emptyDict = H.empty
  isEmptyDict (h) = H.null h
  getAllKeys (h) = H.keys h
  getAllElems (h) = H.elems h
  getAllKeyElemPairs (h) = H.toList h
  fromKeyElemPairs list = (H.fromList list)

fromKeyElemPairs' list = foldr (\(file,content) d -> appendValue file [content] d) H.empty list

changeValue :: DictLike k v d => k -> (v -> v) -> d -> d
changeValue k f d = case getValue k d of
  Just x -> setValue k (f x) d
  Nothing -> d

appendValue k v d = case getValue k d of
  Just x -> setValue k (x <> v) d
  Nothing -> setValue k v d

popValue :: DictLike k v d => k -> d -> (Maybe v , d)
popValue k d = (getValue k d , deleteValue k d)

restoreValue :: DictLike k v d => d -> k -> d -> (Maybe v , d)
restoreValue oldDict key dict =
  let oldValue = getValue key oldDict
  in case oldValue of
    Nothing        -> (getValue key dict , deleteValue key dict)
    Just oldValue  -> (getValue key dict , setValue key oldValue dict)


getValueMaybe a scope = a >>= (\x -> getValue x scope)
setValueMaybe (Just k) v scope = setValue k v scope
setValueMaybe Nothing v scope = scope




