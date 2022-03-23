
module DiffMu.Abstract.Data.Error where

import DiffMu.Prelude

type role DMPersistentMessage nominal
data DMPersistentMessage (t :: * -> *)
data DMException
type role WithContext representational nominal
data WithContext (e :: *) (t :: * -> *)
type LocatedDMException t = WithContext DMException t
class IsNaturalError (e :: (* -> *) -> *)
class (IsNaturalError e, MonadError (e t) t) => MonadDMError e t where
  isCritical :: e t -> t Bool
  persistentError :: LocatedDMException t -> t ()
  catchAndPersist :: (Normalize t x, ShowPretty x, Show x) => t a -> (DMPersistentMessage t -> t (a, x)) -> t a
  enterNonPersisting :: t ()
  exitNonPersisting :: t ()

