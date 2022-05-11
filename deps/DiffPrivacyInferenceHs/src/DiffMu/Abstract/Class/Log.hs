

{- |
Description: Class for monads in which logging / throwing of errors can be done.
-}
module DiffMu.Abstract.Class.Log where

import DiffMu.Prelude
import DiffMu.Abstract.Data.Error
import qualified Control.Monad.Except as QUAL

throwError :: (MonadLog m, MonadError e m) => e -> m a
throwError e = do
  -- logForce $ "-------------------------\nError information:\n-----------------------\ncallstack: " <> show callStack <> "\n"
  QUAL.throwError e

class Monad m => MonadLog m where
  log  :: Text -> m ()
  debug  :: Text -> m ()
  info  :: Text -> m ()
  warn :: Text -> m ()
  logForce  :: Text -> m ()
  withLogLocation :: String -> m a -> m a


throwUnlocatedError e = throwError (WithContext e (DMPersistentMessage ()))
throwLocatedError err loc = throwError (WithContext err (DMPersistentMessage loc))


