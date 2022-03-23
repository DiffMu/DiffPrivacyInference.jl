

module DiffMu.Abstract.Class.Log where

import DiffMu.Prelude
import DiffMu.Abstract.Data.Error
-- import DiffMu.Core.Logging -- (DMPersistentMessage(DMPersistentMessage))
import qualified Control.Monad.Except as QUAL

throwError :: (MonadLog m, MonadError e m) => e -> m a
throwError e = do
  -- logForce $ "-------------------------\nError information:\n-----------------------\ncallstack: " <> show callStack <> "\n"
  QUAL.throwError e

class Monad m => MonadLog m where
  log  :: String -> m ()
  debug  :: String -> m ()
  info  :: String -> m ()
  warn :: String -> m ()
  logForce  :: String -> m ()
  withLogLocation :: String -> m a -> m a


throwUnlocatedError e = throwError (WithContext e (DMPersistentMessage ()))


