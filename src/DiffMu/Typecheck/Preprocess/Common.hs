
{-# LANGUAGE TemplateHaskell #-}

{- |
Description: Definition of `LightTC`, a monad with state, logging and errors to be used by the preprocessing steps.
-}
module DiffMu.Typecheck.Preprocess.Common where

import DiffMu.Prelude
import DiffMu.Abstract
import DiffMu.Core
import DiffMu.Core.TC
import DiffMu.Core.Logging

import qualified Data.HashMap.Strict as H

import qualified Data.Text as T

import Debug.Trace



newtype LightTC l s a = LightTC {runLightTC :: ((StateT s (ExceptT (LocatedDMException (LightTC l s)) (ReaderT RawSource (Writer (DMMessages (LightTC l s) ))))) a)}
  deriving (Functor, Applicative, Monad, MonadState s, MonadError (LocatedDMException (LightTC l s)), MonadWriter (DMMessages (LightTC l s)), MonadReader RawSource)

instance ISing_DMLogLocation l => MonadInternalError (LightTC l s) where
  internalError = throwUnlocatedError . InternalError

instance ISing_DMLogLocation l => MonadImpossible (LightTC l s) where
  impossible = throwUnlocatedError . ImpossibleError

instance ISing_DMLogLocation l => MonadLog (LightTC l a) where
  log = logWithSeverityOfMut Debug
  debug = logWithSeverityOfMut Debug
  info = logWithSeverityOfMut Info
  logForce = logWithSeverityOfMut Force
  warn = logWithSeverityOfMut Warning
  withLogLocation loc action = internalError "setting of location for logging in mtc not implemented"


-- logging
logWithSeverityOfMut :: forall l a. ISing_DMLogLocation l => DMLogSeverity -> Text -> LightTC l a ()
logWithSeverityOfMut sev text = do
  -- here we split the messages at line breaks (using `lines`)
  -- in order to get consistent looking output (every line has a header)
  let messages = DMLogMessage sev (singDMLogLocation (Proxy @l)) <$> (reverse $ linesS text)
  tell (DMMessages messages [])

-- lifting

newtype WrapMessageLight a = WrapMessageLight a
  deriving (Show)
instance ShowPretty a => ShowPretty (WrapMessageLight a) where
  showPretty (WrapMessageLight a) = showPretty a
instance ShowLocated a => ShowLocated (WrapMessageLight a) where
  showLocated (WrapMessageLight a) = showLocated a
instance Monad m => Normalize m (WrapMessageLight a) where
  normalize e x = pure x

liftNewLightTC :: Default s => LightTC l s a -> TC a
liftNewLightTC a =
  let s = runReaderT $ runExceptT $ runStateT (runLightTC a) def

      h = \(DMPersistentMessage a) -> DMPersistentMessage (WrapMessageLight a)

      i = \(WithContext e ctx) -> WithContext e (h ctx)

      g :: DMMessages (LightTC l1 s1) -> DMMessages (TCT Identity)
      g (DMMessages xs ys) = DMMessages xs (fmap i ys)

      f :: (Either (LocatedDMException (LightTC l s)) (a, s), DMMessages (LightTC l s)) -> (Either (LocatedDMException (TCT Identity)) (a, Full (DMPersistentMessage TC)), DMMessages (TCT Identity))
      f (Left (WithContext e ctx), b) = (Left (WithContext e (h ctx)) , g b)
      f (Right (a, s), b) = (Right (a, def), g b)

  in TCT (StateT (\t -> ExceptT (ReaderT (\readstate -> (WriterT (return (f $ runWriter $ s readstate)))))))

liftLightTC :: forall s t k l a. s -> (s -> t) -> LightTC k s a -> LightTC l t a
liftLightTC start conv a =
  let s = (runReaderT $ runExceptT $ runStateT (runLightTC a) start)

      h = \(DMPersistentMessage a) -> DMPersistentMessage (WrapMessageLight a)

      i = \(WithContext e ctx) -> WithContext e (h ctx)

      g :: DMMessages (LightTC k1 s) -> DMMessages (LightTC k2 t)
      g (DMMessages xs ys) = DMMessages xs (fmap (i) ys)

      f :: (Either (LocatedDMException (LightTC k1 s)) (a, s), DMMessages (LightTC k1 s)) -> (Either (LocatedDMException (LightTC l t)) (a, t), DMMessages (LightTC l t))
      f (Left (WithContext e ctx), b) = (Left (WithContext e (h ctx)) , g b)
      f (Right (a, s), b) = (Right (a, conv s), g b)

  in LightTC (StateT (\t -> ExceptT (ReaderT (\readstate -> WriterT (return (f $ runWriter $ s readstate))))))


