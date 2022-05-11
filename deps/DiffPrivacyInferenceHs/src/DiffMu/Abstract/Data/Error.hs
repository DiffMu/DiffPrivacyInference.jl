
{-# LANGUAGE UndecidableInstances #-}

{- |
Description: Different error types and printing of (located) messages.
-}
module DiffMu.Abstract.Data.Error where

import DiffMu.Prelude
import DiffMu.Abstract.Data.HashMap

import {-# SOURCE #-} DiffMu.Core.Definitions

import Debug.Trace
import Data.String (IsString)
import qualified Data.Text as T
import qualified Prelude as P
import Data.Graph (edges)
import System.IO (FilePath)
import qualified Data.HashMap.Strict as H
import qualified Data.Array as A

--------------------------------------------------------------------------
-- Printing


newlineIndentIfLong :: StringLike t => t -> t
newlineIndentIfLong xs = if length (linesS xs) <= 1
  then xs
  else "\n" <> indent xs

parenIfMultiple :: StringLike t => t -> t
parenIfMultiple xs = if length (wordsS xs) <= 1
  then xs
  else let sxs = toStringS xs 
           firstChar = sxs !! 0
           lastChar = reverse sxs !! 0
       in if (firstChar == '(' && lastChar == ')')
          then xs
          else "(" <> xs <> ")"


parenIndent :: StringLike s => s -> s
parenIndent s = "\n(\n" <> unlinesS (fmap ("  " <>) (linesS s)) <> ")"

braceIndent :: StringLike s => s -> s
braceIndent s = "\n{\n" <> unlinesS (fmap ("  " <>) (linesS s)) <> "}"


indent :: StringLike s => s -> s
indent s = unlinesS (fmap ("  " <>) (linesS s))

indentWith :: StringLike s => s -> s -> s
indentWith indentText s = intercalateS "\n" (fmap (indentText <>) (linesS s))


indentAfterFirstWith :: StringLike s => s -> s -> s
indentAfterFirstWith indentText s =
  let ls = linesS s
  in case ls of
      [] -> ""
      (l:ls) -> intercalateS "\n" (l : fmap (indentText <>) ls)

prettyEnumVertical :: StringLike s => [s] -> s
prettyEnumVertical as = "{\n" <> intercalateS "\n,\n" (fmap (indentWith "|   ") as) <> "\n}"


--------------------------------------------------------------------------
-- Locations


data SourceLoc = SourceLoc
  {
    getLocFile  :: SourceFile
  , getLocBegin :: Int
  , getLocEnd   :: Int
  }
  deriving (Eq, Ord)

data SourceLocExt = ExactLoc SourceLoc | RelatedLoc Text SourceLocExt | UnknownLoc | NotImplementedLoc Text
  deriving (Eq, Ord)

data Located a = Located
  {
    getLocation :: SourceLocExt
  , getLocated :: a
}
  deriving (Functor, Foldable, Traversable, Eq)

instance Normalize t a => Normalize t (Located a) where
  normalize e (Located loc a) = Located loc <$> normalize e a

instance Show a => Show (Located a) where
  show (Located loc a) = show a


instance ShowLocated a => ShowLocated (Located a) where
  showLocated (Located loc a) = showLocated a

downgradeToRelated :: Text -> SourceLocExt -> SourceLocExt
downgradeToRelated = RelatedLoc

notLocated :: a -> Located a
notLocated = Located UnknownLoc

instance Monad t => Normalize t SourceLocExt where
  normalize e = pure

instance ShowPretty SourceLoc where
  showPretty (SourceLoc file begin end) =
    let file' = showT file
    in case (begin P.+ 1 >= end) of
        True -> file' <> ": line " <> showPretty begin
        False -> file' <> ": between lines " <> showPretty begin <> " and " <> showPretty end


instance Show SourceLocExt where
  show = T.unpack . showPretty

instance ShowLocated SourceLoc where
  showLocated loc@(SourceLoc file (begin) (end)) = do
    sourcelines <- printSourceLines file (begin, end)
    return $ (showPretty loc) <> "\n"
             <> sourcelines

instance ShowPretty SourceLocExt where
  showPretty = \case
    ExactLoc sl -> showPretty sl
    RelatedLoc s sle -> showPretty s <> ": " <> showPretty sle
    UnknownLoc -> "Unknown location"
    NotImplementedLoc s -> "This location is currently ineffable. (" <> showPretty s <> ")"


instance ShowLocated SourceLocExt where
  showLocated = \case
    ExactLoc sl -> showLocated sl
    RelatedLoc s sle -> do s' <- showLocated s
                           sle' <- showLocated sle
                           return $ s' <> ": " <> sle'
    UnknownLoc -> pure "Unknown location"
    NotImplementedLoc s -> do
      s' <- showLocated s
      return $ "This location is currently ineffable. (" <> s' <> ")"

-------------------------------------------------------------------------
-- Source Quotes

newtype SourceQuote = SourceQuote [(SourceLocExt, Text)]
  deriving (Show)


instance Monad t => Normalize t SourceQuote where
  normalize e = pure

instance ShowLocated SourceQuote where
  showLocated (SourceQuote sts) =
    let f (ExactLoc (SourceLoc file begin end),text) = [(file, (begin,text))]
        f (RelatedLoc _ l, text) = f (l,text)
        f _ = []

        betterLocs = sts >>= f
        locsByFile :: H.HashMap (SourceFile) [(Int,Text)]
        locsByFile = fromKeyElemPairs' betterLocs

        changeSource :: Array Int Text -> [(Int,Text)] -> Array Int Text
        changeSource = A.accum (\line edit -> line <> blue ("  <- " <> edit))

    in do
      RawSource originalSource <- ask
      let changedSource = H.mapWithKey (\k v -> case getValue k locsByFile of
                                                  Nothing -> v
                                                  Just edit -> changeSource v edit
                                        )
                              originalSource 

      let printSingle (fp, edits) =
            let lines = fst <$> edits
            in showT fp <> ":\n"
               <> printSourceLinesFromSource (RawSource changedSource) fp (minimum lines, maximum lines P.+ 1)

      let result = intercalateS "\n" (printSingle <$> (H.toList locsByFile))

      return (result)


-------------------------------------------------------------------------
-- Printing source

--
-- conditions:
--  - `begin <= end`
--
printSourceLines :: MonadReader RawSource t => SourceFile -> (Int,Int) -> t Text
printSourceLines fp (begin,end) = do
  let numbersize = length (show end)
  RawSource source <- ask
  case H.lookup fp source of
    Just source -> do
      let printed_lines = fmap (printSourceLine source numbersize) [begin .. (end - 1)]
      let edge = T.pack $ take (numbersize P.+ 2) (repeat ' ') <> "|"
      return $ edge <> "\n"
               <> T.concat (fmap (<> "\n") printed_lines)
               <> edge <> "\n"
    Nothing -> return $    "  |\n"
                        <> "  | <<source not available>>\n"
                        <> "  | (for file: " <> T.pack (show fp) <> ")\n"
                        <> "  |\n"


--
-- conditions:
--  - `begin <= end`
--
printSourceLinesFromSource :: RawSource -> SourceFile -> (Int,Int) -> Text
printSourceLinesFromSource rsource fp range = runReader (printSourceLines fp range) rsource

--
-- conditions:
--  - `length(show(linenumber)) <= required_numbersize`
--
printSourceLine :: Array Int Text -> Int -> Int -> Text
printSourceLine source required_numbersize linenumber =
  let printed_linenumber = show linenumber
      padded_linenumber = take (required_numbersize - length printed_linenumber) (repeat ' ') <> printed_linenumber
      required_line = source ! linenumber
  in " " <> T.pack padded_linenumber <> " |     " <> required_line


-------------------------------------------------------------------------
type MessageLike t a = (Normalize t a, Show a, ShowLocated a)

data DMPersistentMessage t where
  DMPersistentMessage :: MessageLike t a => a -> DMPersistentMessage t


instance Show (DMPersistentMessage t) where
  show (DMPersistentMessage msg) = show msg

instance ShowLocated (DMPersistentMessage t) where
  showLocated (DMPersistentMessage msg) = showLocated msg

instance Monad t => Normalize t (DMPersistentMessage t) where
  normalize e (DMPersistentMessage msg) = DMPersistentMessage <$> normalize e msg

instance MonadReader RawSource t => SemigroupM t (DMPersistentMessage t) where
  (DMPersistentMessage a) ⋆ (DMPersistentMessage b) = return (DMPersistentMessage $ a :-----: b)

instance MonadReader RawSource t => MonoidM t (DMPersistentMessage t) where
  neutral = pure (DMPersistentMessage ())

instance Monad t => CheckNeutral t (DMPersistentMessage t) where
  checkNeutral b = pure False

data WithContext e t = WithContext e (DMPersistentMessage t)


instance ShowLocated e => ShowLocated (WithContext e t) where
  showLocated (WithContext e ctx) = do
    e' <- showLocated e
    ctx' <- showLocated ctx
    return $ e' <> "\n" <> indent ctx'


instance Show e => Show (WithContext e t) where
  show (WithContext e ctx) = show e


withContext e x = WithContext e (DMPersistentMessage x)

type LocatedDMException t = WithContext DMException t


--------------------------------------------------------------------------
-- DMException
--
-- The different kinds of errors we can throw.

data DMException where
  UnsupportedError        :: Text -> DMException
  UnificationError        :: Show a => a -> a -> DMException
  WrongNumberOfArgs       :: Show a => a -> a -> DMException
  WrongNumberOfArgsOp     :: Show a => a -> Int -> DMException
  ImpossibleError         :: Text -> DMException
  InternalError           :: Text -> DMException
  VariableNotInScope      :: Show a => a -> DMException
  UnsatisfiableConstraint :: String -> DMException
  TypeMismatchError       :: Text -> DMException
  NoChoiceFoundError      :: String -> DMException
  UnblockingError         :: String -> DMException
  DemutationError         :: Text -> DMException
  DemutationDefinitionOrderError :: Show a => a -> DMException
  DemutationVariableAccessTypeError :: Text -> DMException
  BlackBoxError           :: String -> DMException
  FLetReorderError        :: String -> DMException
  UnificationShouldWaitError :: DMTypeOf k -> DMTypeOf k -> DMException
  TermColorError          :: AnnotationKind -> Text -> DMException
  ParseError              :: String -> Maybe String -> Int -> Int-> DMException -- error message, filename, line number, line number of next expression
  DemutationMovedVariableAccessError :: Show a => a -> DMException
  DemutationLoopError     :: Text -> DMException
  DemutationNonAliasedMutatingArgumentError :: Text -> DMException
  DemutationSplitMutatingArgumentError :: Text -> DMException

instance Show DMException where
  show (UnsupportedError t) = "The term '" <> T.unpack t <> "' is currently not supported."
  show (UnificationError a b) = "Could not unify '" <> show a <> "' with '" <> show b <> "'."
  show (WrongNumberOfArgs a b) = "While unifying: the terms '" <> show a <> "' and '" <> show b <> "' have different numbers of arguments"
  show (WrongNumberOfArgsOp op n) = "The operation " <> show op <> " was given a wrong number (" <> show n <> ") of args."
  show (ImpossibleError e) = "Something impossible happened: " <> T.unpack e
  show (InternalError e) = "Internal error: " <> T.unpack e
  show (VariableNotInScope v) = "Variable not in scope: " <> show v
  show (UnsatisfiableConstraint c) = "The constraint " <> c <> " is not satisfiable."
  show (TypeMismatchError e) = "Type mismatch: " <> T.unpack e
  show (NoChoiceFoundError e) = "No choice found: " <> e
  show (UnificationShouldWaitError a b) = "Trying to unify types " <> show a <> " and " <> show b <> " with unresolved infimum (∧)."
  show (UnblockingError e) = "While unblocking, the following error was encountered:\n " <> e
  show (DemutationError e) = "While demutating, the following error was encountered:\n " <> T.unpack e
  show (BlackBoxError e) = "While preprocessing black boxes, the following error was encountered:\n " <> e
  show (FLetReorderError e) = "While processing function signatures, the following error was encountered:\n " <> e
  show (ParseError e (Just file) line nextline) = case line == nextline of
                                                True -> "Unsupported julia expression in file " <> file <> ", line " <> show line <> ":\n " <> e
                                                False -> "Unsupported julia expression in file " <> file <> ", between line " <> show line <> " and " <> show nextline <> ":\n " <> e
  show (ParseError e Nothing line nextline) = case line == nextline of
                                                True -> "Unsupported julia expression in \"none\", line " <> show line <> ":\n " <> e
                                                False -> "Unsupported julia expression in \"none\", between line " <> show line <> " and " <> show nextline <> ":\n " <> e
  show (TermColorError color t) = "Expected " <> show t <> " to be a " <> show color <> " expression but it is not."
  show (DemutationDefinitionOrderError a) = "The variable '" <> show a <> "' has not been defined before being used.\n"
                                            <> "Note that every variable has to be assigned some value prior to its usage.\n"
                                            <> "Here, 'prior to usage' means literally earlier in the code."
  show (DemutationLoopError e) = "An error regarding loop demutation occured:\n" <> T.unpack e
  show (DemutationVariableAccessTypeError e) = "An error regarding variable access types occured:\n" <> T.unpack e
  show (DemutationMovedVariableAccessError a) = "Tried to access the variable " <> show a <> ". But this variable is not valid anymore, because it was assigned to something else."
  show (DemutationNonAliasedMutatingArgumentError a) = "An error regarding non-aliasing of mutating arguments occured:\n" <> T.unpack a
  show (DemutationSplitMutatingArgumentError a) = "An error regarding mutating arguments occured:\n" <> T.unpack a

instance ShowPretty (DMException) where
  showPretty = T.pack . show

instance ShowLocated (DMException) where
  showLocated = return . showPretty

instance Eq DMException where
  UnificationError        a a2     == UnificationError        b b2    = True
  WrongNumberOfArgs       a a2     == WrongNumberOfArgs       b b2    = True
  WrongNumberOfArgsOp     a a2     == WrongNumberOfArgsOp     b b2    = True
  ImpossibleError         a        == ImpossibleError         b       = True
  InternalError           a        == InternalError           b       = True
  VariableNotInScope      a        == VariableNotInScope      b       = True
  UnsatisfiableConstraint a        == UnsatisfiableConstraint b       = True
  TypeMismatchError       a        == TypeMismatchError       b       = True
  NoChoiceFoundError      a        == NoChoiceFoundError      b       = True
  UnificationShouldWaitError a a2  == UnificationShouldWaitError b b2 = True
  ParseError e1 file1 line1 nlne1  == ParseError e2 file2 line2 nlne2 = True
  FLetReorderError        a        == FLetReorderError        b       = True
  TermColorError      a b          == TermColorError c d              = True
  DemutationError a                == DemutationError         b       = True
  DemutationDefinitionOrderError a == DemutationDefinitionOrderError b = True
  DemutationLoopError a == DemutationLoopError b = True
  DemutationVariableAccessTypeError a == DemutationVariableAccessTypeError b = True
  DemutationMovedVariableAccessError a       == DemutationMovedVariableAccessError b = True
  DemutationNonAliasedMutatingArgumentError a       == DemutationNonAliasedMutatingArgumentError b = True
  DemutationSplitMutatingArgumentError a       == DemutationSplitMutatingArgumentError b = True
  _ == _ = False


-- throwLocatedError e xs = throwError (WithContext e [(s,)])


isCriticalError e = case e of
  ImpossibleError s -> True
  InternalError s -> True
  _ -> False


data WrapMessageNatural s t e a = WrapMessageNatural (forall x. t x -> s (Maybe x)) a

instance Show a => Show (WrapMessageNatural s t e a) where show (WrapMessageNatural f a) = show a
instance (Monad s, ShowLocated a) => ShowLocated (WrapMessageNatural s t e a) where showLocated (WrapMessageNatural f a) = showLocated a

instance (Monad s, Normalize t a) => Normalize s (WrapMessageNatural s t e a) where
  normalize level (WrapMessageNatural f x) = WrapMessageNatural f <$> do
    x' <- f (normalize level x)
    case x' of
      Just x'' -> return x''
      Nothing -> pure x

instance IsNaturalError (WithContext e) where
  functionalLift α (WithContext x (DMPersistentMessage msg)) = WithContext x (DMPersistentMessage (WrapMessageNatural @_ @_ @e α msg))

class IsNaturalError e where
  functionalLift :: (Monad t, Monad s) => (forall a. t a -> s (Maybe a)) -> e t -> e s


class (IsNaturalError e, MonadError (e t) t) => MonadDMError e t where
  isCritical :: e t -> t Bool
  persistentError :: LocatedDMException t -> t ()
  catchAndPersist :: MessageLike t x => t a -> (DMPersistentMessage t -> t (a, x)) -> t a
  enterNonPersisting :: t ()
  exitNonPersisting :: t ()


--------------------------------------------------------------------
----------------- message construction -----------------------------
--------------------------------------------------------------------



instance Monad t => Normalize t Char where
  normalize e = pure


-------------------------------------------------------------------------
-- Vertical combination

infixl 5 :-----:
data (:-----:) a b = (:-----:) a b
  deriving (Show)

instance (ShowLocated a, ShowLocated b) => ShowLocated (a :-----: b) where
  showLocated (a :-----: b) = do
    a' <- showLocated a
    b' <- showLocated b
    return $       a'
                   <> "\n"
                   <> "---------------------------------------------------------"
                   <> "\n"
                   <> b'

instance (Normalize t a, Normalize t b) => Normalize t (a :-----: b) where
  normalize e (a :-----: b) = (:-----:) <$> normalize e a <*> normalize e b

--------------

infixl 5 :\\:
data (:\\:) a b = (:\\:) a b
  deriving (Show)

instance (ShowLocated a, ShowLocated b) => ShowLocated (a :\\: b) where
  showLocated (a :\\: b) = do
    a' <- showLocated a
    b' <- showLocated b
    return $       a'
                   <> "\n"
                   <> b'

instance (Normalize t a, Normalize t b) => Normalize t (a :\\: b) where
  normalize e (a :\\: b) = (:\\:) <$> normalize e a <*> normalize e b

--------------

infixl 5 :\\->:
data (:\\->:) a b = (:\\->:) a b
  deriving (Show)

instance (ShowLocated a, ShowLocated b) => ShowLocated (a :\\->: b) where
  showLocated (a :\\->: b) = do
    a' <- showLocated a
    b' <- showLocated b
    return $ a' <> " " <> newlineIndentIfLong b'

instance (Normalize t a, Normalize t b) => Normalize t (a :\\->: b) where
  normalize e (a :\\->: b) = (:\\->:) <$> normalize e a <*> normalize e b


-------------------------------------------------------------------------
-- Horizontal combination

infixl 6 :<>:
data (:<>:) a b = (:<>:) a b
  deriving (Show)

instance (ShowLocated a, ShowLocated b) => ShowLocated (a :<>: b) where
  showLocated (a :<>: b) = do
    a' <- showLocated a 
    b' <- showLocated b 
    return $ a' <> " " <> b'

instance (Normalize t a, Normalize t b) => Normalize t (a :<>: b) where
  normalize e (a :<>: b) = (:<>:) <$> normalize e a <*> normalize e b

-------------------------------------------------------------------------
-- Quote wrapping

data Quote a = Quote a
  deriving (Show)

quote :: Text -> Text
quote a = "'" <> a <> "'"

instance (ShowLocated a) => ShowLocated (Quote a) where
  showLocated (Quote a) = do
    a' <- showLocated a
    return $ quote a'

instance (Normalize t a) => Normalize t (Quote a) where
  normalize e (Quote a) = Quote <$> normalize e a


