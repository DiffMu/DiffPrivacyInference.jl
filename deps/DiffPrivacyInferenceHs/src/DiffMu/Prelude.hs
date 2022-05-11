{-# LANGUAGE UndecidableInstances #-}

{-
Description: Provides various basic types and classes.
-}
module DiffMu.Prelude
  (
    module All
  , StringLike (..)
  , RawSource (..)
  , SourceFile (..)
  , rawSourceFromString
  , NamePriority (..)
  , CompoundPriority (..)
  , Symbol (..)
  , IxSymbol (..)
  , SymbolOf (..)
  , DictKey (..)
  , KHashable (..)
  , KShow (..)
  , KEq (..)
  , IsKind (..)
  , HasVarPriority (..)
  , FromSymbol (..)
  , composeFun
  , composeFunM
  , MonadImpossible (..)
  , MonadInternalError (..)
  , MonadUnificationError (..)
  , ProcVar (..)
  , TeVar (..)
  , ScopeVar (..)
  , MemVar (..)
  , ShowPretty (..)
  , ShowLocated (..)
  , (:=:) (..)
  , throwOriginalError
  , blue, green, yellow, red, magenta
  , (&&), (||)
  , showT
  , findDuplicatesWith
  , (%=~)
  )
  where

import DiffMu.Imports as All hiding (msum, throwError)
import qualified DiffMu.Imports as QUAL (throwError)


import DiffMu.Prelude.MonadicAlgebra as All
import Data.List.Unicode as All
import Data.String as S
import Data.Array as All hiding (index, indices)

import Prelude ((&&),(||),div,rem,(/),(!!))
import qualified Prelude (String)
import qualified Data.Text as T
import Data.HashMap.Strict as H
import System.IO (FilePath, readFile)
import GHC.IO (catchAny)


-------------------------------------------------------------------------
-- kinds for introspection

type IsKind k = (SingI k, Typeable k)

-------------------------------------------------------------------------
-- normalization

instance Monad t => Normalize t IxSymbol where
  normalize nt a = pure a

instance Monad t => Normalize t Symbol where
  normalize nt a = pure a

instance Monad t => Normalize t Text where
  normalize nt a = pure a

instance Monad t => Normalize t ProcVar where
  normalize nt a = pure a


instance Monad t => Normalize t (TeVar) where
  normalize nt v = pure v


-------------------------------------------------------------------------
-- name / var priority


-- NOTE : Order is important
data NamePriority = GeneratedNamePriority | UserNamePriority
  deriving (Eq, Ord, Generic, Show)

instance Hashable NamePriority

data CompoundPriority = CompoundPriority NamePriority Int
  deriving (Show, Eq)

instance Ord CompoundPriority where
  CompoundPriority n1 i1 <= CompoundPriority n2 i2 | n1 == n2 = i1 >= i2
  CompoundPriority n1 i1 <= CompoundPriority n2 i2 | n1 > n2  = False
  CompoundPriority n1 i1 <= CompoundPriority n2 i2 | otherwise = True

class HasVarPriority v where
  varPriority :: IsKind k => v k -> CompoundPriority

instance HasVarPriority SymbolOf where
  varPriority (SymbolOf (IxSymbol (_,ix,np))) = CompoundPriority np ix

-------------------------------------------------------------------------
-- StringLike

class (IsString t, Semigroup t, Ord t) => StringLike t where
  wordsS :: t -> [t]
  linesS :: t -> [t]
  unlinesS :: [t] -> t
  intercalateS :: t -> [t] -> t
  fromStringS :: String -> t
  toStringS :: t -> String
  lengthS :: t -> Int

instance StringLike Text where
  wordsS = T.words
  linesS = T.lines
  unlinesS = T.unlines
  intercalateS = T.intercalate
  fromStringS = T.pack
  toStringS = T.unpack
  lengthS = T.length

instance StringLike String where
  wordsS = S.words
  linesS = S.lines
  unlinesS = S.unlines
  intercalateS = intercalate
  fromStringS = \a -> a
  toStringS = \a -> a
  lengthS = length

showT :: Show a => a -> Text
showT = T.pack . show


-------------------------------------------------------------------------
-- ShowLocated

class ShowLocated a where
  showLocated :: MonadReader RawSource t => a -> t Text

instance ShowLocated () where
  showLocated _ = return ""

instance ShowLocated Text where
  showLocated a = return a

instance ShowLocated Symbol where
  showLocated (Symbol a) = return a

instance ShowLocated IxSymbol where
  showLocated a = T.pack <$> (return $ show a)

instance ShowLocated TeVar where
  showLocated = pure . showPretty

instance ShowLocated ProcVar where
  showLocated = pure . showPretty

instance ShowLocated a => ShowLocated [a] where
  showLocated as = do
    as' <- (mapM showLocated as)
    return $ "[" <> T.intercalate ", " as' <> "]"

-------------------------------------------------------------------------
-- ShowPretty

class ShowPretty a where
  showPretty :: a -> Text

instance ShowPretty () where
  showPretty _ = ""

instance ShowPretty Int where
  showPretty = T.pack . show

instance ShowPretty Text where
  showPretty s = s

instance (ShowPretty a, ShowPretty b) => ShowPretty (a,b) where
  showPretty (a,b) = "("<> showPretty a <> ", " <> showPretty b <> ")"

class FromSymbol (v :: j -> *) where
  fromSymbol :: Symbol -> Int -> NamePriority -> v k


newtype SymbolOf (k :: j) = SymbolOf IxSymbol
  deriving (Eq, Hashable)


instance FromSymbol SymbolOf where
  fromSymbol v n p = SymbolOf (IxSymbol (v, n, p))

class (Eq v, Hashable v) => DictKey v

instance DictKey v => DictKey [v]

-------------------------------------------------------------------------
-- Symbols & IxSymbols

newtype Symbol = Symbol Text
  deriving (Eq,Ord,Hashable,Semigroup,Monoid)

newtype IxSymbol = IxSymbol (Symbol,Int,NamePriority)
  deriving (Eq,Ord,Hashable)


-- WARNING: Not total
showSubscriptDigit :: Int -> Char
showSubscriptDigit a | a <= 9 = ['₀' .. '₉'] !! a
showSubscriptDigit _ = undefined

showSubscriptInt :: Int -> String
showSubscriptInt a | a <= 9 = showSubscriptDigit a : []
showSubscriptInt a          =
  let last = (a `rem` 10)
      beforeLast = (a - last) `div` 10
  in showSubscriptInt beforeLast <> (showSubscriptDigit last : [])

showWithSubscript :: Show a => (a,Int) -> String
showWithSubscript (a,0) = show a
showWithSubscript (a,n) = show a <> showSubscriptInt n

instance Show IxSymbol where
  show (IxSymbol (x,n,p)) = showWithSubscript (x,n)

instance DictKey IxSymbol

instance ShowPretty IxSymbol where
  showPretty = T.pack . show

instance Show (SymbolOf k) where
  show (SymbolOf x :: SymbolOf k) = show x --  <> " : " <> show (demote @k)

instance Show Symbol where
  show (Symbol t) = T.unpack t

instance ShowPretty Symbol where
  showPretty = T.pack . show

instance DictKey Symbol


-------------------------------------------------------------------------
-- proc variables

data ProcVar = UserProcVar (Symbol) | GenProcVar (IxSymbol)
  deriving (Eq,Generic, Ord)

instance Hashable ProcVar
instance Show ProcVar where
  show (UserProcVar x) = show x
  show (GenProcVar x) =  show x

instance ShowPretty ProcVar where
  showPretty (UserProcVar x) = T.pack $ show x
  showPretty (GenProcVar x) =  T.pack $ show x

instance DictKey ProcVar

-------------------------------------------------------------------------
-- term variables

data TeVar = UserTeVar ProcVar | GenTeVar IxSymbol (Maybe TeVar)
  deriving (Eq,Generic, Ord)

instance Hashable TeVar
instance Show TeVar where
  show (UserTeVar x) = show x
  show (GenTeVar x pv) = "gen_" <> show x
instance ShowPretty TeVar where
  showPretty (UserTeVar x) = showPretty x
  showPretty (GenTeVar x pv) = case pv of
    Just pv -> showPretty pv
    Nothing -> T.pack $ show x

instance DictKey TeVar



-------------------------------------------------------------------------
-- scope variables

data ScopeVar = ScopeVar IxSymbol
  deriving (Eq,Generic, Ord)

instance Hashable ScopeVar
instance Show ScopeVar where
  show (ScopeVar x) = show x
instance DictKey ScopeVar

-------------------------------------------------------------------------
-- memory variables

data MemVar = MemVarForProcVar ProcVar IxSymbol | StandaloneMemVar IxSymbol
  deriving (Eq,Generic, Ord)

instance Hashable MemVar
instance Show MemVar where
  show (MemVarForProcVar p x) = show p <> "#" <> show x
  show (StandaloneMemVar x) = show x

instance ShowPretty MemVar where
  showPretty = showT

instance DictKey MemVar


-------------------------------------------------------------------------
-- hashing constraints

type KHashable :: (j -> *) -> Constraint
type KHashable v = (forall k. Hashable (v k))

type KShow :: (j -> *) -> Constraint
type KShow v = (forall k. Show (v k))

type KEq :: (j -> *) -> Constraint
type KEq v = (forall k. Eq (v k))

-------------------------------------------------------------------------
-- custom tuples

data (:=:) a b = (:=:) a b
  deriving (Eq)

instance (Show a, Show b) => Show (a :=: b) where
  show (a :=: b) = show a <> " :=: " <> show b

instance (Normalize t a, Normalize t b) => Normalize t (a :=: b) where
  normalize nt (a :=: b) =  (:=:) <$> normalize nt a <*> normalize nt b


-------------------------------------------------------------------------
-- basic monad classes

class Monad t => MonadImpossible t where
  impossible :: Text -> t a

class Monad t => MonadInternalError t where
  internalError :: Text -> t a

class Monad t => MonadUnificationError t where
  unificationError :: Show a => a -> a -> t b

throwOriginalError :: (MonadError e m) => e -> m a
throwOriginalError = QUAL.throwError


-------------------------------------------------------------------------
-- colors in terminal output

blue x = "\27[34m" <> x <> "\27[0m"
green x = "\27[32m" <> x <> "\27[0m"
yellow x = "\27[33m" <> x <> "\27[0m"
red x = "\27[31m" <> x <> "\27[0m"
magenta x = "\27[35m" <> x <> "\27[0m"


-------------------------------------------
-- algorithms

findDuplicatesWith :: forall a b. Eq a => (b -> a) -> [b] -> [b]
findDuplicatesWith f = findDuplicates' []
  where
    findDuplicates' :: [a] -> [b] -> [b]
    findDuplicates' good [] = []
    findDuplicates' good (a:as) = case f a `elem` good of
      False -> findDuplicates' (f a:good) as
      True  -> a : findDuplicates' (good) as


-------------------------------------------------------------------------
-- generic utility functions

composeFun :: [a -> a] -> a -> a
composeFun [] a = a
composeFun (f:fs) a = f (composeFun fs a)

composeFunM :: Monad t => [a -> t a] -> a -> t a
composeFunM [] a = return a
composeFunM (f:fs) a = do
  rs <- composeFunM fs a
  f rs

-------------------------------------------------------------------------
-- source file reading

newtype SourceFile = SourceFile (Maybe FilePath)
  deriving (Eq, Hashable, DictKey, Ord)

instance Show SourceFile where
  show (SourceFile Nothing) = "none"
  show (SourceFile (Just fp)) = fp

newtype RawSource = RawSource (HashMap SourceFile (Array Int Text))
  deriving (Show)

rawSourceFromString :: String -> [FilePath] -> IO RawSource
rawSourceFromString input other_files = do
  let make_line_array file = let ls = (T.pack <$> linesS file)
                             in  listArray (1,length ls) (ls) 
  let tryReadFile f = (Just <$> readFile f) `catchAny` (\e -> return Nothing)

  let onlyJust xs = [(SourceFile (Just a), make_line_array b) | (a, Just b) <- xs]

  other_file_contents <- mapM tryReadFile other_files
  let good_other_file_contents = onlyJust ((other_files) `zip` (other_file_contents))
  return $ RawSource $ H.fromList $
    ((SourceFile Nothing, make_line_array input)
    :
    (good_other_file_contents)
    )


-------------------------------------------------------------------------
-- lens operators

-- Helper function for using a monadic function to update the state of a "by a lens accessible"
-- value in a state monad. Such an operator does not seem to be defined in the "lenses" library.
-- This might be because using it is not always well behaved, the following note applies.
--
-- NOTE: Warning, this function destroys information if the function `f` which does the update
-- has monadic effects in m which affect the part of the state which is accessed by the lens.
(%=~) :: MonadState s m => (forall f. Functor f => LensLike f s s a a) -> (a -> m a) -> m ()
(%=~) lens f = do
  curVal <- use lens
  newVal <- f curVal
  lens .= newVal
  return ()

infixr 4 %=~
