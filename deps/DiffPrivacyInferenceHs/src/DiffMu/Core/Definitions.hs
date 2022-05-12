
{-# LANGUAGE TemplateHaskell, UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}

{- |
Description: Definitions of basic type-checking-relevant data types such as terms and types.
-}
module DiffMu.Core.Definitions where

import DiffMu.Prelude

import DiffMu.Core.Symbolic
import DiffMu.Abstract
import DiffMu.Core.Logging

import {-# SOURCE #-} DiffMu.Core.TC

import Data.Singletons.TH

import           Data.Singletons.Prelude hiding (Symbol)
import           Data.Singletons.Prelude.Enum (SEnum (..))
import           Data.Singletons.Prelude.List hiding (Group)

import qualified Data.Text as T

import Data.HashMap.Strict

import           Foreign.C.String
import           Foreign.C.Types
import           Foreign.Ptr

---------------------------------------------------------
-- Definition of Meta variables
--
-- We are going to need a type of variables/symbols which
-- do not only contain a string for a name, but also which
-- are annotated with some kind k from some type j containing
-- these kinds, i.e. (k :: j).
-- For this we use the `SymbolOf (k :: j)` type defined in our Prelude.

-- Here we simply add abbreviations for the variable types which we
-- are going to use.
-- The Notation with the "@" symbol comes from the "TypeApplications" ghc-extension.
-- It allows us to explicitly set "j := DMKind" or "j := SensKind". Such that the
-- k's with which TVarOf (resp. SVarOf) are annotated must come from the `DMKind`
-- (resp. `SensKind`) type.
type TVarOf = SymbolOf @DMKind
type SVarOf = SymbolOf @SensKind

-- We further add abbreviations for type/sens variables of their respective "main"-kind.
type TVar   = TVarOf MainKind
type SVar   = SVarOf MainSensKind

-- NOTE: Sensitivities only have a single kind, `MainSensKind`.

---------------------------------------------------------
-- Definition of DMTypes
--


data AnnotationKind = SensitivityK | PrivacyK
  deriving (Show, Eq)

instance ShowPretty AnnotationKind where
    showPretty SensitivityK = "SensitivityKind"
    showPretty PrivacyK = "PrivacyKind"

instance Monad t => Normalize t AnnotationKind where
  normalize nt a = pure a

data Annotation (a :: AnnotationKind) where
  SensitivityAnnotation :: SymTerm MainSensKind -> Annotation SensitivityK
  PrivacyAnnotation :: (SymTerm MainSensKind, SymTerm MainSensKind) -> Annotation PrivacyK

instance Show (Annotation a) where
  show (PrivacyAnnotation p) = show p
  show (SensitivityAnnotation s) = show s
  
instance ShowPretty (Annotation a) where
    showPretty (SensitivityAnnotation a) = " @ " <> showPretty a
    showPretty (PrivacyAnnotation a) = " @ " <> showPretty a

instance Eq (Annotation a) where
  (SensitivityAnnotation a) == SensitivityAnnotation b = a == b
  (PrivacyAnnotation a) == PrivacyAnnotation b = a == b

instance Monad t => SemigroupM t (Annotation a) where
  (SensitivityAnnotation a) ⋆ (SensitivityAnnotation b) = SensitivityAnnotation <$> (a ⋆ b)
  (PrivacyAnnotation a) ⋆ (PrivacyAnnotation b) = PrivacyAnnotation <$> (a ⋆ b)

instance Monad t => CheckNeutral t (Annotation a) where
  checkNeutral (SensitivityAnnotation s) = checkNeutral s
  checkNeutral (PrivacyAnnotation s) = checkNeutral s

instance Typeable a => MonoidM Identity (Annotation a) where
  neutral = let case1 = testEquality (typeRep @a) (typeRep @SensitivityK)
                case2 = testEquality (typeRep @a) (typeRep @PrivacyK)
            in case (case1, case2) of
                (Just Refl , _) -> pure $ SensitivityAnnotation zeroId
                (_ , Just Refl) -> pure $ PrivacyAnnotation (zeroId, zeroId)
                _ -> undefined

instance Typeable a => CMonoidM Identity (Annotation a) where

--------------------
-- DMKinds
----------
--  Our DMTypes do not only contain the real types of the duet
-- type system, but also norm and clip expressions. To still
-- be able to differentiate between the different kinds of `DMTypes`,
-- We annotate their type with a term of `DMKind`.

-- A `DMKind` is one of the following constructors:
data DMKind =
    MainKind
  | NumKind
  | BaseNumKind
  | IRNumKind
  | ClipKind
  | NormKind
  | FunKind
  | NoFunKind
  | VecKindKind
  | ConstnessKind
  deriving (Typeable)

-- Using the "TemplateHaskell" ghc-extension, and the following function from the singletons library,
-- we generate the `SingI` instances (and related stuff) needed to work with `DMKind` expressions on the type level.
genSingletons [''AnnotationKind]
genSingletons [''DMKind]

-- DMKinds are pretty printed as follows. For this we implement the `Show` typeclass for `DMKind`.
instance Show DMKind where
  show MainKind = "*"
  show NumKind = "Num"
  show BaseNumKind = "BaseNum"
  show IRNumKind = "IRNum"
  show ClipKind = "Clip"
  show NormKind = "Norm"
  show FunKind = "Fun"
  show NoFunKind = "NoFun"
  show VecKindKind = "VecKind"
  show ConstnessKind = "Constness"

-- so we don't get incomplete pattern warnings for them
{-# COMPLETE DMInt, DMReal, IRNum, Num, Const, NonConst, DMData, Numeric, TVar, (:->:), (:->*:), DMTup, L1, L2, LInf, U, Clip, Vector, Gradient, Matrix,
 DMContainer, DMVec, DMGrads, DMMat, DMModel, NoFun, Fun, (:∧:), BlackBox, DMBool #-}

--------------------
-- 2. DMTypes
-------------
-- Now we can define our actual DMTypes.
-- We call the general case of a type of some kind k, `DMTypeOf k`.

-- The specific case of a type of "main" kind, we simply call `DMType`, i.e.:
type DMMain = DMTypeOf MainKind
type DMType = DMTypeOf NoFunKind
type DMFun = DMTypeOf FunKind

-- And we give a similar abbreviation for numeric dmtypes:
type DMNum = DMTypeOf NumKind

-- Abbreviation for veckinds
type VecKind = DMTypeOf VecKindKind

pattern DMVec n c d t = DMContainer Vector n c d t
pattern DMMat n c r d t = DMContainer (Matrix r) n c d t
pattern DMGrads n c d t = DMContainer Gradient n c d t

-- The actual, generic definition of `DMTypeOf` for types of any kind `k` (for `k` in `DMKind`) is given as follows.
-- NOTE: We can write `(k :: DMKind)` here, because we use the `DataKinds` ghc-extension, which allows us to use
-- the terms in `DMKind` in a place where normally haskell types would be expected.
data DMTypeOf (k :: DMKind) where
  -- a "virtual" type of which everything is a subtype
  -- we need this in places where we require stuff to
  -- be subtype of some julia type, and do not need
  -- additional information about possible refinements
  DMAny :: DMTypeOf k

  DMBool :: DMType

  -- the base numeric constructors
  DMInt    :: DMTypeOf IRNumKind
  DMReal   :: DMTypeOf IRNumKind
  DMData   :: DMTypeOf BaseNumKind
  IRNum    :: DMTypeOf IRNumKind -> DMTypeOf BaseNumKind

  -- a base numeric type can be either constant or non constant or data

  Const :: Sensitivity -> DMTypeOf ConstnessKind
  NonConst :: DMTypeOf ConstnessKind

  Num :: DMTypeOf BaseNumKind -> DMTypeOf ConstnessKind -> DMTypeOf NumKind

  -- DMData   :: DMTypeOf NumKind

  -- we include numeric types into main types using this constructor
  Numeric  :: DMTypeOf NumKind -> DMType

  -- type vars can be of any kind (k :: DMKind). But we require the constraint that
  -- k be typeable, because it is needed in cases where we want to compare different k's.
  TVar :: IsKind k => SymbolOf k -> DMTypeOf k

  -- the arrow type
  (:->:) :: [DMTypeOf MainKind :@ Sensitivity] -> DMTypeOf MainKind -> DMFun

  -- the privacy-arrow type
  (:->*:) :: [DMTypeOf MainKind :@ Privacy] -> DMTypeOf MainKind -> DMFun

  -- tuples
  DMTup :: [DMType] -> DMType

   --- matrix norms
  L1 :: DMTypeOf NormKind
  L2 :: DMTypeOf NormKind
  LInf :: DMTypeOf NormKind

  -- embed norms into ClipKind
  U :: DMTypeOf ClipKind
  Clip :: DMTypeOf NormKind -> DMTypeOf ClipKind

  -- veckinds
  Vector :: VecKind
  Gradient :: VecKind
  Matrix :: Sensitivity -> VecKind

  -- matrices
  DMContainer :: VecKind -> (DMTypeOf NormKind) -> (DMTypeOf ClipKind) -> Sensitivity -> DMMain -> DMType
  DMModel :: Sensitivity -> DMType -- number of parameters

  -- annotations
  NoFun :: DMType -> DMTypeOf MainKind
  Fun :: [DMTypeOf FunKind :@ Maybe [JuliaType]] -> DMTypeOf MainKind
  (:∧:) :: DMTypeOf MainKind -> DMTypeOf MainKind -> DMTypeOf MainKind -- infimum

  -- black box functions (and a wrapper to make them MainKind but still have a BlackBoxKind so we can have TVars of it)
  BlackBox :: [JuliaType] -> DMTypeOf MainKind



instance Hashable (DMTypeOf k) where
  hashWithSalt s (DMBool) = s +! 12
  hashWithSalt s (DMInt) = s +! 1
  hashWithSalt s (DMReal) = s +! 2
  hashWithSalt s (DMData) = s +! 3
  hashWithSalt s (L1) = s +! 4
  hashWithSalt s (L2) = s +! 5
  hashWithSalt s (LInf) = s +! 6
  hashWithSalt s (U) = s +! 7
  hashWithSalt s (DMAny) = s +! 8
  hashWithSalt s (Vector) = s +! 9
  hashWithSalt s (Gradient) = s +! 10
  hashWithSalt s (NonConst) = s +! 11
  hashWithSalt s (Const t) = s `hashWithSalt` t
  hashWithSalt s (IRNum t) = s `hashWithSalt` t
  hashWithSalt s (Num t n) = s `hashWithSalt` n `hashWithSalt` t
  hashWithSalt s (Numeric t) = s `hashWithSalt` t
  hashWithSalt s (TVar t) = s `hashWithSalt` t
  hashWithSalt s (n :->: t) = s `hashWithSalt` n `hashWithSalt` t
  hashWithSalt s (n :->*: t) = s `hashWithSalt` n `hashWithSalt` t
  hashWithSalt s (DMTup t) = s `hashWithSalt` t
  hashWithSalt s (Matrix t) = s `hashWithSalt` t
  hashWithSalt s (Clip t) = s `hashWithSalt` t
  hashWithSalt s (DMContainer k n t u v) = s `hashWithSalt` k `hashWithSalt` n `hashWithSalt` t `hashWithSalt` u `hashWithSalt` v
--  hashWithSalt s (DMMat n t u v w) = s `hashWithSalt` n `hashWithSalt` t `hashWithSalt` u `hashWithSalt` v `hashWithSalt` w
  hashWithSalt s (DMModel u) = s `hashWithSalt` u
  hashWithSalt s (Fun t) = s `hashWithSalt` t
  hashWithSalt s (NoFun t) = s `hashWithSalt` t
  hashWithSalt s (n :∧: t) = s `hashWithSalt` n `hashWithSalt` t
  hashWithSalt s (BlackBox n) = s `hashWithSalt` n


instance (Hashable a, Hashable b) => Hashable (a :@ b) where
  hashWithSalt s (a:@ b) = s `hashWithSalt` a `hashWithSalt` b

type DMExtra e = (Typeable e, SingI e)

-- Types are pretty printed as follows.
instance Show (DMTypeOf k) where
  show DMAny = "DMAny"
  show DMBool = "Bool"
  show DMInt = "Integer"
  show DMReal = "Real"
  show DMData = "Data"
  show (IRNum a) = "IR " <> show a
  show (Num t NonConst) = show t
  show (Num t c) = show t <> "[" <> show c <> "]"
  show (NonConst) = "--"
  show (Const c) = show c <> " ©"
  show (Numeric t) = "Num(" <> show t <> ")"
  show (TVar t) = show t
  show (a :->: b) = "(" <> show a <> " -> " <> show b <> ")"
  show (a :->*: b) = "(" <> show a <> " ->* " <> show b <> ")"
  show (DMTup ts) = "Tupl(" <> show ts <> ")"
  show L1 = "L1"
  show L2 = "L2"
  show LInf = "LInf"
  show U = "U"
  show Vector = "Vector"
  show Gradient = "Gradient"
  show (Matrix n) = show n <> "-row Matrix"
  show (Clip n) = "Clip(" <> show n <> ")"
  show (DMVec nrm clp n τ) = "Vector<n: "<> show nrm <> ", c: " <> show clp <> ">[" <> show n <> "](" <> show τ <> ")"
  show (DMMat nrm clp n m τ) = "Matrix<n: "<> show nrm <> ", c: " <> show clp <> ">[" <> show n <> " × " <> show m <> "](" <> show τ <> ")"
  show (DMModel m) = "Model[" <> show m <> "]"
  show (DMGrads nrm clp m τ) = "Grads<n: "<> show nrm <> ", c: " <> show clp <> ">[" <> show m <> "](" <> show τ <> ")"
  show (DMContainer k nrm clp m τ) = "Container("<> show k <> ")<n: "<> show nrm <> ", c: " <> show clp <> ">[" <> show m <> "](" <> show τ <> ")"
  show (NoFun x) = "NoFun(" <> show x <> ")"
  show (Fun xs) = "Fun(" <> show xs <> ")"
  show (x :∧: y) = "(" <> show x <> "∧" <> show y <> ")"
  show (BlackBox n) = "BlackBox [" <> show n <> "]"

appendDifferentIfLastIsLong :: StringLike s => s -> Int -> Int -> s -> s -> s
appendDifferentIfLastIsLong main verticalToSwitch lengthToSwitch shortExtra longExtra =
  let lastLength = case reverse (linesS main) of
                     [] -> 0
                     (l:ls) -> lengthS l
  in case length (linesS main) > verticalToSwitch of
       True  -> main <> longExtra
       False -> case lastLength <= lengthToSwitch of
                  True  -> main <> shortExtra
                  False -> main <> longExtra
                     

showArgPrettyShort :: (ShowPretty a, ShowPretty b) => (a :@ b) -> Text
showArgPrettyShort (a :@ b) = showPretty a <> " @ " <> parenIfMultiple (showPretty b)

showFunPrettyShort :: (ShowPretty a, ShowPretty b) => Text -> [(a :@ b)] -> a -> Text
showFunPrettyShort marker args ret =  "(" <> intercalateS ", " (fmap showArgPrettyShort args) <> ")"
                                      <> " " <> marker <> " " <> (showPretty ret)

showArgPrettyLong :: (ShowPretty a, ShowPretty b) => (a :@ b) -> Text
showArgPrettyLong (a :@ b) =
  let ty = "- " <> indentAfterFirstWith "  " (showPretty a) 
  in appendDifferentIfLastIsLong ty 2 20
       ("@" <> showPretty b <> "\n")
       ("\n"
       <> "    @ " <> showPretty b <> "\n")

showFunPrettyLong :: (ShowPretty a, ShowPretty b) => Text -> [(a :@ b)] -> a -> Text
showFunPrettyLong marker args ret =
  let text = intercalateS "\n" (fmap showArgPrettyLong args)
             <> "--------------------------\n"
             <> " " <> marker <> " " <> (showPretty ret)
  in text

showFunPretty :: (ShowPretty a, ShowPretty b) => Text -> [(a :@ b)] -> a -> Text
showFunPretty marker args ret =
  let shortResult = showFunPrettyShort marker args ret
  in case lengthS shortResult < 40 of
      True  -> shortResult
      False -> showFunPrettyLong marker args ret

showPrettyEnumVertical :: (ShowPretty a) => [a] -> Text
showPrettyEnumVertical = prettyEnumVertical . fmap showPretty

instance ShowPretty (Sensitivity) where
  showPretty s = T.pack $ show s

instance ShowPretty (SymbolOf k) where
  showPretty = T.pack . show

instance (ShowPretty a, ShowPretty b) => ShowPretty (a :@ b) where
  showPretty (a :@ b) = showPretty a <> " @ " <> showPretty b

instance ShowPretty (DMTypeOf k) where
  showPretty DMAny = "Any"
  showPretty DMBool = "Bool"
  showPretty DMInt = "Integer"
  showPretty DMReal = "Real"
  showPretty DMData = "Data"
  showPretty (IRNum a) = showPretty a
  showPretty (Num t c) = let cc = showPretty c
                         in case cc of
                                 "--" -> showPretty t
                                 _    ->showPretty t <> "[" <> cc <> "]"
  showPretty (NonConst) = "--"
  showPretty (Const c) = showPretty c <> " ©"
  showPretty (Numeric t) = showPretty t
  showPretty (TVar t) = showPretty t
  showPretty (a :->: b) = showFunPretty "->" a b
  showPretty (a :->*: b) = showFunPretty "->*" a b
  showPretty (DMTup ts) = "Tuple{" <> T.intercalate "," (showPretty <$> ts) <> "}"
  showPretty L1 = "L1"
  showPretty L2 = "L2"
  showPretty LInf = "LInf"
  showPretty U = "U"
  showPretty Vector = "Vector"
  showPretty Gradient = "DMGrads"
  showPretty (Matrix n) = showPretty n <> "-row Matrix"
  showPretty (Clip n) = showPretty n
  showPretty (DMVec nrm clp n τ) = "Vector<n: "<> showPretty nrm <> ", c: " <> showPretty clp <> ">[" <> showPretty n <> "]{" <> showPretty τ <> "}"
  showPretty (DMMat nrm clp n m τ) = "Matrix<n: "<> showPretty nrm <> ", c: " <> showPretty clp <> ">[" <> showPretty n <> " × " <> showPretty m <> "]{" <> showPretty τ <> "}"
  showPretty (DMModel m) = "DMModel[" <> showPretty m <> "]"
  showPretty (DMGrads nrm clp m τ) = "DMGrads<n: "<> showPretty nrm <> ", c: " <> showPretty clp <> ">[" <> showPretty m <> "]{" <> showPretty τ <> "}"
  showPretty (DMContainer k nrm clp m τ) = "DMContainer<kind: " <> showPretty k <> ", n: "<> showPretty nrm <> ", c: " <> showPretty clp <> ">[" <> showPretty m <> "]{" <> showPretty τ <> "}"
  showPretty (NoFun x) = showPretty x
  showPretty (Fun xs) = showPrettyEnumVertical (fmap fstAnn xs)
  showPretty (x :∧: y) = "(" <> showPretty x <> "∧" <> showPretty y <> ")"
  showPretty (BlackBox n) = "BlackBox<sign: " <> showPretty n <> ">"

instance ShowLocated (DMTypeOf k) where
  showLocated = pure . showPretty

instance Eq (DMTypeOf k) where
  -- special
  TVar a == TVar b = a == b

  -- ClipKind
  U == U = True
  Clip c == Clip d = c == d

  -- NormKind
  L1 == L1 = True
  L2 == L2 = True
  LInf == LInf = True

  -- VecKind
  Vector == Vector = True
  Gradient == Gradient = True
  Matrix r1 == Matrix r2 = r1 == r2

  DMBool == DMBool = True

  -- the base numeric constructors
  DMInt    == DMInt = True
  DMReal   == DMReal = True

  -- a base numeric type can be either constant or non constant or data
  Const s == Const s2 = s == s2
  NonConst == NonConst = True
  DMData   == DMData = True
  Num t1 c1 == Num t2 c2 = and [t1 == t2, c1 == c2]
  IRNum s == IRNum s2 = s == s2

  -- we include numeric types into main types using this constructor
  Numeric t1 == Numeric t2 = t1 == t2

  -- the arrow type
  (xs :->: x) == (ys :->: y) = and [xs == ys, x == y]

  -- the privacy-arrow type
  (xs :->*: x) == (ys :->*: y) = and [xs == ys, x == y]

  -- tuples
  DMTup xs == DMTup ys = xs == ys

  -- matrices
  DMContainer k a b c d == DMContainer k2 a2 b2 c2 d2 = and [k == k2, a == a2, b == b2, c == c2, d == d2]

  -- annotations
  NoFun t == NoFun s = t == s
  Fun ts == Fun ss = ts == ss
  (a :∧: b) == (a2 :∧: b2) = and [a == a2, b == b2]

  (BlackBox n1) == (BlackBox n2) = n1 == n2

  -- Error case
  _ == _ = False


instance Ord (DMTypeOf NormKind) where
  a <= b = (show a) <= (show b)

--------------------
-- 3. Additional Notation
--
-- We sometimes want to pair a type with a sensitivity, just as in the arrow
-- type constructor in DMType. For this we define the type (a :@ b), which is
-- effectively just a tuple (a,b). But this gives us this new notation, and
-- terms (x :@ y) :: (a :@ b) are pretty printed with an "@".

infix 3 :@
data (:@) a b = (:@) a b
  deriving (Generic, Eq)

instance (Show a, Show b) => Show (a :@ b) where
  show (a :@ b) = show a <> " @ " <> show b

instance (Substitute v x a, Substitute v x b) => Substitute v x (a :@ b) where
  substitute σs (a :@ b) = (:@) <$> substitute σs a <*> substitute σs b

-- Since we want to use (monadic-)algebraic operations on terms of type `(a :@ b)`,
-- we declare these instances here. That is, if `a` and `b` have such instances,
-- then (a :@ b) has them as well:

-- (a :@ b) is a monadic semigroup.
instance (SemigroupM t a, SemigroupM t b) => SemigroupM t (a :@ b) where
  (⋆) (a₁ :@ b₁) (a₂ :@ b₂) = (:@) <$> (a₁ ⋆ a₂) <*> (b₁ ⋆ b₂)

-- (a :@ b) is a monadic monoid.
instance (MonoidM t a, MonoidM t b) => MonoidM t (a :@ b) where
  neutral = (:@) <$> neutral <*> neutral

-- (a :@ b) is a monadic monoid in which an explicit equality check with the neutral element
-- is possible.
instance (CheckNeutral m a, CheckNeutral m b) => CheckNeutral m (a :@ b) where
  checkNeutral (a :@ b) = (\a b -> and [a,b]) <$> checkNeutral a <*> checkNeutral b

-- NOTE: The monoidal operation for sensitivities is addition.
--       The operation for DMTypes is unification.
--       That means, given `(x :@ s), (y :@ t) :: (DMType :@ Sensitivity)`,
--       computing `(x :@ s) ⋆ (y :@ t)` unifies `x` and `y`, and sums `s` and `t`.
--       The result lives in a monad.

fstAnn :: (a :@ b) -> a
fstAnn (a :@ b) = a

sndAnn :: (a :@ b) -> b
sndAnn (a :@ b) = b


-------------
-- Recursion into DMTypes
--
recDMTypeM :: forall m k. (Monad m)
           => (forall k. DMTypeOf k -> m (DMTypeOf k)) 
           -> (Sensitivity -> m (Sensitivity)) 
           -> DMTypeOf k -> m (DMTypeOf k)
recDMTypeM typemap sensmap DMAny = pure DMAny
recDMTypeM typemap sensmap L1 = pure L1
recDMTypeM typemap sensmap L2 = pure L2
recDMTypeM typemap sensmap LInf = pure LInf
recDMTypeM typemap sensmap U = pure U
recDMTypeM typemap sensmap Vector = pure Vector
recDMTypeM typemap sensmap Gradient = pure Gradient
recDMTypeM typemap sensmap (Matrix n) = Matrix <$> sensmap n
recDMTypeM typemap sensmap (Clip n) = Clip <$> typemap n
recDMTypeM typemap sensmap DMBool = pure DMBool
recDMTypeM typemap sensmap DMInt = pure DMInt
recDMTypeM typemap sensmap DMReal = pure DMReal
recDMTypeM typemap sensmap DMData = pure DMData
recDMTypeM typemap sensmap (IRNum τ) = IRNum <$> typemap τ
recDMTypeM typemap sensmap (Numeric τ) = Numeric <$> typemap τ
recDMTypeM typemap sensmap (NonConst) = pure NonConst
recDMTypeM typemap sensmap (Const t) = Const <$> sensmap t
recDMTypeM typemap sensmap (Num τ c) = Num <$> (typemap τ) <*> typemap c
recDMTypeM typemap sensmap (TVar x) = pure (TVar x)
recDMTypeM typemap sensmap (τ1 :->: τ2) = (:->:) <$> mapM (\(a :@ b) -> (:@) <$> typemap a <*> sensmap b) τ1 <*> typemap τ2
recDMTypeM typemap sensmap (τ1 :->*: τ2) = (:->*:) <$> mapM (\(a :@ (b0, b1)) -> f <$> typemap a <*> sensmap b0 <*> sensmap b1) τ1 <*> typemap τ2
  where
    f a b0 b1 = a :@ (b0, b1)
recDMTypeM typemap sensmap (DMTup τs) = DMTup <$> mapM typemap τs
recDMTypeM typemap sensmap (DMContainer k nrm clp n τ) = DMContainer <$> typemap k <*> typemap nrm <*> typemap clp <*> sensmap n <*> typemap τ
recDMTypeM typemap sensmap (DMModel m) = DMModel <$> sensmap m
recDMTypeM typemap sensmap (NoFun x) = NoFun <$> typemap x
recDMTypeM typemap sensmap (Fun xs) = Fun <$> mapM (\(a :@ b) -> (:@) <$> typemap a <*> pure b) xs
recDMTypeM typemap sensmap (x :∧: y) = (:∧:) <$> typemap x <*> typemap y
recDMTypeM typemap sensmap (BlackBox n) = pure (BlackBox n)

---------------------------------------------------------
-- Sensitivity and Privacy
--
-- The actual definition of sensitivity terms is in Core.Symbolic.
-- Here we only give it a different name .

-- In order to fit the same type classes (in particular Term, and MonadTerm from Abstract.Class),
-- sensitivities are also annotated with (k :: SensKind). Even though this type only contains a single
-- kind (MainSensKind :: SensKind). But because of this we also have a kinded, and an abbreviated definition:
type SensitivityOf = SymTerm
type Sensitivity = SymTerm MainSensKind

-- Privacies are defined similarly.
-- NOTE: Since they are currently not used anywhere, this definition is not battle tested.
--       We might want to define them slightly differently, for example using a newtype.
--       On the other hand, this seems to be the most sensible option currently, with the least syntactic overhead.
type PrivacyOf a = (SensitivityOf a,SensitivityOf a)
type Privacy = PrivacyOf MainSensKind


-- the special infinity values
--
inftyS :: Sensitivity
inftyS = constCoeff Infty
--
inftyP :: Privacy
inftyP = (constCoeff Infty, constCoeff Infty)
---------------------------------------------------------
-- Julia types
-- 
-- An almost one-to-one representation of all supported julia types, with the exception of JTBot which does not
-- exist in julia and is set to be a julia-subtype of all other JuliaTypes as defined in Typecheck/JuliaTypes.jl

data JuliaType =
    JTAny
    | JTBot
    | JTBool
    | JTInt
    | JTReal
    | JTData
    | JTFunction
    | JTPFunction
    | JTTuple [JuliaType]
    | JTVector JuliaType
    | JTMatrix JuliaType
    | JTMetricVector JuliaType (DMTypeOf NormKind)
    | JTMetricMatrix JuliaType (DMTypeOf NormKind)
    | JTMetricGradient JuliaType (DMTypeOf NormKind)
    | JTModel
    | JTGrads
  deriving (Generic, Eq, Ord)

instance Hashable JuliaType where
instance DictKey JuliaType

instance Monad t => Normalize t JuliaType where
  normalize nt = pure

-- this is used for callbacks to actual julia, so the string representation matches julia exactly.
instance Show JuliaType where
  show JTAny = "Any"
  show JTBool = "Bool"
  show JTInt = "Integer"
  show JTReal = "Real"
  show JTData = "Data"
  show JTFunction = "Function"
  show JTPFunction = "PrivacyFunction"
  show (JTTuple as) = "Tuple{" ++ (intercalate "," (show <$> as)) ++ "}"
  show (JTVector t) = "Vector{<:" ++ show t ++ "}"
  show (JTMatrix t) = "Matrix{<:" ++ show t ++ "}"
  show (JTMetricVector t nrm) = "MetricVector(" ++ show t ++ "," ++ show nrm ++ ")"
  show (JTMetricMatrix t nrm) = "MetricMatrix(" ++ show t ++ "," ++ show nrm ++ ")"
  show (JTMetricGradient t nrm) = "MetricGradient(" ++ show t ++ "," ++ show nrm ++ ")"
  show (JTModel) = "DMModel"
  show (JTGrads) = "DMGrads"
  show (JTBot) = "Union{}"

instance ShowLocated JuliaType where
  showLocated = pure . T.pack . show

--------------------------------------------------------------------------
-- Type Operations
-- It is often the case that we cannot say what type a simple operation
-- such as `a + b` will have, since this depends on the types of `a` and `b`,
-- which apriori seldom are going to be known.
-- Thus we introduce 'type operations' encoding these unknown types,
-- If `a : A` and `b : B`, then `a + b : Binary(DMOpAdd(), A, B)`.
-- Further along while typechecking, we will compute the actual value of that type.

-- The type of all possible unary type operations.
data DMTypeOps_Unary =
   DMOpCeil
  deriving (Generic, Eq, Ord)

-- The type of all possible binary type operations.
data DMTypeOps_Binary =
   DMOpAdd
   | DMOpSub
   | DMOpMul
   | DMOpDiv
   | DMOpMod
   | DMOpEq
  deriving (Generic, Eq, Ord)


data DMTypeOp_Some = IsUnary DMTypeOps_Unary | IsBinary DMTypeOps_Binary
  deriving (Show, Generic, Eq, Ord)

instance Show DMTypeOps_Unary where
  show DMOpCeil = "ceil"

instance Show DMTypeOps_Binary where
  show DMOpAdd = "+"
  show DMOpSub = "-"
  show DMOpMul = "*"
  show DMOpDiv = "/"
  show DMOpMod = "%"
  show DMOpEq = "=="

-- An application of a type operation to an appropriate number of type arguments
data DMTypeOp =
     Unary DMTypeOps_Unary   (DMType :@ SVar) (DMType)
   | Binary DMTypeOps_Binary (DMType :@ SVar , DMType :@ SVar) (DMType)
  deriving (Show, Eq)

instance ShowPretty DMTypeOp where
    showPretty (Unary op t s) = "Unary operation " <> T.pack (show op) <> " on " <> showPretty t <> " with result type " <> showPretty s
    showPretty (Binary op t s) = "Binary operation " <> T.pack (show op) <> " on " <> showPretty t <> " with result type " <> showPretty s

instance ShowLocated DMTypeOp_Some where
  showLocated (IsUnary a) = pure $ T.pack $ show a
  showLocated (IsBinary a) = pure $ T.pack $ show a


--------------------------------------------------------------------------
-- DMTerms
--

type NormTerm = DMTypeOf NormKind

data Asgmt a = (:-) TeVar a
  deriving (Generic, Show, Eq, Ord)

fstA :: Asgmt a -> TeVar
fstA (x :- τ) = x

sndA :: Asgmt a -> a
sndA (x :- τ) = τ

data LetKind = PureLet | BindLet | SampleLet
  deriving (Eq, Show)

data BBKind (t :: * -> *) = BBSimple JuliaType | BBVecLike JuliaType (LocPreDMTerm t) | BBMatrix JuliaType (LocPreDMTerm t) (LocPreDMTerm t)

deriving instance (forall a. Show a => Show (t a)) => Show (BBKind t)
deriving instance (forall a. Eq a => Eq (t a)) => Eq (BBKind t)

type LocPreDMTerm t = Located (PreDMTerm t)

data PreDMTerm (t :: * -> *) =
    Extra (t (LocPreDMTerm t))
  | Ret ((LocPreDMTerm t))
  | Sng Float JuliaType
  | DMTrue
  | DMFalse
  | Var TeVar
  | Disc (LocPreDMTerm t)
  | Undisc (LocPreDMTerm t)
  | Arg TeVar JuliaType Relevance
  | Op DMTypeOp_Some [(LocPreDMTerm t)]
  | Phi (LocPreDMTerm t) (LocPreDMTerm t) (LocPreDMTerm t)
  | Lam     [Asgmt (JuliaType, Relevance)] JuliaType (LocPreDMTerm t)
  | LamStar [(Asgmt (JuliaType, Relevance))] JuliaType (LocPreDMTerm t)
  | BBLet TeVar [JuliaType] (LocPreDMTerm t) -- name, arguments, tail
  | BBApply (LocPreDMTerm t) [(LocPreDMTerm t)] [TeVar] (BBKind t) -- term containing the application, list of captured variables, return type.
  | Apply (LocPreDMTerm t) [(LocPreDMTerm t)]
  | FLet TeVar (LocPreDMTerm t) (LocPreDMTerm t)
  | Choice (HashMap [JuliaType] (LocPreDMTerm t))
  | SLetBase LetKind TeVar (LocPreDMTerm t) (LocPreDMTerm t)
  | Tup [(LocPreDMTerm t)]
  | TLetBase LetKind [TeVar] (LocPreDMTerm t) (LocPreDMTerm t)
  | Gauss (LocPreDMTerm t) (LocPreDMTerm t) (LocPreDMTerm t) (LocPreDMTerm t)
  | Laplace (LocPreDMTerm t) (LocPreDMTerm t) (LocPreDMTerm t)
  | Exponential (LocPreDMTerm t) (LocPreDMTerm t) (LocPreDMTerm t) (LocPreDMTerm t)
  | AboveThresh (LocPreDMTerm t) (LocPreDMTerm t) (LocPreDMTerm t) (LocPreDMTerm t)
  | MutGauss (LocPreDMTerm t) (LocPreDMTerm t) (LocPreDMTerm t) (LocPreDMTerm t)
  | MutLaplace (LocPreDMTerm t) (LocPreDMTerm t) (LocPreDMTerm t)
-- matrix related things
  | MakeVec (LocPreDMTerm t)
  | MakeRow (LocPreDMTerm t)
  | MapRows (LocPreDMTerm t) (LocPreDMTerm t)
  | MapCols (LocPreDMTerm t) (LocPreDMTerm t)
  | MapCols2 (LocPreDMTerm t) (LocPreDMTerm t) (LocPreDMTerm t)
  | MapRows2 (LocPreDMTerm t) (LocPreDMTerm t) (LocPreDMTerm t)
  | PFoldRows (LocPreDMTerm t) (LocPreDMTerm t) (LocPreDMTerm t) (LocPreDMTerm t)
  | PReduceCols (LocPreDMTerm t) (LocPreDMTerm t)
  | MFold (LocPreDMTerm t) (LocPreDMTerm t) (LocPreDMTerm t)
  | Count (LocPreDMTerm t) (LocPreDMTerm t)
  | MMap (LocPreDMTerm t) (LocPreDMTerm t)
  | MutConvertM NormTerm (LocPreDMTerm t)
  | ConvertM NormTerm (LocPreDMTerm t)
  | MutUndiscM (LocPreDMTerm t)
  | UndiscM (LocPreDMTerm t)
  | MCreate (LocPreDMTerm t) (LocPreDMTerm t) (TeVar, TeVar) (LocPreDMTerm t)
  | Transpose (LocPreDMTerm t)
  | Size (LocPreDMTerm t) -- matrix dimensions, returns a tuple of two numbers
  | Length (LocPreDMTerm t) -- vector dimension, returns a number
  | Index (LocPreDMTerm t) (LocPreDMTerm t) (LocPreDMTerm t) -- matrix index
  | VIndex (LocPreDMTerm t) (LocPreDMTerm t) -- vector index
  | Row (LocPreDMTerm t) (LocPreDMTerm t) -- matrix row
  | ClipM NormTerm (LocPreDMTerm t)
  | ClipN (LocPreDMTerm t) (LocPreDMTerm t) (LocPreDMTerm t)
  | MutClipM NormTerm (LocPreDMTerm t)
  | Loop ((LocPreDMTerm t), (LocPreDMTerm t), (LocPreDMTerm t)) [TeVar] (TeVar, TeVar) (LocPreDMTerm t)
-- Special NN builtins
  | MutSubGrad (LocPreDMTerm t) (LocPreDMTerm t)
  | SubGrad (LocPreDMTerm t) (LocPreDMTerm t)
  | ScaleGrad (LocPreDMTerm t) (LocPreDMTerm t) -- scale (a : Scalar) (g : Mutating Gradient)
-- Special Tuple terms
  | TProject Int (LocPreDMTerm t)
  | ZeroGrad (LocPreDMTerm t)
  | SumGrads (LocPreDMTerm t) (LocPreDMTerm t)
  | Sample (LocPreDMTerm t) (LocPreDMTerm t) (LocPreDMTerm t)
-- Internal terms
  | InternalExpectConst (LocPreDMTerm t)
  | InternalMutate (LocPreDMTerm t)
-- Demutation related, but user specified
  | Clone (LocPreDMTerm t)
  deriving (Generic)

pattern SLet a b c = SLetBase PureLet a b c
pattern SBind a b c = SLetBase BindLet a b c
pattern TLet a b c = TLetBase PureLet a b c
pattern TBind a b c = TLetBase BindLet a b c
pattern SmpLet a b c = TLetBase SampleLet a b c

{-# COMPLETE Extra, Ret, DMTrue, DMFalse, Sng, Var, Arg, Op, Phi, Lam, LamStar, BBLet, BBApply, Disc,
 Apply, FLet, Choice, SLet, SBind, Tup, TLet, TBind, Gauss, Laplace, Exponential, MutGauss, MutLaplace, AboveThresh, Count, MMap, MapRows, MapCols, MapCols2, MapRows2, PReduceCols, PFoldRows, MFold, MutConvertM, ConvertM, MCreate, Transpose, UndiscM, MutUndiscM, Undisc,
 Size, Length, Index, VIndex, Row, ClipN, ClipM, MutClipM, Loop, SubGrad, MutSubGrad, ScaleGrad, TProject, ZeroGrad, SumGrads, SmpLet,
 Sample, InternalExpectConst, InternalMutate #-}

deriving instance (forall a. Show a => Show (t a)) => Show (PreDMTerm t)
deriving instance (forall a. Eq a => Eq (t a)) => Eq (PreDMTerm t)

instance Monad m => Normalize m (PreDMTerm t) where
  normalize e x = pure x


--------------------------------------------------------------------------
-- Extensions

-----
-- empty extension
data EmptyExtension a where
 deriving (Functor, Foldable, Traversable)

instance Show (EmptyExtension a) where
  show a = undefined

instance Eq (EmptyExtension a) where
  _ == _ = True

type DMTerm = PreDMTerm EmptyExtension


data ProcAsgmt a = (::-) (ProcVar) a
  deriving (Generic, Show, Eq, Ord)

type LocDMTerm = LocPreDMTerm EmptyExtension
type ProcDMTerm = PreDMTerm ProceduralExtension
type LocProcDMTerm = LocPreDMTerm ProceduralExtension


data ProceduralExtension a =
  ProcTLetBase LetKind [(ProcVar)] a
  | ProcSLetBase LetKind (ProcVar) a
  | ProcFLet ProcVar a
  | ProcBBLet ProcVar [JuliaType] -- name, arguments
  | ProcBBApply a [a] (BBKind ProceduralExtension)
  | ProcPhi a a (Maybe a)
  | ProcPreLoop (a,a,a) (ProcVar) a
  | ProcReturn
  | ProcVarTerm (ProcVar)
  | ProcLam     [ProcAsgmt (JuliaType, Relevance)] JuliaType a
  | ProcLamStar [(ProcAsgmt (JuliaType, Relevance))] JuliaType a
  | Block [a]
  deriving (Show, Eq, Functor, Foldable, Traversable)


type DemutDMTerm = PreDMTerm DemutatedExtension
type LocDemutDMTerm = LocPreDMTerm DemutatedExtension

data DemutatedExtension a =
  DemutTLetBase LetKind [(TeVar)] a
  | DemutSLetBase LetKind (TeVar) a
  | DemutFLet TeVar a
  | DemutBBLet TeVar [JuliaType] -- name, arguments
  | DemutPhi a a a
  | DemutLoop (a,a,a) [TeVar] [TeVar] (TeVar, TeVar) a -- number of iters, captures before, captures after, iter-var, capture-var
  | DemutBlock [a]
  deriving (Show, Eq, Functor, Foldable, Traversable)

----
-- sum of extensions
data SumExtension e f a = SELeft (e a) | SERight (f a)
  deriving (Show, Eq, Functor, Foldable, Traversable)

----
-- functions

liftExtension_Loc :: (Located (t (LocPreDMTerm t)) -> LocPreDMTerm s) -> LocPreDMTerm t -> LocPreDMTerm s
liftExtension_Loc f x = runIdentity $ recDMTermM_Loc (Identity . liftExtension_Loc f) (Identity . f) (x)

recDMTermSameExtension_Loc :: forall t. (Traversable t) => (LocPreDMTerm t -> (LocPreDMTerm t)) -> LocPreDMTerm t -> (LocPreDMTerm t)
recDMTermSameExtension_Loc f x = runIdentity (recDMTermMSameExtension_Loc (Identity . f) x)

recDMTermMSameExtension_Loc :: forall t m. (Monad m, Traversable t) => (LocPreDMTerm t -> m (LocPreDMTerm t)) -> LocPreDMTerm t -> m (LocPreDMTerm t)
recDMTermMSameExtension_Loc f t = recDMTermM_Loc f g t
  where
    g :: Located (t (LocPreDMTerm t)) -> m (LocPreDMTerm t)
    g (Located l x) =
      let x' :: t (m (LocPreDMTerm t))
          x' = fmap (recDMTermMSameExtension_Loc f) x
          x'' :: m (t (LocPreDMTerm t))
          x'' = sequence x'
      in Located l <$> fmap Extra x''

recKindM :: forall t m s. (Monad m) => (LocPreDMTerm t -> m (LocPreDMTerm s)) -> BBKind t -> m (BBKind s)
recKindM f = \case
  BBSimple jt -> return $ BBSimple jt
  BBVecLike jt pdt -> BBVecLike jt <$> f pdt
  BBMatrix jt pdt pdt' -> BBMatrix jt <$> f pdt <*> f pdt'

recDMTermM_Loc :: forall t m s. (Monad m) => (LocPreDMTerm t -> m (LocPreDMTerm s)) -> (Located (t (LocPreDMTerm t)) -> m (LocPreDMTerm s)) -> LocPreDMTerm t -> m (LocPreDMTerm s)
recDMTermM_Loc f h (Located l (Extra e))         = h (Located l e)
recDMTermM_Loc f h (rest)            = mapM (recDMTermM_Loc_Impl f h) rest -- h e
  where
    recDMTermM_Loc_Impl f h (Disc (r))         = Disc <$> (f r)
    recDMTermM_Loc_Impl f h (Extra e)          = undefined -- impossible "This DMTerm recursion case should already be handled."
    recDMTermM_Loc_Impl f h (Ret r)            = Ret <$> (f r)
    recDMTermM_Loc_Impl f h (Sng g jt)         = pure $ Sng g jt
    recDMTermM_Loc_Impl f h DMTrue             = pure $ DMTrue
    recDMTermM_Loc_Impl f h DMFalse            = pure $ DMFalse
    recDMTermM_Loc_Impl f h (Var v)            = pure $ Var v
    recDMTermM_Loc_Impl f h (Arg v jt r)       = pure $ Arg v jt r
    recDMTermM_Loc_Impl f h (Op op ts)         = Op op <$> (mapM (f) ts)
    recDMTermM_Loc_Impl f h (Phi a b c)        = Phi <$> (f a) <*> (f b) <*> (f c)
    recDMTermM_Loc_Impl f h (Lam     jts jt a)    = Lam jts jt <$> (f a)
    recDMTermM_Loc_Impl f h (LamStar jts jt a)    = LamStar jts jt <$> (f a)
    recDMTermM_Loc_Impl f h (BBLet n jts b)    = (BBLet n jts <$> f b)
    recDMTermM_Loc_Impl f h (BBApply a as bs k)  = BBApply <$> (f a) <*> (mapM (f) as) <*> pure bs <*> recKindM f k
    recDMTermM_Loc_Impl f h (Apply a bs)       = Apply <$> (f a) <*> (mapM (f) bs)
    recDMTermM_Loc_Impl f h (FLet v a b)       = FLet v <$> (f a) <*> (f b)
    recDMTermM_Loc_Impl f h (Choice chs)       = Choice <$> (mapM (f) chs)
    recDMTermM_Loc_Impl f h (SLetBase x jt a b) = SLetBase x jt <$> (f a) <*> (f b)
    recDMTermM_Loc_Impl f h (Tup as)           = Tup <$> (mapM (f) as)
    recDMTermM_Loc_Impl f h (TLetBase x jt a b) = TLetBase x jt <$> (f a) <*> (f b)
    recDMTermM_Loc_Impl f h (Gauss a b c d)    = Gauss <$> (f a) <*> (f b) <*> (f c) <*> (f d)
    recDMTermM_Loc_Impl f h (AboveThresh a b c d)    = AboveThresh <$> (f a) <*> (f b) <*> (f c) <*> (f d)
    recDMTermM_Loc_Impl f h (Laplace a b c)    = Laplace <$> (f a) <*> (f b) <*> (f c)
    recDMTermM_Loc_Impl f h (MutGauss a b c d) = MutGauss <$> (f a) <*> (f b) <*> (f c) <*> (f d)
    recDMTermM_Loc_Impl f h (MutLaplace a b c) = MutLaplace <$> (f a) <*> (f b) <*> (f c)
    recDMTermM_Loc_Impl f h (Exponential a b c d) = Exponential <$> (f a) <*> (f b) <*> (f c) <*> (f d)
    recDMTermM_Loc_Impl f h (Count a b)         = Count <$> (f a) <*> (f b)
    recDMTermM_Loc_Impl f h (MakeVec a)         = MakeVec <$> (f a)
    recDMTermM_Loc_Impl f h (MakeRow a)         = MakeRow <$> (f a)
    recDMTermM_Loc_Impl f h (MMap a b)         = MMap <$> (f a) <*> (f b)
    recDMTermM_Loc_Impl f h (MapRows a b)     = MapRows <$> (f a) <*> (f b)
    recDMTermM_Loc_Impl f h (MapCols a b)     = MapCols <$> (f a) <*> (f b)
    recDMTermM_Loc_Impl f h (MapCols2 a b c)   = MapCols2 <$> (f a) <*> (f b) <*> (f c)
    recDMTermM_Loc_Impl f h (MapRows2 a b c)   = MapRows2 <$> (f a) <*> (f b) <*> (f c)
    recDMTermM_Loc_Impl f h (PFoldRows a b c d)   = PFoldRows <$> (f a) <*> (f b) <*> (f c) <*> (f d)
    recDMTermM_Loc_Impl f h (PReduceCols a b)  = PReduceCols <$> (f a) <*> (f b)
    recDMTermM_Loc_Impl f h (MFold a b c)      = MFold <$> (f a) <*> (f b) <*> (f c)
    recDMTermM_Loc_Impl f h (MutConvertM a b)  = MutConvertM a <$> (f b)
    recDMTermM_Loc_Impl f h (ConvertM a b)     = ConvertM a <$> (f b)
    recDMTermM_Loc_Impl f h (MutUndiscM a)     = MutUndiscM <$> (f a)
    recDMTermM_Loc_Impl f h (UndiscM a)        = UndiscM <$> (f a)
    recDMTermM_Loc_Impl f h (Undisc a)         = Undisc <$> (f a)
    recDMTermM_Loc_Impl f h (MCreate a b x c ) = MCreate <$> (f a) <*> (f b) <*> pure x <*> (f c)
    recDMTermM_Loc_Impl f h (Transpose a)      = Transpose <$> (f a)
    recDMTermM_Loc_Impl f h (Size a)           = Size <$> (f a)
    recDMTermM_Loc_Impl f h (Length a)         = Length <$> (f a)
    recDMTermM_Loc_Impl f h (Index a b c)      = Index <$> (f a) <*> (f b) <*> (f c)
    recDMTermM_Loc_Impl f h (VIndex a b)       = VIndex <$> (f a) <*> (f b)
    recDMTermM_Loc_Impl f h (Row a b)          = Row <$> (f a) <*> (f b)
    recDMTermM_Loc_Impl f h (ClipN a b c)      = ClipN <$> (f a) <*> (f b) <*> (f c)
    recDMTermM_Loc_Impl f h (ClipM c a)        = ClipM c <$> (f a)
    recDMTermM_Loc_Impl f h (MutClipM c a)     = MutClipM c <$> (f a)
    recDMTermM_Loc_Impl f h (Loop (a1,a2,a3) b x d )  = Loop <$> ((,,) <$> (f a1) <*> (f a2) <*> (f a3)) <*> pure b <*> pure x <*> (f d)
    recDMTermM_Loc_Impl f h (SubGrad a b)      = SubGrad <$> (f a) <*> (f b)
    recDMTermM_Loc_Impl f h (MutSubGrad a b)      = MutSubGrad <$> (f a) <*> (f b)
    recDMTermM_Loc_Impl f h (ScaleGrad a b)    = ScaleGrad <$> (f a) <*> (f b)
    recDMTermM_Loc_Impl f h (TProject x a)     = TProject x <$> f a
    recDMTermM_Loc_Impl f h (ZeroGrad a)       = ZeroGrad <$> (f a)
    recDMTermM_Loc_Impl f h (SumGrads a b)     = SumGrads <$> (f a) <*> (f b)
    recDMTermM_Loc_Impl f h (Sample a b c)     = Sample <$> (f a) <*> (f b) <*> (f c)
    recDMTermM_Loc_Impl f h (Clone t) = Clone <$> (f t)
    recDMTermM_Loc_Impl f h (InternalExpectConst a) = InternalExpectConst <$> (f a)
    recDMTermM_Loc_Impl f h (InternalMutate a) = InternalMutate <$> (f a)

--------------------------------------------------------------------------
-- Free variables for terms

freeVarsOfProcDMTerm_Loc :: LocProcDMTerm -> [ProcVar]
freeVarsOfProcDMTerm_Loc = freeVarsOfProcDMTerm . getLocated


freeVarsOfProcDMTerm :: ProcDMTerm -> [ProcVar]
freeVarsOfProcDMTerm (Extra (ProcVarTerm v)) = [v]
freeVarsOfProcDMTerm (Extra (ProcLam jts _ body)) = freeVarsOfProcDMTerm_Loc body \\ [v | (v ::- _) <- jts]
freeVarsOfProcDMTerm (Extra (ProcLamStar jts _ body)) = freeVarsOfProcDMTerm_Loc body \\ [v | (v ::- _) <- jts]
freeVarsOfProcDMTerm t = fst $ recDMTermMSameExtension_Loc f (Located UnknownLoc t)
  where
    f :: LocProcDMTerm -> ([ProcVar] , LocProcDMTerm)
    f = (\a -> (freeVarsOfProcDMTerm_Loc a, a))

--------------------------------------------------------------------------
-- pretty printing for terms

instance ShowPretty a => ShowPretty [a] where
  showPretty as = "[" <> intercalateS ", " (fmap showPretty as) <> "]"

instance (Show a, Show b) => ShowPretty (HashMap a b) where
    showPretty = T.pack . show

instance ShowPretty a => ShowPretty (Maybe a) where
      showPretty (Just v) = "Just " <> (showPretty v)
      showPretty Nothing = "Nothing"

instance ShowPretty a => ShowPretty (Asgmt a) where
  showPretty (a :- x) = showPretty a <> " :- " <> showPretty x

instance ShowPretty a => ShowPretty (ProcAsgmt a) where
  showPretty (a ::- x) = showPretty a <> " :- " <> showPretty x

instance ShowPretty (DMTypeOp_Some) where
  showPretty (IsBinary op) = T.pack $ show op
  showPretty (IsUnary op) = T.pack $ show op

instance ShowPretty (JuliaType) where
  showPretty = T.pack . show

instance (ShowPretty a, ShowPretty b, ShowPretty c) => ShowPretty (a,b,c) where
  showPretty (a,b,c) = "("<> showPretty a <> ", " <> showPretty b <> ", " <> showPretty c <> ")"

instance (ShowPretty a, ShowPretty b, ShowPretty c, ShowPretty d) => ShowPretty (a,b,c,d) where
  showPretty (a,b,c,d) = "("<> showPretty a <> ", " <> showPretty b <> ", " <> showPretty c <> ", " <> showPretty d <> ")"

instance ShowPretty Relevance where
  showPretty = T.pack . show

instance ShowPretty a => ShowPretty (Located a) where
  showPretty (Located l a) = showPretty a


showVar = showT

instance (forall a. ShowPretty a => ShowPretty (t a)) => ShowPretty (PreDMTerm t) where
  showPretty (Extra e)          = showPretty e
  showPretty (Ret (r))          = "Ret (" <>  showPretty r <> ")"
  showPretty (Disc (r))          = "Disc (" <>  showPretty r <> ")"
  showPretty (DMFalse)          = "DMFalse"
  showPretty (DMTrue)           = "DMTrue"
  showPretty (Sng g jt)         = T.pack $ show g
  showPretty (Var v)            = showVar v
  showPretty (Arg v jt r)       = showPretty v
  showPretty (Op op [t1])       = showPretty op <> " " <> parenIfMultiple (showPretty t1)
  showPretty (Op op [t1,t2])    = parenIfMultiple (showPretty t1)
                                  <> " " <> showPretty op <> " "
                                  <> parenIfMultiple (showPretty t2)
  showPretty (Op op ts)         = showPretty op <> " " <> showPretty ts
  showPretty (Phi a b c)        = "Phi (" <> showPretty a <> ")" <> parenIndent (showPretty b) <> parenIndent (showPretty c)
  showPretty (Lam     jts ret a) = "Lam (" <> showPretty jts <> " -> " <> showPretty ret <> ")" <> parenIndent (showPretty a)
  showPretty (LamStar jts ret a) = "LamStar (" <> showPretty jts <> " -> " <> showPretty ret <> ")" <> parenIndent (showPretty a)
  showPretty (BBLet n jts b)    = "BBLet " <> showPretty n <> " = (" <> showPretty jts <> " -> ?)\n" <> showPretty b
  showPretty (BBApply t as cs k)  = "BBApply (" <> showPretty t <> ")[" <> showPretty cs <> "](" <> showPretty as <> ") -> " <> showPretty k
  showPretty (Apply a bs)       = (showPretty a) <> (showPretty bs)
  showPretty (FLet v a b)       = "FLet " <> showVar v <> " = " <> newlineIndentIfLong (showPretty a) <> "\n" <> (showPretty b)
  showPretty (Choice chs)       = "Choice <..>"
  showPretty (SLet v a b)       = "SLet " <> showVar v <> " = " <> newlineIndentIfLong (showPretty a) <> "\n" <> (showPretty b)
  showPretty (Tup as)           = "Tup " <> (showPretty as)
  showPretty (TLet v a b)       = "TLet " <> showVar v <> " = " <> newlineIndentIfLong (showPretty a) <> "\n" <> (showPretty b)
  showPretty (TBind v a b)      = "TBind " <> showVar v <> " <- " <> newlineIndentIfLong (showPretty a) <> "\n" <> (showPretty b)
  showPretty (Gauss a b c d)    = "Gauss (" <> (showPretty a) <> ", " <> (showPretty b) <> ", " <> (showPretty c) <> ", " <> (showPretty d) <> ")"
  showPretty (AboveThresh a b c d) = "AboveThresh (" <> (showPretty a) <> ", " <> (showPretty b) <> ", " <> (showPretty c) <> ", " <> (showPretty d) <> ")"
  showPretty (MutLaplace a b c) = "MutLaplace (" <> (showPretty a) <> ", " <> (showPretty b) <> ", " <> (showPretty c) <> ")"
  showPretty (MutGauss a b c d) = "MutGauss (" <> (showPretty a) <> ", " <> (showPretty b) <> ", " <> (showPretty c) <> ", " <> (showPretty d) <> ")"
  showPretty (Laplace a b c)    = "Laplace (" <> (showPretty a) <> ", " <> (showPretty b) <> ", " <> (showPretty c) <> ")"
  showPretty (Exponential a b c d) = "Exponential (" <> (showPretty a) <> ", " <> (showPretty b) <> ", " <> (showPretty c) <> ", " <> (showPretty d) <> ")"
  showPretty (Count a b)         = "Count (" <> (showPretty a) <> " to " <> (showPretty b)  <> ")"
  showPretty (MakeVec a)         = "MakeVec (" <> (showPretty a) <> ")"
  showPretty (MakeRow a)         = "MakeRow (" <> (showPretty a) <> ")"
  showPretty (MMap a b)         = "MMap (" <> (showPretty a) <> " to " <> (showPretty b)  <> ")"
  showPretty (MapRows a b)     = "MapRows (" <> (showPretty a) <> " to " <> (showPretty b)  <> ")"
  showPretty (MapCols a b)     = "MapCols (" <> (showPretty a) <> " to " <> (showPretty b)  <> ")"
  showPretty (MapCols2 a b c)   = "MapCols2 (" <> (showPretty a) <> " to " <> (showPretty b) <> ", " <> (showPretty c)  <> ")"
  showPretty (MapRows2 a b c)   = "MapRows2 (" <> (showPretty a) <> " to " <> (showPretty b) <> ", " <> (showPretty c)  <> ")"
  showPretty (PFoldRows a b c d)   = "PFoldRows (" <> (showPretty a) <> " to " <> (showPretty b) <> ", " <> (showPretty c) <> ", " <> (showPretty d)  <> ")"
  showPretty (PReduceCols a b)  = "PReduceCols (" <> (showPretty a) <> " to " <> (showPretty b)  <> ")"
  showPretty (MFold a b c)      = "MFold (" <> (showPretty a) <> ", " <> (showPretty b) <> ", " <> (showPretty c) <> ")"
  showPretty (MutUndiscM a)     = "MutUndiscM (" <> (showPretty a) <> ")"
  showPretty (UndiscM a)        = "UndiscM (" <> (showPretty a) <> ")"
  showPretty (Undisc a)         = "Undisc (" <> (showPretty a) <> ")"
  showPretty (MutConvertM a b)  = "MutConvertM (" <> (showPretty a) <> ", " <> showPretty b <> ")"
  showPretty (ConvertM a b)     = "ConvertM (" <> (showPretty a) <> ", " <> showPretty b <> ")"
  showPretty (MCreate a b x c ) = "MCreate (" <> (showPretty a) <> ", " <> (showPretty b)  <> ", " <> showPretty x <> ", " <> (showPretty c) <> ")"
  showPretty (Transpose a)      = "Transpose (" <> (showPretty a) <> ")"
  showPretty (Size a)           = "Size (" <> (showPretty a) <> ")"
  showPretty (Length a)         = "Length (" <> (showPretty a) <> ")"
  showPretty (Index a b c)      = "Index (" <> (showPretty a) <> ", " <> (showPretty b)  <> ", " <> (showPretty c) <> ")"
  showPretty (VIndex a b)       = "VIndex (" <> (showPretty a) <> ", " <> (showPretty b)  <> ")"
  showPretty (Row a b)          = "Row (" <> (showPretty a) <> ", " <> (showPretty b) <> ")"
  showPretty (ClipN a b c)      = "ClipN (" <> (showPretty a) <> ", " <> (showPretty b) <> ", " <> (showPretty c) <> ")"
  showPretty (ClipM c a)        = "ClipM (" <> showPretty c <> ", " <> (showPretty a) <> ")"
  showPretty (MutClipM c a)     = "MutClipM (" <> showPretty c <> ", " <> (showPretty a) <> ")"
  showPretty (SubGrad a b)      = "SubGrad (" <> (showPretty a) <> ", " <> (showPretty b) <>  ")"
  showPretty (MutSubGrad a b)      = "MutSubGrad (" <> (showPretty a) <> ", " <> (showPretty b) <>  ")"
  showPretty (ScaleGrad a b)    = "ScaleGrad (" <> (showPretty a) <> ", " <> (showPretty b) <>  ")"
  showPretty (TProject x a)     = "Proj" <> showPretty x <> " " <>  (showPretty a)
  showPretty (Loop a b x d )    = "Loop (" <> (showPretty a) <> ", " <> (showPretty b)  <> ", " <> showPretty x <> ")" <> parenIndent (showPretty d)
  showPretty (SBind x a b)      = "SBind " <> showVar x <> " <- " <> newlineIndentIfLong (showPretty a) <> "\n" <> (showPretty b)

  showPretty (ZeroGrad a)       = "ZeroGrad " <> (showPretty a)
  showPretty (SumGrads a b)     = "SumGrads (" <> (showPretty a) <> ", " <> (showPretty b) <> ")"
  showPretty (SmpLet v a b)     = "SmpLet " <> showPretty v <> " <- " <> (showPretty a) <> "\n" <> (showPretty b)
  showPretty (Sample a b c)     = "Sample (" <> (showPretty a) <> ", " <> (showPretty b) <> ", " <> (showPretty c) <> ")"
  showPretty (Clone a)  = "(Clone " <> showPretty a <> ")"
  showPretty (InternalExpectConst a) = "InternalExpectConst " <> (showPretty a)
  showPretty (InternalMutate a) = "InternalMutate " <> (showPretty a)

instance ShowPretty a => ShowPretty (ProceduralExtension a) where
  showPretty = \case
    ProcTLetBase lk v a -> "PTLet " <> showVar v <> " = " <> newlineIndentIfLong (showPretty a)
    ProcSLetBase lk v a -> "PSLet " <> showVar v <> " = " <> newlineIndentIfLong (showPretty a)
    ProcFLet v a        -> "PFLet " <> showVar v <> " = " <> newlineIndentIfLong (showPretty a)
    ProcBBLet v jts     -> "PBBLet " <> showVar v <> " = " <> newlineIndentIfLong (showPretty jts)
    ProcPhi a b c        -> "PPhi " <> showPretty a <> "\n" <> braceIndent (showPretty b) <> "\n" <> braceIndent (showPretty c)
    ProcPreLoop a x d   -> "PLoop (" <> (showPretty a) <> ", " <> showPretty x <> ")" <> parenIndent (showPretty d)
    ProcReturn          -> "PReturn"
    ProcVarTerm pa  -> showPretty pa
    ProcLam jts ret a       -> "PLam (" <> showPretty jts <> " -> " <> showPretty ret <> ")" <> parenIndent (showPretty a)
    ProcLamStar jts ret a   -> "PLamStar (" <> showPretty jts <> " ->* " <> showPretty ret <> ")" <> parenIndent (showPretty a)
    ProcBBApply t as k  -> "PBBApply (" <> showPretty t <> ") (" <> showPretty as <> ") -> " <> showPretty k
    Block as -> braceIndent $ intercalateS "\n" $ showPretty <$> as

instance ShowPretty a => ShowPretty (DemutatedExtension a) where
  showPretty = \case
    DemutTLetBase lk v a -> "DTLet " <> showVar v <> " = " <> newlineIndentIfLong (showPretty a)
    DemutSLetBase lk v a -> "DSLet " <> showVar v <> " = " <> newlineIndentIfLong (showPretty a)
    DemutFLet v a        -> "DFLet " <> showVar v <> " = " <> newlineIndentIfLong (showPretty a)
    DemutBBLet v jts     -> "DBBLet " <> showVar v <> " = " <> newlineIndentIfLong (showPretty jts)
    DemutPhi a b c       -> "DPhi " <> showPretty a <> "\n" <> braceIndent (showPretty b) <> "\n" <> braceIndent (showPretty c)
    DemutLoop a b c x d    -> "Loop (" <> (showPretty a) <> ", " <> (showPretty b)  <> ", " <> (showPretty c)  <> ", " <> showPretty x <> ")" <> parenIndent (showPretty d)
    DemutBlock as        -> braceIndent $ intercalateS "\n" $ showPretty <$> reverse as


instance (forall a. ShowPretty a => ShowPretty (t a)) => ShowPretty (BBKind t) where
  showPretty = \case
    BBSimple jt          -> "BBSimple " <> showPretty jt
    BBVecLike jt pdt     -> "BBVecLike " <> showPretty jt <> " (" <> showPretty pdt <> ")"
    BBMatrix jt pdt pdt' -> "BBMatrix " <> showPretty jt <> " (" <> showPretty pdt <> ", " <> showPretty pdt' <> ")"

instance ShowPretty (EmptyExtension a) where
  showPretty a = undefined

instance (forall a. ShowPretty a => ShowPretty (t a)) => ShowLocated (PreDMTerm t) where
  showLocated = pure . showPretty


--------------------------------------------------------------------------
-- The environment for executing typechecking

data DMEnv = DMEnv
  {
    -- askJuliaSubtypeOf :: Maybe (FunPtr (JuliaType -> JuliaType -> Bool))
    askJuliaSubtypeOf :: Maybe (FunPtr (CString -> CString -> Bool))
  }
makeDMEnv :: FunPtr (CString -> CString -> Bool) -> DMEnv
makeDMEnv subtype = DMEnv
  { askJuliaSubtypeOf = Just $ subtype
  -- { askJuliaSubtypeOf = Just $ \(JuliaType _ a) (JuliaType _ b) -> subtype a b
  }
makeEmptyDMEnv :: DMEnv
makeEmptyDMEnv = DMEnv
  { askJuliaSubtypeOf = Nothing
  }


-------------------------------------------------------------------------
-- Relevance Annotations

data Relevance = IsRelevant | NotRelevant
  deriving (Eq, Ord)

instance Show Relevance where
   show IsRelevant = "interesting"
   show NotRelevant = "uninteresting"

data WithRelev extra = WithRelev Relevance (DMTypeOf MainKind :@ Annotation extra)


instance Semigroup Relevance where
  (<>) IsRelevant b = IsRelevant
  (<>) a IsRelevant = IsRelevant
  (<>) _ _ = NotRelevant

instance Show (WithRelev e) where
  show (WithRelev IsRelevant  x) = show x
  show (WithRelev NotRelevant x) = "{" <> show x <> "}"

makeRelev :: (DMTypeOf MainKind :@ Annotation e) -> WithRelev e
makeRelev = WithRelev IsRelevant

makeNotRelev :: (DMTypeOf MainKind :@ Annotation e) -> WithRelev e
makeNotRelev = WithRelev NotRelevant

