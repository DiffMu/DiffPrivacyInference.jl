
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE UndecidableInstances #-}


{- |
Description: Definition of the TC monad in which typechecking happens.

Defines the TC monad, ie.:
 - all class instances for Types, Sensitivity, Privacy terms.
 - all substitution, normalization, constraints, logging functionality for TC
-}
module DiffMu.Core.TC where

import DiffMu.Prelude
import DiffMu.Abstract
import DiffMu.Core.Definitions
import DiffMu.Core.Symbolic
import DiffMu.Core.Logging
import {-# SOURCE #-} DiffMu.Typecheck.Subtyping
import {-# SOURCE #-} DiffMu.Core.Unification
import DiffMu.Typecheck.Constraint.Definitions

import Data.List (partition)
import qualified Data.HashMap.Strict as H
import qualified Prelude as P
import qualified Data.Text as T

import Debug.Trace
import DiffMu.Core.Symbolic (normalizeSensSpecial)

default (Text)


--------------------------------------------------------------------------------------------------
-- Substitution
--------------------------------------------------------------------------------------------------

instance Substitute TVarOf DMTypeOf Int where
  substitute σs jt = pure jt

instance Substitute TVarOf DMTypeOf JuliaType where
  substitute σs jt = pure jt

instance Substitute SVarOf SensitivityOf JuliaType where
  substitute σs jt = pure jt

instance Substitute TVarOf DMTypeOf Sensitivity where
  substitute σs η = pure η

instance (Typeable a, Typeable v, Substitute v a DMMain, Substitute v a (Annotation x)) => Substitute v a (WithRelev x) where
  substitute σs (WithRelev i x) = WithRelev i <$> (substitute σs x)

instance Substitute v a x => Substitute v a (H.HashMap k x) where
  substitute σs h = mapM (substitute σs) h

instance Substitute TVarOf DMTypeOf (SVarOf k) where
  substitute σs = pure

instance Substitute SVarOf SensitivityOf (AnnotationKind) where
  substitute σs = pure

instance Substitute TVarOf DMTypeOf DMTypeOp where
  substitute σs (Unary op arg res) = (Unary op <$> substitute σs arg <*> substitute σs res)
  substitute σs (Binary op args res) = (Binary op <$> substitute σs args <*> substitute σs res)

instance Substitute TVarOf DMTypeOf (Annotation a) where
  substitute σs (SensitivityAnnotation s) = SensitivityAnnotation <$> (substitute σs s)
  substitute σs (PrivacyAnnotation s) = PrivacyAnnotation <$> (substitute σs s)

instance Substitute TVarOf DMTypeOf (AnnotationKind) where
  substitute σs = pure

instance Substitute SVarOf SensitivityOf Text where
  substitute _ x = pure x

instance Substitute TVarOf DMTypeOf Text where
  substitute _ x = pure x

instance Substitute SVarOf SensitivityOf (SensitivityOf k) where
  substitute (σs :: forall k. (IsKind k) => SVarOf k -> t (SensitivityOf k)) s = substitute f s
    where f :: (IsKind l) => SymVar l -> t (SensitivityOf l)
          f (HonestVar a) = σs (a)
          -- f (Id a) = pure (coerce a)
          f b = pure $ var (b)

instance Substitute TVarOf DMTypeOf (DMTypeOf k) where
  substitute σs DMAny = pure DMAny
  substitute σs L1 = pure L1
  substitute σs L2 = pure L2
  substitute σs LInf = pure LInf
  substitute σs U = pure U
  substitute σs Vector = pure Vector
  substitute σs Gradient = pure Gradient
  substitute σs (Matrix r) = Matrix <$> substitute σs r
  substitute σs (Clip n) = Clip <$> substitute σs n
  substitute σs DMBool = pure DMBool
  substitute σs DMInt = pure DMInt
  substitute σs DMReal = pure DMReal
  substitute σs DMData = pure DMData
  substitute σs (IRNum τ) = IRNum <$> substitute σs τ
  substitute σs (Numeric τ) = Numeric <$> substitute σs τ
  substitute σs (NonConst) = pure NonConst
  substitute σs (Const c) = Const <$> substitute σs c
  substitute σs (Num τ c) = Num <$> substitute σs τ <*> substitute σs c
  substitute σs (TVar x) = σs x
  substitute σs (τ1 :->: τ2) = (:->:) <$> substitute σs τ1 <*> substitute σs τ2
  substitute σs (τ1 :->*: τ2) = (:->*:) <$> substitute σs τ1 <*> substitute σs τ2
  substitute σs (DMTup τs) = DMTup <$> substitute σs τs
  substitute σs (DMContainer k nrm clp n τ) = DMContainer <$> substitute σs k <*> substitute σs nrm <*> substitute σs clp <*> substitute σs n <*> substitute σs τ
  substitute σs (DMMat nrm clp n m τ) = DMMat <$> substitute σs nrm <*> substitute σs clp <*> substitute σs n <*> substitute σs m <*> substitute σs τ
  substitute σs (DMModel m) = DMModel <$> substitute σs m
  substitute σs (NoFun (x)) = NoFun <$> substitute σs x
  substitute σs (Fun xs) = Fun <$> substitute σs xs
  substitute σs (x :∧: y) = (:∧:) <$> substitute σs x <*> substitute σs y
  substitute σs (BlackBox n) = pure (BlackBox n)


instance Substitute SVarOf SensitivityOf (Annotation a) where
  substitute σs (SensitivityAnnotation s) = SensitivityAnnotation <$> (substitute σs s)
  substitute σs (PrivacyAnnotation s) = PrivacyAnnotation <$> (substitute σs s)

instance Substitute SVarOf SensitivityOf (DMTypeOf k) where
  substitute σs DMAny = pure DMAny
  substitute σs L1 = pure L1
  substitute σs L2 = pure L2
  substitute σs LInf = pure LInf
  substitute σs U = pure U
  substitute σs Vector = pure Vector
  substitute σs Gradient = pure Gradient
  substitute σs (Matrix n) = Matrix <$> substitute σs n
  substitute σs (Clip n) = Clip <$> substitute σs n
  substitute σs DMBool = pure DMBool
  substitute σs DMInt = pure DMInt
  substitute σs DMReal = pure DMReal
  substitute σs (DMData) = pure DMData
  substitute σs (IRNum τ) = IRNum <$> substitute σs τ
  substitute σs (Numeric τ) = Numeric <$> substitute σs τ
  substitute σs (NonConst) = pure NonConst
  substitute σs (Const c) = Const <$> substitute σs c
  substitute σs (Num τ c) = Num <$> substitute σs τ <*> substitute σs c
  substitute σs (TVar x) = pure (TVar x)
  substitute σs (τ1 :->: τ2) = (:->:) <$> substitute σs τ1 <*> substitute σs τ2
  substitute σs (τ1 :->*: τ2) = (:->*:) <$> substitute σs τ1 <*> substitute σs τ2
  substitute σs (DMTup τs) = DMTup <$> substitute σs τs
  substitute σs (DMContainer k nrm clp n τ) = DMContainer <$> substitute σs k <*> substitute σs nrm <*> substitute σs clp <*> substitute σs n <*> substitute σs τ
  substitute σs (DMMat nrm clp n m τ) = DMMat nrm clp <$> substitute σs n <*> substitute σs m <*> substitute σs τ
  substitute σs (DMModel m) = DMModel <$> substitute σs m
  substitute σs (NoFun x) = NoFun <$> substitute σs x
  substitute σs (Fun xs) = Fun <$> substitute σs xs
  substitute σs (x :∧: y) = (:∧:) <$> substitute σs x <*> substitute σs y
  substitute σs (BlackBox n) = pure (BlackBox n)




--------------------------------------------------------------------------------------------------
-- Free variables
--------------------------------------------------------------------------------------------------


instance FreeVars TVarOf Int where
  freeVars _ = mempty

instance FreeVars TVarOf (Solvable (GoodConstraint) (GoodConstraintContent) MonadDMTC) where
  freeVars (Solvable (c :: c a)) = freeVars @_ @TVarOf (runConstr c)

instance DMExtra a => FreeVars TVarOf (WithRelev a) where
  freeVars (WithRelev _ a) = freeVars a

instance FreeVars TVarOf Symbol where
   freeVars a = []

instance FreeVars TVarOf IxSymbol where
   freeVars a = []

instance FreeVars TVarOf TeVar where
   freeVars a = []

instance FreeVars TVarOf AnnotationKind where
   freeVars a = []

instance (FreeVars v a, FreeVars v b) => FreeVars v (Either a b) where
  freeVars (Left aa) = freeVars aa
  freeVars (Right bb) = freeVars bb

instance (FreeVars v a, FreeVars v b) => FreeVars v (a :@ b) where
  freeVars (a :@ b) = freeVars a <> freeVars b

instance (FreeVars v a, FreeVars v b) => FreeVars v (a :=: b) where
  freeVars (a :=: b) = freeVars a <> freeVars b

instance FreeVars TVarOf Sensitivity where
  freeVars _ = mempty

instance FreeVars TVarOf JuliaType where
  freeVars _ = mempty

instance Typeable k => FreeVars TVarOf (SVarOf k) where
  freeVars = mempty

instance FreeVars TVarOf DMTypeOp where
  freeVars (Unary op arg res) = freeVars arg <> freeVars res
  freeVars (Binary op arg res) = freeVars arg <> freeVars res

instance Typeable a => FreeVars TVarOf (Annotation a) where
  freeVars (SensitivityAnnotation s) = freeVars s
  freeVars (PrivacyAnnotation s) = freeVars s

instance Typeable k => FreeVars TVarOf (DMTypeOf k) where
  freeVars DMAny = []
  freeVars DMBool = []
  freeVars DMInt = []
  freeVars DMReal = []
  freeVars DMData = []
  freeVars L1 = []
  freeVars L2 = []
  freeVars LInf = []
  freeVars U = []
  freeVars Vector = []
  freeVars Gradient = []
  freeVars (Matrix τ) = freeVars τ
  freeVars (Clip τ) = freeVars τ
  freeVars (IRNum τ) = freeVars τ
  freeVars (Numeric τ) = freeVars τ
  freeVars (Const t) = freeVars t
  freeVars (NonConst) = []
  freeVars (Num t c) = freeVars t <> freeVars c
  freeVars (TVar x) = [SomeK x]
  freeVars (τ1 :->: τ2) = freeVars (τ1) <> freeVars τ2
  freeVars (τ1 :->*: τ2) = freeVars (τ1) <> freeVars τ2
  freeVars (DMTup τs) = freeVars τs
  freeVars (DMContainer k nrm clp n τ) = freeVars k <> freeVars nrm <> freeVars clp <> freeVars τ
  freeVars (DMMat nrm clp n m τ) = freeVars nrm <> freeVars clp <> freeVars τ
  freeVars (DMModel m) = []
  freeVars (NoFun x) = freeVars x
  freeVars (Fun xs) = freeVars xs
  freeVars (x :∧: y) = freeVars x <> freeVars y
  freeVars (BlackBox n) = []

instance FreeVars TVarOf SolvingMode where
  freeVars _ = []

instance FreeVars SVarOf SolvingMode where
  freeVars _ = []

instance Substitute SVarOf SensitivityOf SolvingMode where
  substitute _ x = pure x

instance Substitute TVarOf DMTypeOf SolvingMode where
  substitute _ x = pure x

instance FreeVars TVarOf Text where
  freeVars _ = []

instance FreeVars SVarOf Text where
  freeVars _ = []


instance FreeVars SVarOf (SymVal) where
  freeVars _ = []

instance FreeVars SVarOf (SymVar 'MainSensKind) where
  freeVars = \case
    HonestVar so -> [SomeK so]
    Ln sk -> freeVars sk
    Exp x0 -> freeVars x0
    Ceil sk -> freeVars sk
    Sqrt sk -> freeVars sk
    Max sks -> freeVars sks
    Minus x0 -> freeVars x0
    Div sk -> freeVars sk
    TruncateSym sk sk' -> freeVars sk <> freeVars sk'
    TruncateDoubleSym x0 sk -> freeVars x0 <> freeVars sk

instance Typeable k => FreeVars SVarOf (SensitivityOf k) where
  freeVars (SingleKinded (LinCom (MonCom as))) = H.toList as >>= f
    where
      f :: (MonCom Int (SymVar 'MainSensKind), SymVal) -> [SomeK SVarOf]
      f (MonCom bs, val) = (H.toList bs >>= g) <> freeVars val

      g :: (SymVar 'MainSensKind, Int) -> [SomeK SVarOf]
      g (x, _) = freeVars x



--------------------------------------------------------------------------------------------------
-- term instances
--------------------------------------------------------------------------------------------------

type TSubs = Subs DMTypeOf
type SSubs = Subs SensitivityOf

instance Term TVarOf DMTypeOf where
  var x = TVar x
  isVar (TVar x) = Just x
  isVar _        = Nothing

-- TODO: implement isVar and freeVars
instance Term SVarOf SensitivityOf where
  var (v) = var (HonestVar v)
  isVar s = case isVar s of
    Just (HonestVar v) -> Just v
    _ -> Nothing

--------------------------------------------------------------------------------------------------
-- variable helper functions
--------------------------------------------------------------------------------------------------
  
removeVars :: forall t. Monad t => (forall k. (IsKind k) => TVarOf k -> t (DMTypeOf k)) -> [SomeK (TVarOf)] -> t [SomeK (TVarOf)]
removeVars σs vs = do
  let f :: SomeK (TVarOf) -> t (Maybe (SomeK TVarOf))
      f (SomeK var) = do
        replacement <- σs var
        case (replacement) of
          TVar rep | rep == var -> return (Just (SomeK var))
          _ -> return Nothing
  newvs <- mapM f vs
  return [v | (Just v) <- newvs]


filterWithSomeVars :: FreeVars TVarOf x => [SomeK TVarOf] -> [x] -> [x]
filterWithSomeVars wanted ctrs =
  let f x = freeVars @_ @TVarOf x
  in [x | x <- ctrs , length (intersect (f x) wanted) > 0]





--------------------------------------------------------------------------------------------------
-- main MonadDMTC class
--------------------------------------------------------------------------------------------------

class GoodConstraint (x :: *) where
instance GoodConstraint x where

class (FreeVars TVarOf x, Substitute TVarOf DMTypeOf x) => GoodConstraintContent (x :: *) where
instance (FreeVars TVarOf x, Substitute TVarOf DMTypeOf x) => GoodConstraintContent x where

class (MonadImpossible (t), MonadWatch (t), MonadLog t,
       MonadTerm DMTypeOf (t),
       MonadTerm SensitivityOf (t),
       MonadState (Full (DMPersistentMessage t)) (t),
       MonadWriter (DMMessages t) (t),
       MonadDMError (WithContext DMException) (t),
       MonadInternalError t,
       MonadUnificationError t,
       MonadConstraint (MonadDMTC) (t),
       MonadNormalize t,
       ContentConstraintOnSolvable t ~ GoodConstraintContent,
       ConstraintOnSolvable t ~ GoodConstraint,
       LiftTC t
      ) => MonadDMTC (t :: * -> *) where




--------------------------------------------------------------------------------------------------
-- Watched (change tracking system)
--------------------------------------------------------------------------------------------------

---------
-- normalization levels
--
-- the system tracks for which solving modes the content is already normal,
-- such that normalization for that mode does not have to be executed again.

data NormalizationLevel = NormalForMode [SolvingMode]
  deriving (Eq)

-- this is the action of Changed on NormalizationLevel
updateNormalizationLevel :: Changed -> NormalizationLevel -> NormalizationLevel
updateNormalizationLevel NotChanged a = a
updateNormalizationLevel IsChanged _ = NormalForMode []

instance Semigroup NormalizationLevel where
  NormalForMode a <> NormalForMode b = NormalForMode (a `intersect` b)

---------
-- definition of `Watched`

data Watched a = Watched NormalizationLevel a

---------
-- instances

instance Show a => Show (Watched a) where
  show (Watched (NormalForMode m) a) = show m <> " " <> show a

instance ShowPretty a => ShowPretty (Watched a) where
  showPretty (Watched (NormalForMode m) a) = showPretty a

instance ShowLocated a => ShowLocated (Watched a) where
  showLocated (Watched (NormalForMode m) a) = showLocated a

instance (MonadWatch t, Normalize t a) => Normalize t (Watched a) where
  normalize nt (Watched c a) =
    do resetChanged
       a' <- normalize nt a
       newc <- getChanged
       return (Watched (updateNormalizationLevel newc c) a')

instance (SemigroupM t a) => SemigroupM t (Watched a) where
  (⋆) (Watched x a) (Watched y b) = Watched (x <> y) <$> a ⋆ b

instance (MonoidM t a) => MonoidM t (Watched a) where
  neutral = Watched (NormalForMode [SolveExact , SolveAssumeWorst , SolveGlobal]) <$> neutral

instance (CheckNeutral t a) => CheckNeutral t (Watched a) where
  checkNeutral a = pure False


--------------------------------------------------------------------------------------------------
-- Constraints with message
--------------------------------------------------------------------------------------------------

instance Monad t => (SemigroupM t (Solvable eC eC2 a)) where
  (⋆) (Solvable a) (Solvable b) = error "Trying to combine two constraints with the same name."
instance Monad t => (MonoidM t (Solvable eC eC2 a)) where
  neutral = error "Trying to get neutral of solvable"
instance Monad t => (CheckNeutral t (Solvable eC eC2 a)) where
  checkNeutral a = pure False

data ConstraintWithMessage m = ConstraintWithMessage (Watched (Solvable GoodConstraint GoodConstraintContent MonadDMTC)) m
  deriving (Functor,Show)

instance ShowPretty m => ShowPretty (ConstraintWithMessage m) where
  showPretty (ConstraintWithMessage c m) = showPretty c <> "\n"
                                          <> indent (showPretty m)

instance ShowLocated m => ShowLocated (ConstraintWithMessage m) where
  showLocated (ConstraintWithMessage c m) = do
    c' <- showLocated c
    m' <- (showLocated m)
    return $ c' <> "\n" <> indent m'

instance (MonadDMTC t, Normalize t m) => Normalize t (ConstraintWithMessage m) where
  normalize e (ConstraintWithMessage x m) = ConstraintWithMessage <$> (normalize e x) <*> normalize e m

instance (SemigroupM t m) => SemigroupM t (ConstraintWithMessage m) where
  (⋆) (ConstraintWithMessage x0 m0) (ConstraintWithMessage x1 m1) = ConstraintWithMessage <$> (x0 ⋆ x1) <*> (m0 ⋆ m1)

instance (MonoidM t m) => MonoidM t (ConstraintWithMessage m) where
  neutral = ConstraintWithMessage <$> neutral <*> neutral


instance (CheckNeutral t m) => CheckNeutral t (ConstraintWithMessage m) where
  checkNeutral (ConstraintWithMessage x m) = do
    nx <- checkNeutral x
    nm <- checkNeutral m
    return (and [nx , nm])


--------------------------------------------------------------------------------------------------
-- Constraint context
--------------------------------------------------------------------------------------------------

data CtxStack v a = CtxStack
  {
    _topctx :: Ctx v a,
    _otherctxs :: [Ctx v a]
  }
deriving instance Functor (CtxStack v)

getValueCtxStack :: DictKey v => v -> CtxStack v a -> Maybe a
getValueCtxStack v (CtxStack top others) = f v (top:others)
  where
    f :: DictKey v => v -> [Ctx v a] -> Maybe a 
    f v [] = Nothing
    f v (x:xs) = case getValue v x of
                  Just a -> Just a
                  Nothing -> f v xs

type ConstraintCtx m = AnnNameCtx (CtxStack IxSymbol (ConstraintWithMessage m))
instance DictKey v => DictLike v x (CtxStack v x) where
  setValue k v (CtxStack d other) = CtxStack (setValue k v d) other
  getValue k (CtxStack d _) = getValue k d
  getAllKeys (CtxStack d _) = getAllKeys d
  getAllElems (CtxStack d _) = getAllElems d
  getAllKeyElemPairs (CtxStack d _) = getAllKeyElemPairs d
  fromKeyElemPairs list = (CtxStack (fromKeyElemPairs list) [])
  deleteValue k (CtxStack d other) = CtxStack (deleteValue k d) other
  emptyDict = CtxStack emptyDict []
  isEmptyDict (CtxStack top others) = isEmptyDict top

instance Normalize t a => Normalize t (CtxStack v a) where
  normalize nt (CtxStack top other) = CtxStack <$> normalize nt top <*> normalize nt other


instance (Show v, Show a, DictKey v) => Show (CtxStack v a) where
      show (CtxStack top other) = "   - top:\n" <> show top <> "\n"
                              <> "   - others:\n" <> show other


instance (ShowPretty v, ShowPretty a, DictKey v) => ShowPretty (CtxStack v a) where
      showPretty (CtxStack top other) = showPretty top <> showPretty other


instance (ShowLocated v, ShowLocated a, DictKey v) => ShowLocated (CtxStack v a) where
      showLocated (CtxStack top other) = do
        top' <- showLocated top
        other' <- showLocated other
        return $ top' <> other'

--------------------------------------------------------------------------------------------------
-- annotated name context
--------------------------------------------------------------------------------------------------

data AnnNameCtx ks = AnnNameCtx
  {
    _annnames :: NameCtx,
    _anncontent :: ks
  }
  deriving (Generic, Functor)

instance (MonadWatch t, Normalize t ks) => Normalize t (AnnNameCtx ks) where
  normalize nt (AnnNameCtx names ks) =
    do res <- AnnNameCtx names <$> normalize nt ks
       -- isC <- getChanged
       -- traceShowM $ "CHANGED: " <> show isC <> "\n"
       return res

instance Show ks => Show (AnnNameCtx ks) where
  show (AnnNameCtx _ kinds) = show kinds

instance ShowPretty ks => ShowPretty (AnnNameCtx ks) where
  showPretty (AnnNameCtx _ kinds) = showPretty kinds


instance ShowLocated ks => ShowLocated (AnnNameCtx ks) where
  showLocated (AnnNameCtx _ kinds) = showLocated kinds

instance Default ks => Default (AnnNameCtx ks)

newAnnName :: DictLike IxSymbol k ks => NamePriority -> Text -> k -> AnnNameCtx ks -> (IxSymbol, AnnNameCtx ks)
newAnnName np hint k (AnnNameCtx names kinds) =
  let (name, names') = newName np hint names
      kinds' = setValue name k kinds
  in (name, AnnNameCtx names' kinds')


--------------------------------------------------------------------------------------------------
-- Casting between privacy and sensitivity contexts
--------------------------------------------------------------------------------------------------

class Cast a b where
  cast :: MonadDMTC t => a -> t b

instance Cast (Either Sensitivity Privacy) Sensitivity where
  cast (Left e) = return e
  cast (Right e) = error $ "Expected a sensitivity but got a privacy (" <> show e <> ")."

instance Cast (Either Sensitivity Privacy) Privacy where
  cast (Left e) = error $ "Expected a privacy but got a sensitivity (" <> show e <> ")."
  cast (Right e) = return e


instance Typeable x => Cast (Either (Annotation SensitivityK) (Annotation PrivacyK)) (Annotation x) where
  cast e =
    let case1 = testEquality (typeRep @x) (typeRep @SensitivityK)
        case2 = testEquality (typeRep @x) (typeRep @PrivacyK)
    in case (case1,case2) of
      (Just Refl, _) -> case e of
                          Left e -> return e
                          Right _ -> error "Expected a sensitivity but got a privacy."
      (_ , Just Refl) -> case e of
                          Right e -> return e
                          Left _ -> error "Expected a privacy but got a sensitivity."
      _    -> impossible "Found an AnnotatedKind which was neither SensitivityK nor PrivacyK."

instance Typeable x => Cast (Either (WithRelev SensitivityK) (WithRelev PrivacyK)) (WithRelev x) where
  cast (Left (WithRelev i x))  = WithRelev i <$> cast @(Either (DMTypeOf MainKind :@ Annotation SensitivityK) (DMTypeOf MainKind :@ Annotation PrivacyK)) (Left x)
  cast (Right (WithRelev i x)) = WithRelev i <$> cast @(Either (DMTypeOf MainKind :@ Annotation SensitivityK) (DMTypeOf MainKind :@ Annotation PrivacyK)) (Right x)



instance (Cast (Either a b) x) => Cast (Either (z :@ a) (z :@ b)) (z :@ x) where
  cast (Left (x :@ e)) = (x :@) <$> cast @(Either a b) (Left e)
  cast (Right (x :@ e)) = (x :@) <$> cast @(Either a b) (Right e)

instance (Cast a b) => Cast (Maybe a) (Maybe b) where
  cast Nothing = pure Nothing
  cast (Just a) = Just <$> cast a


--------------------------------------------------------------------------------------------------
-- solving events
--------------------------------------------------------------------------------------------------

data SolvingEvent =
  Event_ConstraintDischarged IxSymbol
  | Event_ConstraintMarkedFailed IxSymbol
  | Event_ConstraintUpdated IxSymbol String
  | Event_ConstraintCreated IxSymbol String
  | Event_SubstitutionAdded String
  | Event_ConstraintSetCreated
  | Event_ConstraintSetMerged [IxSymbol]

instance Show SolvingEvent where
  show (Event_ConstraintCreated name constr) = "CREATE " <> show name <> " : " <> constr
  show (Event_ConstraintUpdated name constr) = "UPDATE " <> show name <> " : " <> constr
  show (Event_ConstraintDischarged name)     = "DISCHARGE " <> show name
  show (Event_ConstraintMarkedFailed name)   = "MARK FAIL " <> show name
  show (Event_SubstitutionAdded sub)         = "SUB " <> sub
  show (Event_ConstraintSetCreated)          = "CREATE CONSTR_SET"
  show (Event_ConstraintSetMerged constrs)   = "MERGE CONSTR_SET : {" <> intercalate ", " (show <$> constrs) <> "}"



--------------------------------------------------------------------------------------------------
-- User-choosable variables
--------------------------------------------------------------------------------------------------

newtype UserVars = UserVars [(Sensitivity, Text, JuliaType, SourceLocExt)]

instance Default UserVars where
    def = UserVars []

instance MonadDMTC t => Normalize t UserVars where
    normalize nt (UserVars vs) = UserVars <$> normalize nt vs

instance ShowPretty UserVars where
 showPretty (UserVars vs) = let
        isNumber :: SymTerm MainSensKind -> Bool
        isNumber a@(SingleKinded (LinCom (MonCom as))) = case H.toList as of
           [(MonCom aterm, av)] -> case H.toList aterm of
                                       [] -> True
                                       _ -> False
           [] -> True
           _ -> False

        showIfVar (name, cond, typ, loc) = case isNumber name of
           True -> ""
           False -> " - Variable " <> showPretty name <> " can be chosen with type " <> showPretty typ <> " to be " <> cond <> ". Appeared in the privacy loop in " <> showPretty loc <> "\n"
    in case vs of
         [] -> ""
         vs -> let s = (foldl (<>) "" (map showIfVar vs)) in
                   case s of
                        "" -> ""
                        s -> "where\n" <> s

--------------------------------------------------------------------------------------------------
-- The TCT monad transformer and TC monad
--------------------------------------------------------------------------------------------------

-----------------------
-- Definition


data MetaCtx m = MetaCtx
  {
    _sensVars :: KindedNameCtx SVarOf,
    _typeVars :: KindedNameCtx TVarOf,
    _termVars :: NameCtx,
    _sensSubs :: Subs SVarOf SensitivityOf,
    _typeSubs :: Subs TVarOf DMTypeOf,
    _constraints :: ConstraintCtx m,
    _failedConstraints :: Ctx IxSymbol (ConstraintWithMessage m),
    _userVars :: UserVars
  }
  deriving (Generic, Functor)

data Watcher = Watcher Changed
  deriving (Generic)

data TCState m = TCState
  {
    _watcher :: Watcher,
    _logger :: DMLogger,
    _solvingEvents :: [SolvingEvent],
    _persistingCounter :: Int
  }
  deriving (Generic, Functor)

type TypeCtx extra = Ctx TeVar (WithRelev extra)
type TypeCtxSP = Either (TypeCtx SensitivityK) (TypeCtx PrivacyK)

data Full m = Full
  {
    _tcstate :: TCState m,
    _meta :: MetaCtx m,
    _types :: TypeCtxSP
  }
  deriving (Generic, Functor)

newtype TCT m a = TCT {runTCT :: ((StateT (Full (DMPersistentMessage (TCT m))) (ExceptT (LocatedDMException (TCT m)) (ReaderT RawSource (WriterT (DMMessages (TCT m)) (m))))) a)}
  deriving (Functor, Applicative, Monad, MonadState (Full (DMPersistentMessage (TCT m))), MonadError (LocatedDMException (TCT m)), MonadWriter (DMMessages (TCT m)), MonadReader RawSource)

class LiftTC t where
  liftTC :: TC a -> t a

type TC = TCT Identity

-----------------------
-- Lenses

$(makeLenses ''AnnNameCtx)
$(makeLenses ''CtxStack)
$(makeLenses ''MetaCtx)
$(makeLenses ''Full)
$(makeLenses ''TCState)

-----------------------
-- Defaults

instance Default (CtxStack v a) where
  def = CtxStack def []
instance Default (Watcher) where
instance Default (TCState m) where
instance Default (MetaCtx m) where
instance Default (Full m) where
  def = Full def def (Left def)

-----------------------
-- Printing

instance Show m => Show (MetaCtx m) where
  show (MetaCtx s t n sσ tσ cs failedCs (UserVars uvs)) =
       "- sens vars: " <> show s <> "\n"
    <> "- type vars: " <> show t <> "\n"
    <> "- name vars: " <> show n <> "\n"
    <> "- sens subs:   " <> show sσ <> "\n"
    <> "- type subs:   " <> show tσ <> "\n"
    <> "- user-chosen vars: " <> show uvs <> "\n"
    <> "- constraints:\n" <> show cs <> "\n"
    <> "- failed constraints:\n" <> show failedCs <> "\n"

instance ShowLocated m => ShowLocated (MetaCtx m) where
  showLocated (MetaCtx s t n sσ tσ cs failedCs (UserVars uvs)) =
    do lcs <- showLocated cs
       lfailedCs <- showLocated failedCs
       return $
             "- sens vars: " <> T.pack (show s) <> "\n"
          <> "- type vars: " <> T.pack (show t) <> "\n"
          <> "- name vars: " <> T.pack (show n) <> "\n"
          <> "- sens subs:   " <> T.pack (show sσ) <> "\n"
          <> "- type subs:   " <> T.pack (show tσ) <> "\n"
          <> "- user-chosen vars: " <> T.pack (show uvs) <> "\n"
          <> "- constraints:\n" <> lcs <> "\n"
          <> "- failed constraints:\n" <> lfailedCs <> "\n"

instance Show Watcher where
  show (Watcher changed) = show changed

instance Show (TCState m) where
  show (TCState w l _ _) = "- watcher: " <> show w <> "\n"
                        <> "- messages: " <> show l <> "\n"

instance Show m => Show (Full m) where
  show (Full tcs m γ) = "\nState:\n" <> show tcs <> "\nMeta:\n" <> show m <> "\nTypes:\n" <> show γ <> "\n"


--------------------------------------------------------------------------------------------------
-- TC usage helpers
--------------------------------------------------------------------------------------------------


----------
-- user vars

memorizeUserVar :: (MonadDMTC m) => Sensitivity -> Text -> JuliaType -> SourceLocExt -> m ()
memorizeUserVar var bounds ty loc = do
    UserVars ls <- use (meta.userVars)
    meta.userVars .= UserVars ((var, bounds, ty, loc) : ls)


----------
-- constraint creation

supremum :: (IsT isT t, HasNormalize isT ((a k, a k) :=: a k), MonadConstraint isT (t), MonadTerm a (t), Solve isT IsSupremum ((a k, a k) :=: a k), SingI k, Typeable k, ContentConstraintOnSolvable t ((a k, a k) :=: a k), ShowPretty (a k),  ConstraintOnSolvable t (IsSupremum ((a k, a k) :=: a k)), Eq (a k)) => (a k) -> (a k) -> t (a k)
supremum x y = do
  (z :: a k) <- newVar
  addConstraintNoMessage (Solvable (IsSupremum ((x, y) :=: z)))
  return z

supremumFromName :: (IsT isT t, HasNormalize isT ((a k, a k) :=: a k), MonadConstraint isT (t), MonadTerm a (t), Solve isT IsSupremum ((a k, a k) :=: a k), SingI k, Typeable k, ContentConstraintOnSolvable t ((a k, a k) :=: a k), ShowPretty (a k), ConstraintOnSolvable t (IsSupremum ((a k, a k) :=: a k)), Eq (a k)) => IxSymbol -> (a k) -> (a k) -> t (a k)
supremumFromName name x y = do
  (z :: a k) <- newVar
  addConstraintFromName name (Solvable (IsSupremum ((x, y) :=: z)))
  return z

infimum :: (IsT isT t, HasNormalize isT ((a k, a k) :=: a k), MonadConstraint isT (t), MonadTerm a (t), Solve isT IsInfimum ((a k, a k) :=: a k), SingI k, Typeable k, ContentConstraintOnSolvable t ((a k, a k) :=: a k), ShowPretty (a k),  ConstraintOnSolvable t (IsInfimum ((a k, a k) :=: a k)), Eq (a k)) => (a k) -> (a k) -> t (a k)
infimum x y = do
  (z :: a k) <- newVar
  addConstraintNoMessage (Solvable (IsInfimum ((x, y) :=: z)))
  return z

----------
-- variable creation

newTVarWithPriority :: forall k e t. (MonadDMTC t, SingI k, Typeable k) => NamePriority -> Text -> t (TVarOf k)
newTVarWithPriority np hint = meta.typeVars %%= ((newKindedName np hint))

newTVar :: forall k e t. (MonadDMTC t, SingI k, Typeable k) => Text -> t (TVarOf k)
newTVar = newTVarWithPriority GeneratedNamePriority 

newSVarWithPriority :: forall k e t. (SingI k, MonadDMTC t, Typeable k) => NamePriority -> Text -> t (SVarOf k)
newSVarWithPriority np hint = meta.sensVars %%= (newKindedName np hint)

newSVar :: forall k e t. (SingI k, MonadDMTC t, Typeable k) => Text -> t (SVarOf k)
newSVar = newSVarWithPriority GeneratedNamePriority

newPVar = do
   p1 :: Sensitivity <- svar <$> newSVarWithPriority UserNamePriority "ε"
   p2 :: Sensitivity <- svar <$> newSVarWithPriority UserNamePriority "δ"
   return (p1, p2)

newTeVar :: (MonadDMTC m) => Text -> m (TeVar)
newTeVar hint = meta.termVars %%= (first (\x -> GenTeVar x Nothing) . (newName GeneratedNamePriority hint))

--------------------------------------------------------------------------------------------------
-- Monad instance: MonadLog
--------------------------------------------------------------------------------------------------

logForceStart :: MonadDMTC t => t ()
logForceStart = do
  old <- (tcstate.logger.loggerCurrentSeverity) %%= (\old -> (old,Force))
  (tcstate.logger.loggerBackupSeverity) %= (\_ -> old)

logForceEnd :: MonadDMTC t => t ()
logForceEnd = do
  old <- use (tcstate.logger.loggerBackupSeverity)
  (tcstate.logger.loggerCurrentSeverity) %= (\_ -> old)


dmWithLogLocation :: MonadDMTC t => DMLogLocation -> t a -> t a
dmWithLogLocation l action = do
  oldloc <- use (tcstate.logger.loggerCurrentLocation)
  (tcstate.logger.loggerCurrentLocation) %= (\_ -> l)
  res <- action
  (tcstate.logger.loggerCurrentLocation) %= (\_ -> oldloc)
  return res


logWithSeverity :: MonadDMTC t => DMLogSeverity -> Text -> t ()
logWithSeverity sev text = do
  loc <- use (tcstate.logger.loggerCurrentLocation)
  -- here we split the messages at line breaks (using `lines`)
  -- in order to get consistent looking output (every line has a header)
  let messages = DMLogMessage sev loc <$> (reverse $ linesS text)
  -- traceM text -- force logging even if the computation des not terminate
  tell (DMMessages messages [])
  -- tcstate.logger.loggerMessages %= (messages <>)

dmlog :: MonadDMTC t => Text -> t ()
dmlog text = do
  loc <- use (tcstate.logger.loggerCurrentLocation)
  sev <- use (tcstate.logger.loggerCurrentSeverity)
  -- here we split the messages at line breaks (using `lines`)
  -- in order to get consistent looking output (every line has a header)
  let messages = DMLogMessage sev loc <$> (reverse $ linesS text)
  -- traceM text -- force logging even if the computation des not terminate
  tell (DMMessages messages [])
  -- tcstate.logger.loggerMessages %= ( <>)

instance Monad m => MonadLog (TCT m) where
  log = dmlog
  debug = logWithSeverity Debug
  info = logWithSeverity Info
  logForce = logWithSeverity Force
  warn = logWithSeverity Warning
  withLogLocation loc action = dmWithLogLocation (fromString_DMLogLocation loc) action


--------------------------------------------------------------------------------------------------
-- Monad instance: MonadTerm
--------------------------------------------------------------------------------------------------

instance Monad m => MonadTerm DMTypeOf (TCT m) where
  type VarFam DMTypeOf = TVarOf
  getSubs = view (meta.typeSubs) <$> get
  addSub σ = do
    σs <- use (meta.typeSubs)
    -- traceM ("/ Type: I have the subs " <> show σs <> ", and I want to add: " <> show σ)
    -- withLogLocation "Subst" $ debug ("/ Type: I have the subs " <> show σs <> ", and I want to add: " <> show σ)
    withLogLocation "Subst" $ debug ("Adding type subst: " <> T.pack (show σ))
    tcstate.solvingEvents %= (Event_SubstitutionAdded (show σ) :)
    -- logPrintConstraints
    σs' <- σs ⋆ singletonSub σ
    -- traceM ("\\ Type: I now have: " <> show σs')
    meta.typeSubs .= σs'
    meta.typeVars %= (removeNameBySubstitution σ)

  newVar = TVar <$> newTVar "τ"


instance Monad m => MonadTerm SensitivityOf (TCT m) where
  type VarFam SensitivityOf = SVarOf
  getSubs = view (meta.sensSubs) <$> get
  addSub σ = do
    σs <- use (meta.sensSubs)
    -- traceM ("I have the subs " <> show σs <> ", and I want to add: " <> show σ)
    tcstate.solvingEvents %= (Event_SubstitutionAdded (show σ) :)
    σs' <- σs ⋆ singletonSub σ
    meta.sensSubs .= σs'
    meta.sensVars %= (removeNameBySubstitution σ)
  newVar = coerce <$> svar <$> newSVar "s"


--------------------------------------------------------------------------------------------------
-- Monad instance: MonadConstraint
--------------------------------------------------------------------------------------------------

instance Monad m => MonadConstraint (MonadDMTC) (TCT m) where
  type ConstraintBackup (TCT m) = (Ctx IxSymbol (Watched (Solvable GoodConstraint GoodConstraintContent MonadDMTC)))
  type ContentConstraintOnSolvable (TCT m) = GoodConstraintContent
  type ConstraintOnSolvable (TCT m) = GoodConstraint
  addConstraint (Solvable c) constr_desc = do

      -- add the constraint to the constraint list
      name :: IxSymbol <- meta.constraints %%= (newAnnName GeneratedNamePriority "constr" (ConstraintWithMessage (Watched (NormalForMode []) (Solvable c)) (DMPersistentMessage constr_desc)))

      -- log this as event
      tcstate.solvingEvents %= (Event_ConstraintCreated name (show c) :)

      return name


  getUnsolvedConstraintMarkNormal modes = do
    (Ctx (MonCom constrs)) <- use (meta.constraints.anncontent.topctx)

    let constrs2 = H.toList constrs
    let changedFor curMode = filter (\(a, (ConstraintWithMessage (Watched (NormalForMode normalModes) constr) _)) -> (curMode `notElem` normalModes)) constrs2
    let changed = join [zip (changedFor m) (repeat m) | m <- modes]
    case changed of
      [] -> return Nothing
      ((((name,(ConstraintWithMessage (Watched (NormalForMode normalModes) constr) descr)),newMode):_)) -> do
        meta.constraints.anncontent.topctx %= (setValue name (ConstraintWithMessage (Watched (NormalForMode (newMode:normalModes)) constr) descr))
        return (Just (name, constr, newMode, descr))

  dischargeConstraint name = do
    meta.constraints.anncontent.topctx %= (deleteValue name)

    -- log this as event
    tcstate.solvingEvents %= (Event_ConstraintDischarged name :)

  markFailedConstraint name = do
    val <- getValue name <$> use (meta.constraints.anncontent.topctx)
    case val of
      Nothing -> internalError $ "Expected constraint " <> showT name <> " to exist."
      Just val -> do
        meta.constraints.anncontent.topctx %= (deleteValue name)
        meta.failedConstraints %= (setValue name val)

        -- log this as event
        tcstate.solvingEvents %= (Event_ConstraintMarkedFailed name :)

  failConstraint name = do
    (AnnNameCtx n cs) <- use (meta.constraints)
    let c = getValue name cs
    throwUnlocatedError (UnsatisfiableConstraint (show c))

  updateConstraint name c = do
    meta.constraints %= (\(AnnNameCtx n cs) -> AnnNameCtx n (changeValue name (\(ConstraintWithMessage _ descr) -> ConstraintWithMessage (Watched (NormalForMode []) c) descr) cs))

    -- log this as event
    tcstate.solvingEvents %= (Event_ConstraintUpdated name (show c) :)

  openNewConstraintSet = do
    (CtxStack top other) <- use (meta.constraints.anncontent)
    meta.constraints.anncontent .= (CtxStack emptyDict (top:other))

    -- log this as event
    tcstate.solvingEvents %= (Event_ConstraintSetCreated :)

    return ()

  mergeTopConstraintSet = do
    (CtxStack (Ctx (MonCom top)) other) <- use (meta.constraints.anncontent)
    case other of
      ((Ctx o):os) -> case null top of
        False -> do
          o' <- MonCom top ⋆ o
          meta.constraints.anncontent .= (CtxStack (Ctx o') os)

          -- log this as event
          tcstate.solvingEvents %= (Event_ConstraintSetMerged (H.keys top) :)
          return ConstraintSet_WasNotEmpty

        True -> do
          meta.constraints.anncontent .= (CtxStack (Ctx o) os)

          -- log this as event
          tcstate.solvingEvents %= (Event_ConstraintSetMerged [] :)
          return ConstraintSet_WasEmpty

      [] -> error "Trying to merge top constraint set, but there are non in the stack."

  getConstraintsByType (Proxy :: Proxy (c a)) = do
    (Ctx (MonCom cs)) <- use (meta.constraints.anncontent.topctx)
    let f :: (ConstraintWithMessage n) -> Maybe (c a) -- (Watched (Solvable GoodConstraint GoodConstraintContent MonadDMTC)) -> Maybe (c a)
        f (ConstraintWithMessage (Watched _ (Solvable (c :: c' a'))) _) = case testEquality (typeRep @(c a)) (typeRep @(c' a')) of
          Just Refl -> Just c
          Nothing -> Nothing

    let cs' = H.toList cs
        cs'' = second f <$> cs'
    return [(name,c) | (name, (Just c)) <- cs'' ]

  logPrintConstraints = do
    ctrs <- use (meta.constraints.anncontent)
    log $ "## Constraints ##"
    log $ T.pack $ show ctrs
    log $ ""

  logPrintSubstitutions = do
    ctrs <- use (meta.sensSubs)
    log $ "## Substitutions ##"
    log $ T.pack $ show ctrs
    log $ ""

  getAllConstraints = do
    (Ctx (MonCom cs)) <- use (meta.constraints.anncontent.topctx)
    let cs' = H.toList cs
    return [(name,c) | (name, (ConstraintWithMessage (Watched _ c) _)) <- cs']

  nubConstraints = do
    cs <- getAllKeyElemPairs <$> use (meta.constraints.anncontent.topctx)

    let getNamesToDischarge ((name,c):cs) = do
          let (duplicateConstrs,otherConstrs) = partition (\(n,c') -> c' == c) cs
          let namesToDischarge = fst <$> duplicateConstrs
          case length namesToDischarge > 0 of
            True -> debug $ "Discharging duplicate constraints for " <> showPretty name <> ":\n"
                      <> "  The following constraints have the same content and are going to be discharged:\n"
                      <> "  " <> showPretty namesToDischarge
            False -> return ()
          otherNamesToDischarge <- getNamesToDischarge otherConstrs
          return (namesToDischarge <> otherNamesToDischarge)
        getNamesToDischarge [] = return []

    names <- getNamesToDischarge (fmap (second (\(ConstraintWithMessage (Watched _ c) _) -> c)) cs)
    mapM dischargeConstraint names
    return ()


  clearSolvingEvents = do
    events <- tcstate.solvingEvents %%= (\ev -> (ev,[]))
    return (showT <$> (reverse events))

  getConstraintMessage name = do
    (AnnNameCtx _ ctrs) <- use (meta.constraints) 
    case getValueCtxStack name ctrs of
      Just (ConstraintWithMessage _ descr) -> return descr
      Nothing -> internalError $ "Expected a constraint with the name " <> showT name <> " to exist (getting message).\n"
                                <> "Ctrs is:\n" 
                                <> showT ctrs

  getConstraint name = do
    (AnnNameCtx _ ctrs) <- use (meta.constraints) 
    case getValueCtxStack name ctrs of
      Just (ConstraintWithMessage (Watched _ a) descr) -> return (a, descr)
      Nothing -> internalError $ "Expected a constraint with the name " <> showT name <> " to exist (getting constraint content).\n"
                                <> "Ctrs is:\n" 
                                <> showT ctrs



--------------------------------------------------------------------------------------------------
-- Monad instance: MonadWatch
--------------------------------------------------------------------------------------------------
instance Monad m => MonadWatch (TCT m) where
  resetChanged = tcstate.watcher %= (\(Watcher _) -> Watcher NotChanged)
  notifyChanged = tcstate.watcher %= (\(Watcher _) -> Watcher IsChanged)
  getChanged = do (Watcher c) <- use (tcstate.watcher)
                  return c


--------------------------------------------------------------------------------------------------
-- Monad instance: MonadInternalError
--------------------------------------------------------------------------------------------------
instance Monad m => MonadInternalError (TCT m) where
  internalError = throwUnlocatedError . InternalError


--------------------------------------------------------------------------------------------------
-- Monad instance: MonadUnificationError
--------------------------------------------------------------------------------------------------
instance Monad m => MonadUnificationError (TCT m) where
  unificationError x y = throwUnlocatedError $ UnificationError x y


--------------------------------------------------------------------------------------------------
-- Monad instance: MonadDMError
--------------------------------------------------------------------------------------------------
instance Monad m => MonadDMError (WithContext DMException) (TCT m) where
  isCritical (WithContext e _)= return (isCriticalError e)
  persistentError e = tell (DMMessages [] [e])
  catchAndPersist x handler = do
      persistingC <- use (tcstate.persistingCounter)
      case persistingC == 0 of
        True -> do
          catchError x $ \(WithContext err msg) -> do
            case isCriticalError err of
              True -> throwError (WithContext err msg)
              False -> do
                (res,msg') <- handler msg
                tell (DMMessages [] [(WithContext err (DMPersistentMessage msg'))])
                return res
        False -> x


  enterNonPersisting = tcstate.persistingCounter %= (P.+ 1)
  exitNonPersisting = tcstate.persistingCounter %= (P.- 1)



--------------------------------------------------------------------------------------------------
-- Monad instance: MonadNormalize
--------------------------------------------------------------------------------------------------

-- Normalizes all contexts in our typechecking monad, i.e., applies all available substitutions.
normalizeContext :: (MonadDMTC t) => NormalizationType -> t ()
normalizeContext nt = do
  types %=~ normalize nt
  meta.constraints %=~ normalize nt
  meta.userVars %=~ normalize nt

instance Monad m => MonadNormalize (TCT m) where
  normalizeState = normalizeContext



--------------------------------------------------------------------------------------------------
-- Monad instance: LiftTC
--------------------------------------------------------------------------------------------------

newtype WrapMessageId a = WrapMessageId a
  deriving (Show)

instance ShowPretty a => ShowPretty (WrapMessageId a) where showPretty (WrapMessageId a) = showPretty a

instance (ShowLocated a) => ShowLocated (WrapMessageId a) where showLocated (WrapMessageId a) = showLocated a

instance (Monad m, Normalize TC a) => Normalize (TCT m) (WrapMessageId a) where
  normalize e (WrapMessageId x) = WrapMessageId <$> liftTC (normalize e x)

newtype WrapMessageRevId a = WrapMessageRevId a
  deriving (Show)
instance ShowPretty a => ShowPretty (WrapMessageRevId a) where showPretty (WrapMessageRevId a) = showPretty a
instance ShowLocated a => ShowLocated (WrapMessageRevId a) where showLocated (WrapMessageRevId a) = showLocated a

instance (Monad m) => Normalize (m) (WrapMessageRevId a) where
  normalize e x = pure x
    -- liftTC (normalize e x)


instance Monad m => Normalize (TCT m) DMTypeOps_Unary where
  normalize e x = pure x

instance Monad m => Normalize (TCT m) DMTypeOps_Binary where
  normalize e x = pure x

instance Monad m => Normalize (TCT m) DMTypeOp_Some where
  normalize e x = pure x


instance Monad m => LiftTC (TCT m) where
  liftTC (TCT v) = -- TCT (v >>= (lift . lift . return))
    let g :: DMPersistentMessage (TCT Identity) -> DMPersistentMessage (TCT m)
        g (DMPersistentMessage a) = DMPersistentMessage (WrapMessageId a)

        i :: LocatedDMException (TCT Identity) -> LocatedDMException (TCT m)
        i (WithContext e ctx) = WithContext e (g ctx)

        g' :: DMPersistentMessage (TCT m) -> DMPersistentMessage (TCT Identity)
        g' (DMPersistentMessage a) = DMPersistentMessage (WrapMessageRevId a)

        f :: DMMessages (TCT Identity) -> DMMessages (TCT m)
        f (DMMessages logs errors) = DMMessages logs (fmap i errors) 

        h :: forall a. Either (LocatedDMException (TCT Identity)) (a, Full (DMPersistentMessage (TCT Identity)))
              -> Either (LocatedDMException (TCT m)) (a, Full (DMPersistentMessage (TCT m)))
        h (Right (a,msg)) = Right (a, fmap g msg)
        h (Left (WithContext e ctx)) = Left (WithContext e (g ctx))

        -- x :: StateT (Full (TCT m)) (ExceptT (LocatedDMException (TCT m)) (WriterT (DMMessages (TCT m)) m)) a
        x = StateT (\s -> ExceptT (ReaderT $ \readstate -> (WriterT (return (bimap h f $ runWriter $ runReaderT (runExceptT $ runStateT v (fmap g' s)) readstate)))))

    in TCT x


--------------------------------------------------------------------------------------------------
-- Monad instance: MonadImpossible
--------------------------------------------------------------------------------------------------
instance Monad m => MonadImpossible (TCT m) where
  impossible err = throwUnlocatedError (ImpossibleError err)


--------------------------------------------------------------------------------------------------
-- Monad instance: MonadDMTC
--------------------------------------------------------------------------------------------------
instance Monad m => MonadDMTC (TCT m) where

instance Monad m => IsT MonadDMTC (TCT m) where


--------------------------------------------------------------------------------------------------
-- Normalization
--------------------------------------------------------------------------------------------------

instance (MonadDMTC t) => Normalize t (WithRelev e) where
  normalize nt (WithRelev i x) = WithRelev i <$> normalize nt x

instance (MonadDMTC t) => Normalize t (DMTypeOf k) where
  normalize nt n =
    do -- we apply all type variable substitutions
       σ <- getSubs @_ @DMTypeOf
       n₂ <- σ ↷ n

       -- and all sensitivity variables substitutions
       σ <- getSubs @_ @SensitivityOf
       n₃ <- σ ↷ n₂

       -- finally we normalize the uppermost "annotation" layer (if there is one)
       -- , i.e., compute {↷,∧,Trunc}-terms
       normalizeAnn nt n₃

instance (Normalize t a, Normalize t b) => Normalize t (a :@ b) where
  normalize nt (a :@ b) = (:@) <$> normalize nt a <*> normalize nt b

instance MonadDMTC t => Normalize (t) Sensitivity where
  normalize nt n =
    do σ <- getSubs @_ @SensitivityOf
       res <- σ ↷ n
       return $ normalizeSensSpecial nt res

instance Monad t => Normalize t (SymbolOf k) where
  normalize _ = pure

instance MonadDMTC t => Normalize t (Annotation a) where
  normalize nt (SensitivityAnnotation s) = SensitivityAnnotation <$> normalize nt s
  normalize nt (PrivacyAnnotation s) = PrivacyAnnotation <$> normalize nt s

instance (Monad t, Normalize t a) => Normalize t (Maybe a) where
  normalize _ Nothing = pure Nothing
  normalize nt (Just a) = Just <$> normalize nt a


instance (MonadDMTC t) => Normalize (t) DMTypeOp where
  normalize nt (Unary op τ res) = Unary op <$> normalize nt τ <*> normalize nt res
  normalize nt (Binary op τ res) = Binary op <$> normalize nt τ <*> normalize nt res

instance (MonadDMTC t) => Normalize t DMException where
  normalize nt x = pure x

instance Normalize m x => Normalize m (WithContext x m) where
  normalize nt (WithContext a msg) = WithContext <$> (normalize nt a) <*> pure msg

instance (MonadDMTC t => Normalize (t) a) => MonadDMTC t :=> Normalize (t) a where
  ins = Sub Dict

----------------------------------------------------------
-- normalization for annotated dmtypes

-- This is for evaluating the ∧, Trunc, ↷ constructors when it is known whether
-- we have a function or non function type.
-- We do not need a monad here.
truncateExtra :: (Eq e, CMonoidM Identity e, CMonoidM Identity f) => f -> e -> f
truncateExtra η η_old =
  (case η_old == zeroId of
      True -> zeroId
      _    -> η)


scaleExtra :: forall (a :: AnnotationKind). Sensitivity -> Annotation a -> Annotation a
scaleExtra η (SensitivityAnnotation s) = SensitivityAnnotation (η ⋅! s)
scaleExtra η (PrivacyAnnotation (ε, δ)) = PrivacyAnnotation (η ⋅! ε , η ⋅! δ)


normalizeAnn :: forall t k. NormalizationType -> (MonadDMTC t) => DMTypeOf k -> t (DMTypeOf k)
normalizeAnn nt (Fun as) = do
  let normalizeInside (f :@ annot) = (:@) <$> normalizeAnn nt f <*> pure annot
  Fun <$> mapM normalizeInside as
normalizeAnn nt (NoFun fs) = pure $ NoFun fs
normalizeAnn nt (a :∧: b) | a == b = return a
normalizeAnn nt (a :∧: b) = do
  a' <- normalizeAnn nt a
  b' <- normalizeAnn nt b

  let makeNoFunInf :: DMTypeOf NoFunKind -> DMTypeOf NoFunKind -> t (DMMain)
      makeNoFunInf x y = do
        -- NOTE: Instead of taking the infimum of x and y we simply
        --       unify them. This is allowed and necessary for type-propagation
        --       to work. I.e, if we put an `a :: Int` into a function f(a) which
        --       might use a multiple times, then we want all those occurences to
        --       receive the actual type `Int`.
        --
        -- z <- newVar
        -- addConstraintNoMessage (Solvable (IsInfimum ((x, y) :=: z)))
        -- return (NoFun z)
        -- addConstraintNoMessage (Solvable (IsEqual (x,y)))

        unify ("During normalization of the type " :<>: (a :∧: b)) x y
        return (NoFun x)

  case (a', b') of
    (Fun xs, Fun ys) -> pure $ Fun (xs <> ys)
    (NoFun x, NoFun y) -> makeNoFunInf x y
    (NoFun x, TVar y) -> do
      y' <- newVar
      addSub (y := NoFun y')
      makeNoFunInf x y'
    (TVar x, NoFun y) -> do
      x' <- newVar
      addSub (x := NoFun x')
      makeNoFunInf x' y
    (NoFun x, Fun y) -> throwUnlocatedError (UnificationError (NoFun x) (Fun y))
    (Fun x, NoFun y) -> throwUnlocatedError (UnificationError (Fun x) (NoFun y))
    (_ , _) -> return (a' :∧: b')
normalizeAnn nt (xs :->: y) = do
  let normalizeInside (x :@ annot) = (:@) <$> normalizeAnn nt x <*> pure (normalizeSensSpecial nt annot)
  (:->:) <$> mapM normalizeInside xs <*> normalizeAnn nt y
normalizeAnn nt (xs :->*: y) = do
  let normalizeInside (x :@ (annot0, annot1)) = (:@) <$> normalizeAnn nt x <*> pure (normalizeSensSpecial nt annot0, normalizeSensSpecial nt annot1)
  (:->*:) <$> mapM normalizeInside xs <*> normalizeAnn nt y
normalizeAnn nt x = recDMTypeM (normalizeAnn nt) (pure . normalizeSensSpecial nt) x




--------------------------------------------------------------------------------------------------
-- unification of sensitivities
--------------------------------------------------------------------------------------------------

-- Before we can unify dmtypes, we have to proof that we can unify
-- sensitivities.
-- We unify them simply by adding an equality constraint. That this
-- constraint is solvable in any class of monads, in particular in MonadDMTC,
-- is shown in Abstract.Data.MonadicPolynomial.
--
instance MonadDMTC t => Unify (WithContext DMException) t Sensitivity where
  unify_ msg s1 s2 = do
    c <- addConstraint (Solvable (IsEqual (s1, s2))) msg
    return s1

instance (Monad t, Unify (WithContext DMException) t a, Unify (WithContext DMException) t b) => Unify (WithContext DMException) t (a,b) where
  unify_ name (a1,b1) (a2,b2) = (,) <$> (unify_ name a1 a2) <*> (unify_ name b1 b2)

instance (MonadDMTC t, Show a, Unify (WithContext DMException) t a) => Unify (WithContext DMException) t (Maybe a) where
  unify_ name Nothing Nothing = pure Nothing
  unify_ name (Just a) (Just b) = Just <$> unify_ name a b
  unify_ name t s = throwUnlocatedError (UnificationError t s)



