
{- |
Description: Definition of all constraints.
-}
module DiffMu.Typecheck.Constraint.Definitions where

import DiffMu.Prelude
import DiffMu.Abstract.Data.Error
import DiffMu.Abstract.Class.IsT
import DiffMu.Abstract.Class.Constraint

import Debug.Trace
import Data.HashMap.Strict (HashMap)

--------------------------------------------------------------------------
-- Constraints
--
-- Constraints are axiomatized as wrappers around their content. Every kind
-- of constraint *is* its own wrapper type, that is, we have:
--
-- IsEqual :: Type -> Type
-- IsLessEqual :: Type -> Type
-- IsTypeOpResult :: Type -> Type
-- ...
--
-- And usually these wrappers have constructors of the same name as their type,
-- i.e., we have, forall a:
--
--  Term constructor
--   |               Type constructor
--   |                |
--   v                v
-- IsEqual :: a -> IsEqual a
-- IsLessEqual :: a -> IsLessEqual a
-- IsTypeOpResult :: a -> IsTypeOpResult a
-- ...
--
-- For example, we have:
newtype IsTypeOpResult a = IsTypeOpResult a
  deriving (Show, Eq)
--
-- The idea is that `a` represents the data which is the actual content which needs
-- to be solved by this constraint, and the type of the wrapper around it tells us
-- what kind of constraint this is.
-- For example, it makes sens to have `IsEqual (DMType,DMType)` or `IsMaximum (Sensitivity,Sensitivity,Sensitivity)`
-- or `IsTypeOpResult DMTypeOp`.
--
-- Having the generic type parameter a allows us to treat all constraints equally,
-- in cases where we are writing generic code for dealing with any kind of constraints.
-- In order for this to work, we have to prove that our "constraint type" is nothing
-- but a wrapper around `a`. For this, we show that it is an instance of the `TCConstraint`
-- type class, for example:
instance TCConstraint IsTypeOpResult where
  constr = IsTypeOpResult
  runConstr (IsTypeOpResult c) = c
  -- where
  --
  -- `constr` :: a -> c a
  --  requires that we can put our "data" into the constraint.
  --
  -- `runConstr` :: c a -> a
  --  requires that we can extract our "data" from the constraint.
--
--
-- There are two further type classes associated with constraints:
-- 1. Constraints exist in order to be solved. This is axiomatized by the typeclass
--    `Solve isT c a`, which says that the class of monads described by `isT`
--    (e.g., `isT := MonadDMTC`) can solve constraints of (wrapper-)type `c`
--    with data `a`.
--
--    For example, we have the instance `Solve MonadDMTC IsTypeOpResult DMTypeOp`
--    (see in DiffMu.Typecheck.Operations).
--    But also `Solve MonadDMTC IsEqual (DMTypeOf k)`, for any k.
--    (see in DiffMu.Core.Unification).
--    These instances implement the `solve_` function which runs in the `MonadDMTC` monad
--    and tries to solve the constraint.
--
--    NOTE: we use a class of monads `isT` here, instead of a specific monad `t` here, because
--          of the following problem: It should be possible to add a constraint while in the
--          sensitivity typechecking monad (`TC Sensitivity a`) but solve it in the privacy monad.
--          Thus we define "solvability" for the whole class of TC like monads at once.
--          That is, for the class `MonadDMTC`.
--
-- 2. While typechecking (and/or solving constraints) we sometimes have to add new constraints.
--    The typeclass `MonadConstraint isT t` expresses that the monad `t` allows us to
--    add, discharge or update constraints which are solvable by monads in the class `isT`.
--    All monads in the `MonadDMTC` class are instances of `MonadConstraint MonadDMTC`.
--
--    But to reiterate: the Haskell type system only allows to add a constraint `c`, via
--    ```
--    do addConstraint (Solvable (c))
--    ```
--    if there is an instance of `Solve isT c a` currently in scope.
--
--
-- NOTE: The basic constraints definitions for equality/less-equal are located
--       in Abstract.Class.Constraint.
--       Here, also the definition of `Solvable` and `MonadConstraint` is to be found.

instance ShowPretty a => ShowPretty (IsTypeOpResult (a)) where
    showPretty (IsTypeOpResult (a)) = showPretty a


-- Equal (solver in Core/Unification.hs):
newtype IsEqual a = IsEqual a
  deriving (Show, Eq)

instance TCConstraint IsEqual where
  constr = IsEqual
  runConstr (IsEqual c) = c

instance ShowPretty a => ShowPretty (IsEqual (a,a)) where
    showPretty (IsEqual (a,b)) = showPretty a <> " and " <> showPretty b <> " must be equal"
        
-------------------------------------------------------------------
-- Subtyping (solver in Typecheck/Subtyping.hs)
-------------------------------------------------------------------

---- Less Equal (both subtyping and sensitivity, actually. sensitivity version lives in Unification.hs)
newtype IsLessEqual a = IsLessEqual a
  deriving (Show, Eq)

instance TCConstraint IsLessEqual where
  constr = IsLessEqual
  runConstr (IsLessEqual c) = c


---- Sups
newtype IsSupremum a = IsSupremum a deriving (Show, Eq)

instance TCConstraint IsSupremum where
  constr = IsSupremum
  runConstr (IsSupremum c) = c

instance ShowPretty a => ShowPretty (IsSupremum ((a,a) :=: a)) where
    showPretty (IsSupremum ((a,b) :=: c)) = "Type " <> showPretty c <> " is the supremum of types " <> showPretty a <> " and " <> showPretty b
        

---- Infimum
newtype IsInfimum a = IsInfimum a deriving (Show, Eq)

instance TCConstraint IsInfimum where
  constr = IsInfimum
  runConstr (IsInfimum c) = c
  
instance ShowPretty a => ShowPretty (IsInfimum ((a,a) :=: a)) where
    showPretty (IsInfimum ((a,b) :=: c)) = "Type " <> showPretty c <> " is the infimum of types " <> showPretty a <> " and " <> showPretty b
        

-------------------------------------------------------------------
-- Function calls and choice resolution (solver in Typecheck/Constraint/IsFunctionArgument.hs)
-------------------------------------------------------------------

---- Choices
newtype IsChoice a = IsChoice a deriving (Show, Eq)

instance TCConstraint IsChoice where
  constr = IsChoice
  runConstr (IsChoice c) = c

newtype IsFunctionArgument a = IsFunctionArgument a deriving (Show, Eq)

instance TCConstraint IsFunctionArgument where
  constr = IsFunctionArgument
  runConstr (IsFunctionArgument c) = c

instance (ShowPretty a) => ShowPretty (IsFunctionArgument (a,a)) where
    showPretty (IsFunctionArgument (a,b)) = "Function type " <> newlineIndentIfLong (showPretty b)
                                            <> "was used in a function application where function type " <> newlineIndentIfLong (showPretty a)
                                            <> "was expected"

-------------------------------------------------------------------
-- Julia Types (solver in Typecheck/Constraint/IsJuliaEqual.hs)
-------------------------------------------------------------------

-------------------------------------------------------------------
-- set the a type to non-const, in case it's numeric or a tuple.
--

newtype IsNonConst a = IsNonConst a deriving (Show, Eq)

instance TCConstraint IsNonConst where
  constr = IsNonConst
  runConstr (IsNonConst c) = c

instance ShowPretty a => ShowPretty (IsNonConst (a,a)) where
    showPretty (IsNonConst (a,b)) = "Type " <> showPretty b <> " is the non-static version of " <> showPretty a

-------------------------------------------------------------------
-- Mostly unify two types, but when encountering const / non-const
-- things behave like subtyping.
--

newtype UnifyWithConstSubtype a = UnifyWithConstSubtype a deriving (Show, Eq)

instance TCConstraint UnifyWithConstSubtype where
  constr = UnifyWithConstSubtype
  runConstr (UnifyWithConstSubtype c) = c

instance ShowPretty a => ShowPretty (UnifyWithConstSubtype (a,a)) where
    showPretty (UnifyWithConstSubtype (a,b)) = "Types " <> showPretty a <> " and " <> showPretty b <> " are equal except for static-ness, where the fist is a subtype of the second"

-----------------------------------------------------------------
-- Fake julia types
--
-- We do not have a real "julia type layer" for now. Since our types
-- mostly only differ from the julia types by having the singleton const types,
-- we have a constraint which checks this by unifying after making variables non-const
-- if possible.

newtype IsJuliaEqual a = IsJuliaEqual a deriving (Show, Eq)

instance TCConstraint IsJuliaEqual where
  constr = IsJuliaEqual
  runConstr (IsJuliaEqual c) = c

instance ShowPretty a => ShowPretty (IsJuliaEqual (a,a)) where
    showPretty (IsJuliaEqual (a,b)) = "Types " <> showPretty a <> " and " <> showPretty b <> " describe the same julia type"

----------------------------------------------------------------
-- Things that should be functions

newtype IsFunction a = IsFunction a deriving (Show, Eq)

instance TCConstraint IsFunction where
  constr = IsFunction
  runConstr (IsFunction c) = c

instance (ShowPretty a, ShowPretty b) => ShowPretty (IsFunction (a,b)) where
    showPretty (IsFunction (a,b)) = "Type " <> showPretty b <> " is a " <> showPretty a <> "-function"
    
-------------------------------------------------------------------
-- Cheap Constraints (solver in Typecheck/Constraint/CheapConstraints.hs)
-------------------------------------------------------------------



-------------------------------------------------------------------
--  Less (for sensitivities)
--

newtype IsLess a = IsLess a
  deriving (Show, Eq)

instance TCConstraint IsLess where
  constr = IsLess
  runConstr (IsLess c) = c


instance ShowPretty a => ShowPretty (IsLess (a,a)) where
    showPretty (IsLess (a,b)) = showPretty a <> " < " <> showPretty b
        

-------------------------------------------------------------------
-- set the a type to a variable const, in case it's numeric or a tuple.
--

newtype MakeConst a = MakeConst a deriving (Show, Eq)

instance TCConstraint MakeConst where
  constr = MakeConst
  runConstr (MakeConst c) = c

instance ShowPretty a => ShowPretty (MakeConst (a,b)) where
    showPretty (MakeConst (a,_)) = "If type " <> showPretty a <> " is numeric or a tuple, it can become static"
        

----------------------------------------------------------
-- replacing all Numeric TVars by non-const


newtype MakeNonConst a = MakeNonConst a deriving (Show, Eq)

instance TCConstraint MakeNonConst where
  constr = MakeNonConst
  runConstr (MakeNonConst c) = c

instance ShowPretty a => ShowPretty (MakeNonConst (a,b)) where
    showPretty (MakeNonConst (a,_)) = "All Numeric types in " <> showPretty a <> " will be set non-static"
        

-------------------------------------------------------------------
-- is it Loop or static Loop (i.e. is no of iterations const or not)

newtype IsLoopResult a = IsLoopResult a deriving (Show, Eq)

instance TCConstraint IsLoopResult where
  constr = IsLoopResult
  runConstr (IsLoopResult c) = c

instance (ShowPretty a, ShowPretty b, ShowPretty c) => ShowPretty (IsLoopResult (a,b,(c,c,c))) where
    showPretty (IsLoopResult (a,b,(c1,c2,c3))) = "Sensitivities " <> showPretty a <> " are dependant on whether number of iterations in "
                                        <> showPretty c1 <> ":" <> showPretty c2 <> ":" <> showPretty c3 <> " is static. Loop body has sensitivity " <> showPretty b

--------------------------------------------------
-- is it gauss or mgauss?
--

newtype IsAdditiveNoiseResult a = IsAdditiveNoiseResult a deriving (Show, Eq)

instance TCConstraint IsAdditiveNoiseResult where
  constr = IsAdditiveNoiseResult
  runConstr (IsAdditiveNoiseResult c) = c

instance (ShowPretty a, ShowPretty b) => ShowPretty (IsAdditiveNoiseResult (a,b)) where
    showPretty (IsAdditiveNoiseResult (a,b)) = "Type " <> showPretty a <> " is the result of an additive noise mechanism executed on " <> showPretty b

--------------------------------------------------
-- projecting of tuples

newtype IsTProject a = IsTProject a deriving (Show, Eq)

instance TCConstraint IsTProject where
  constr = IsTProject
  runConstr (IsTProject c) = c

instance (ShowPretty a) => ShowPretty (IsTProject ((Int , a) :=: a)) where
    showPretty (IsTProject ((i , t) :=: e)) = "Type " <> showPretty t <> " is a tuple whose " <> showPretty i <> "-th entry has type " <> showPretty e

--------------------------------------------------
-- black boxes

newtype IsBlackBox a = IsBlackBox a deriving (Show, Eq)

instance TCConstraint IsBlackBox where
  constr = IsBlackBox
  runConstr (IsBlackBox c) = c

instance (ShowPretty a, ShowPretty b) => ShowPretty (IsBlackBox (a,b)) where
    showPretty (IsBlackBox (a,b)) = "Black box function " <> showPretty a <> " is applied to arguments " <> showPretty b



newtype IsBlackBoxReturn a = IsBlackBoxReturn a deriving (Show, Eq)

instance TCConstraint IsBlackBoxReturn where
  constr = IsBlackBoxReturn
  runConstr (IsBlackBoxReturn c) = c

instance (ShowPretty a, ShowPretty b) => ShowPretty (IsBlackBoxReturn (a,b)) where
    showPretty (IsBlackBoxReturn (a,b)) = "Type " <> showPretty a <> " is an argument of a black box, its sensitivity " <> showPretty b <> "can be set accordingly"



--------------------------------------------------
-- matrix or vector

newtype IsVecOrMat a = IsVecOrMat a deriving (Show, Eq)

instance TCConstraint IsVecOrMat where
  constr = IsVecOrMat
  runConstr (IsVecOrMat c) = c

instance ShowPretty a => ShowPretty (IsVecOrMat (a)) where
    showPretty (IsVecOrMat (a)) = "Type " <> showPretty a <> " must be a vector or matrix"


--------------------------------------------------
-- gradient or vector or 1d-matrix
--

newtype IsVecLike a = IsVecLike a deriving (Show, Eq)

instance TCConstraint IsVecLike where
  constr = IsVecLike
  runConstr (IsVecLike c) = c


instance ShowPretty a => ShowPretty (IsVecLike (a)) where
    showPretty (IsVecLike (a)) = "Type " <> showPretty a <> " must be a vector, gradient or one-row matrix"

--------------------------------------------------
-- container norm conversion
--

newtype ConversionResult a = ConversionResult a deriving (Show, Eq)

instance TCConstraint ConversionResult where
  constr = ConversionResult
  runConstr (ConversionResult c) = c


instance (ShowPretty a, ShowPretty b) => ShowPretty (ConversionResult (a,a,b,b)) where
    showPretty (ConversionResult (a,b,c,d)) = "Converted norm " <> showPretty a <> " to norm " <> showPretty b <> " on an " <> showPretty c <> "-row container, "
                                        <> " incurring conversion penalty is " <> showPretty d
