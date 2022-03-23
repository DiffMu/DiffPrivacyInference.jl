
{-# LANGUAGE TemplateHaskell #-}

module DiffMu.Typecheck.Preprocess.LexicalScoping where

import DiffMu.Prelude
import DiffMu.Abstract
import DiffMu.Core
import DiffMu.Core.Logging
import DiffMu.Typecheck.Preprocess.Common

import qualified Data.HashMap.Strict as H

import qualified Data.Text as T
import Data.Foldable

import Debug.Trace

-----------------------------------------------------------------------------------
-- preprocessing step to make function argument names unique

data LSFull = LSFull
  {
    _termVarsOfLS :: NameCtx
  }

-- the monad keeping the state we require to generate unique names
type LSTC = LightTC Location_PrePro_Demutation LSFull

$(makeLenses ''LSFull)

-- generate unique new variables
newTeVar :: (MonadState LSFull m) => TeVar -> m TeVar
newTeVar t = newTeVarOfLS t

-- generate unique new variables
newTeVarOfLS :: (MonadState LSFull m) => TeVar -> m (TeVar)
newTeVarOfLS hintVar = termVarsOfLS %%= (first (\x -> GenTeVar x (Just hintVar)) . (newName (hint hintVar)))
  where
    hint (GenTeVar (Symbol x) _)   = x <> "_genls"
    hint (UserTeVar (x))         = T.pack (show x) <> "_uls"

-- transform the dmterm to one where function argument names are unique
-- by generating new names for them and substituting all occurances in the body
processLS :: LocDMTerm -> LSTC (LocDMTerm)
processLS t = substituteNames H.empty t

-- in a dmterm, apply all variable name substitutions contained in the hashmap recursively.
substituteNames :: H.HashMap TeVar TeVar -> LocDMTerm -> LSTC LocDMTerm
substituteNames names (Located l term) = let
    subIf c = case H.lookup c names of
                    Nothing -> c
                    Just newc -> newc
    subAsgmt (x :- t) = ((subIf x) :- t)
    subSame t = substituteNames names t

    ret x = return $ Located l x
  in case term of
   -- function argument variables are renamed to sth unique and substituted in the body
   Lam args retjt body -> do
       let argnames = [x | (x :- _) <- args]
       newnames <- mapM newTeVar argnames -- generate new names for all argument variables
       let names' = H.union (H.fromList (zip [n | n <- argnames] [n | n <- newnames])) names -- overwrite hashmap with new names
       newbody <- substituteNames names' body -- substitute new names in the body
       ret (Lam [(x :- t) | (x, (_ :- t)) <- (zip newnames args)] retjt newbody)
   LamStar args retjt body -> do
       let argnames = [x | (x :- _) <- args]
       newnames <- mapM newTeVar argnames -- generate new names for all argument variables
       let names' = H.union (H.fromList (zip [n | n <- argnames] [n | n <- newnames])) names -- overwrite hashmap with new names
       newbody <- substituteNames names' body -- substitute new names in the body
       ret (LamStar [(x :- t) | (x, (_ :- t)) <- (zip newnames args)] retjt newbody)
   -- args/vars are simply substituted
   Arg x t r -> case H.lookup x names of
       Nothing -> ret term
       Just name -> ret (Arg name t r)
   Var x -> case H.lookup x names of
       Nothing -> ret term
       Just name -> ret (Var name)
   BBLet x ts tail -> case H.lookup x names of
       Just _            -> internalError "black boxes should have unique names..."
       Nothing           -> Located l <$> BBLet x ts <$> subSame tail
   BBApply t args caps k -> Located l <$> (BBApply <$> subSame t <*> (mapM subSame args) <*> (return (map subIf caps)) <*> recKindM (substituteNames names) k)
   FLet f t tail         -> Located l <$> (FLet (subIf f) <$> subSame t <*> subSame tail)
   -- the following 2 are only ok bc i cannot modify names from outer scope
   SLetBase k x body tail -> Located l <$> (SLetBase k (subIf x) <$> subSame body <*> subSame tail)
   TLetBase k ns body tail       -> Located l <$> (TLetBase k (map subIf ns) <$> subSame body <*> subSame tail)
   MCreate t1 t2 (x1, x2) t3     -> Located l <$> (MCreate <$> subSame t1 <*> subSame t2 <*> return (subIf x1, subIf x2) <*> subSame t3)
   Loop t1 cs (x1, x2) body      -> Located l <$> (Loop <$> subSame t1 <*> return (map subIf cs) <*> return (subIf x1, subIf x2) <*> subSame body)
   _ -> recDMTermMSameExtension_Loc (substituteNames names) (Located l term)
