{-# LANGUAGE TemplateHaskell #-}

{- |
Description: Preprocessing step to turn a (procedural) pure `DemutDMTerm` into a properly functional `DMTerm`.
-}
module DiffMu.Typecheck.Preprocess.Unblock where

import DiffMu.Prelude
import DiffMu.Abstract
import DiffMu.Core
import DiffMu.Core.Logging
import DiffMu.Typecheck.Preprocess.Common

import Debug.Trace
import qualified Data.Text as T

-----------------------------------------------------------------------------------
-- preprocessing step to make procedural "blocks" of statements into nice nested DMTerms.
-- 

type BlockTC = LightTC Location_PrePro_Demutation ()

unblockingError err msg = throwLocatedError (UnblockingError err) msg

unblock :: LocDemutDMTerm -> BlockTC LocDMTerm
unblock = unblockValue


unblockValue :: LocDemutDMTerm -> BlockTC LocDMTerm
unblockValue (Located l (Extra e)) = case e of
  DemutBlock []       -> unblockingError "Found an empty block where a value was expected." l
  DemutBlock (x:xs)   -> unblockStatementsM (unblockValue x) xs
  DemutPhi cond tr fs -> Located l <$> (Phi <$> (unblock cond) <*> (unblock tr) <*> (unblock fs)) -- a phi that has no tail
  _                   -> unblockingError ("Found a statement without return value. This is not allowed.")
                           (l :\\:
                            ("Statement:\n" <> (showPretty e))
                           )
unblockValue t = recDMTermM_Loc unblockValue (\(Located l x) -> unblock (Located l (Extra x))) t


unblockStatementsM :: BlockTC LocDMTerm -> [LocDemutDMTerm] -> BlockTC LocDMTerm
unblockStatementsM mlast xs = join $ unblockStatements <$> mlast <*> pure xs

unblockStatements :: LocDMTerm -> [LocDemutDMTerm] -> BlockTC LocDMTerm
unblockStatements last [] = pure last
unblockStatements last (Located l (Extra (DemutBlock bs))             : xs) = unblockStatementsM (unblockStatements last bs) xs
unblockStatements last (Located l (Extra (DemutPhi c t f))            : xs) = unblockStatementsM (Located l <$> (Phi <$> (unblock c) <*> (unblockStatements last [t]) <*> (unblockStatements last [f]))) xs
unblockStatements last (Located l (Extra (DemutSLetBase k a b))       : xs) = unblockStatementsM (Located l <$> (SLetBase k a <$> (unblock b) <*> pure last)) xs
unblockStatements last (Located l (Extra (DemutTLetBase k a b))       : xs) = unblockStatementsM (Located l <$> (TLetBase k a <$> (unblock b) <*> pure last)) xs
unblockStatements last (Located l (Extra (DemutFLet a b))             : xs) = unblockStatementsM (Located l <$> (FLet a <$> (unblock b) <*> pure last)) xs
unblockStatements last (Located l (Extra (DemutBBLet a b))            : xs) = unblockStatements (Located l $ BBLet a b last) xs
unblockStatements last (Located l (Extra (DemutLoop (n1,n2,n3) cvars cvars' it body)) : xs) =
        unblockStatementsM (Located l <$> (TLet cvars' <$> (Located l <$> (Loop <$> ((,,) <$> unblock n1 <*> unblock n2 <*> unblock n3) <*> pure cvars <*> pure it <*> (unblock body))) <*> pure last)) xs

unblockStatements last (x                                   : xs) = unblockingError ("Expected a statement, but encountered a term.")
                                                                     (getLocation last :\\:
                                                                      ("term:\n"
                                                                      <> (showPretty x))
                                                                     )

