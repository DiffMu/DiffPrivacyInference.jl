
{-# LANGUAGE TemplateHaskell #-}

{- |
Description: The third parsing step: `JExpr` -> `LocProcDMTerm`.
-}
module DiffMu.Parser.JExprToDMTerm where
    
import DiffMu.Prelude
import DiffMu.Abstract
import DiffMu.Core
import DiffMu.Core.Logging
import DiffMu.Core.TC
import DiffMu.Parser.FromString
import DiffMu.Typecheck.Preprocess.Common
import qualified Data.Text as T
import qualified Prelude as P

import Debug.Trace

import qualified Data.HashMap.Strict as H

data ParseFull = ParseFull
  {
    _location :: (Maybe String, Int, Int), -- filename and line number and line number of next term
    _outerFuncNames :: [Symbol], -- to error upon non-toplevel back box definitions and simple recursion
    _insideAssignment :: Bool, -- to error upon assignemnts within assignments (like x = y = 100).
    _holeNames :: NameCtx -- generate new names for holes
  }

instance Default ParseFull where
    def = ParseFull (Nothing,0,0) [] False def

type ParseTC = LightTC Location_Parse ParseFull

$(makeLenses ''ParseFull)

holeVar :: ParseTC ProcVar
holeVar = holeNames %%= (first GenProcVar . (newName GeneratedNamePriority "hole"))


newProcVar :: Symbol -> ParseTC (ProcVar)
newProcVar (Symbol name) = case H.member name builtins of
                                False -> pure (UserProcVar (Symbol name))
                                True -> parseError $ "Overwriting builtin function name " <> show name <> " is not permitted."

parseError :: String -> ParseTC a
parseError message = do
                       (file, line, next) <- use location
                       loc <- getCurrentLoc
                       throwError (withContext (ParseError message file line next) loc)
                        

-- set parse state to be inside a function
enterFunction :: (MonadState ParseFull m) => Symbol -> m ()
enterFunction s = outerFuncNames %%= (\fs -> ((), s:fs))

-- set parse state to be outside a function
exitFunction :: (MonadState ParseFull m) => m ()
exitFunction = outerFuncNames %%= (\fs -> ((), drop 1 fs))

-- set parse state to be inside an assignment
enterAssignment :: (MonadState ParseFull m) => m ()
enterAssignment = insideAssignment .= True

-- set parse state to be outside a function
exitAssignment :: (MonadState ParseFull m) => m ()
exitAssignment = insideAssignment .= False

getCurrentLoc :: (MonadState ParseFull m) => m SourceLocExt
getCurrentLoc = do
  (file,line,nextline) <- use location
  return $ ExactLoc (SourceLoc (SourceFile file) line nextline)


pSingle_Loc :: JExpr -> ParseTC LocProcDMTerm
pSingle_Loc e = do
  loc <- getCurrentLoc
  val <- pSingle e
  return (Located loc val)

pSingle :: JExpr -> ParseTC ProcDMTerm
pSingle e = case e of
                 JEInteger n -> pure $ Sng n JTInt
                 JETrue -> pure $ DMTrue
                 JEFalse -> pure $ DMFalse
                 JEReal r -> pure $ Sng r JTReal
                 JESymbol (Symbol s) -> case H.member s builtins of
                                    False -> return  (Extra (ProcVarTerm (UserProcVar (Symbol s))))
                                    True  -> parseError $ "Builtin function " <> show s <> " cannot be used as function variables. Please wrap them in a lambda term"
                 JETup elems -> (Tup <$> (mapM pSingle_Loc elems))
                 JERef name refs -> pJRef name refs
                 JECall name args -> pJCall name args
                 
                 JEBlock stmts -> do
                     l <- pList stmts
                     case l of
                          [] -> parseError "Found an empty block."
                          _ -> Extra <$> (Block <$> pure l)
                 JELam args ret body -> pJLam args ret body ProcLam
                 JELamStar args ret body -> pJLam args ret body ProcLamStar
                 JEIfElse cond tr fs -> Extra <$> (ProcPhi <$> (pSingle_Loc cond) <*> (pSingle_Loc tr) <*> (mapM pSingle_Loc fs))
                 JELoop ivar iter body -> pJLoop ivar iter body
                 JEAssignment aee amt -> pJLet aee amt
                 JETupAssignment aee amt -> pJTLet aee amt
                 JEFunction name term -> pJFLet name term
                 JEBlackBox name args -> pJBlackBox name args
                 JEBBCall name args rt size -> pJBBCall name args rt size
                 JEReturn -> pure $ Extra ProcReturn

                 JEHole -> parseError "Holes (_) are only allowed in assignments."
                 JEUnsupported s -> parseError ("Unsupported expression " <> show s)
                 JEIter _ _ _ -> parseError ("Iterators can only be used in for-loop statements directly.")
                 JEColon -> parseError "Colon (:) can only be used to access matrix rows like in M[1,:], or to define iterator ranges like in a:b."
                 JETypeAnnotation _ _ -> parseError "Type annotations are only supported on function arguments or as function return types."
                 JENotRelevant _ _ -> parseError "Type annotations are only supported on function arguments or as function return types."
                 JELineNumber _ _ _ -> throwUnlocatedError (InternalError "What now?") -- TODO
                 JEImport -> parseError "`import` statement is not allowed here."
                 JEUse -> parseError "`using` statement is not allowed here."



pList :: [JExpr] -> ParseTC [LocProcDMTerm]
pList [] = pure []
pList (JEBlock stmts : tail) = pList (stmts ++ tail) -- handle nested blocks
pList (JEImport : tail) = pList tail -- ignore imports
pList (JEUse : tail) = pList tail -- ignore "using DiffPrivacyInference"
pList (s : tail) = do
    ps <- case s of
               JELineNumber file line nextline -> location .= (file, line, nextline) >> return Nothing
               _ -> Just <$> (pSingle_Loc s)
    ptail <- pList tail
    case ps of
        Nothing -> return ptail
        Just pps -> return (pps : ptail)


pJRef name refs = case refs of
                       [i1,JEColon] -> do
                                       t1 <- pSingle_Loc i1
                                       referee <- pSingle_Loc name
                                       return (Row referee t1)
                       [JEColon,_] -> parseError "Acessing columns of matrices using : is not permitted, you can only do that for rows."
                       [i1,i2] -> do
                                  t1 <- pSingle_Loc i1
                                  t2 <- pSingle_Loc i2
                                  referee <- pSingle_Loc name
                                  return (Index referee t1 t2)
                       [i] -> do -- single indices are only allowed for vectors
                                  t <- pSingle_Loc i
                                  referee <- pSingle_Loc name
                                  return (VIndex referee t)
                       _ -> parseError ("Only double indexing to matrix elements and single indexing to vector entries supported, but you gave " <> show refs)

pArg arg = case arg of
                     JEHole -> (::- JTAny) <$> holeVar
                     JESymbol s -> (::- JTAny) <$> (newProcVar s)
                     JETypeAnnotation (JESymbol s) τ -> (::- τ) <$> (newProcVar s)
                     JENotRelevant _ _ -> parseError ("Relevance annotation on a sensitivity function is not permitted.")
                     a -> parseError ("Invalid function argument " <> show a <> ". Expected a symbol, optionally with type annotation, or a hole (_).")

pArgRel arg = case arg of
                       JEHole -> (::- (JTAny, IsRelevant)) <$> holeVar
                       JESymbol s -> (::- (JTAny, IsRelevant)) <$> (newProcVar s)
                       JETypeAnnotation (JESymbol s) τ -> (::- (τ, IsRelevant)) <$> (newProcVar s)
                       JENotRelevant (JESymbol s) τ -> (::- (τ, NotRelevant)) <$> (newProcVar s)
                       a -> parseError ("Invalid function argument " <> show a <> ". Expected a symbol, optionally with type annotation, or a hole (_).")


pJLam args ret body ctor = do
                   dargs <- mapM pArgRel args
                   dbody <- pSingle_Loc body
                   return (Extra (ctor dargs ret dbody))


pJLoop ivar iter body = case iter of
       JEIter start step end -> do
                                 dbody <- pSingle_Loc body
                                 dstart <- pSingle_Loc start
                                 dstep <- pSingle_Loc step
                                 dend <- pSingle_Loc end
                                 i <- case ivar of
                                              JEHole -> holeVar
                                              JESymbol s -> newProcVar s
                                              i -> parseError ("Invalid iteration variable " <> (show i) <> ". Expected a symbol.")
                                 return (Extra (ProcPreLoop (dstart, dstep, dend) i dbody))
       it -> parseError ("Invalid iterator " <> show it <> ", must be a range (i.e. of the form a:b or a:s:b).")


pJLet assignee assignment = do
   inside <- use insideAssignment
   case inside of
        True -> parseError ("Assignments within assignments are forbidden, but variable " <> show assignee <> " is assigned to.")
        False -> do
                   enterAssignment
                   dasgmt <- pSingle_Loc assignment
                   exitAssignment
                   case assignee of
                        JEHole     -> (\p -> Extra (ProcSLetBase PureLet p dasgmt)) <$> holeVar
                        JESymbol s -> do
                            v <- newProcVar s
                            return (Extra (ProcSLetBase  PureLet v dasgmt))
                        JETypeAnnotation _ _ -> parseError "Type annotations on variables are not supported."
                        JENotRelevant _ _    -> parseError "Type annotations on variables are not supported."
                        _                    -> parseError ("Invalid assignee " <> (show assignee) <> ", must be a symbol.")


pJTLet :: [JExpr] -> JExpr -> ParseTC ProcDMTerm
pJTLet assignees assignment = let
   pSample args = case args of
                    [n, m1, m2] -> do
                                     tn <- pSingle_Loc n
                                     tm1 <- pSingle_Loc m1
                                     tm2 <- pSingle_Loc m2
                                     return (Located (NotImplementedLoc "Sample location") (Sample tn tm1 tm2))
                    _ -> parseError ("Invalid number of arguments for `sample`, namely " <> (show (length args)) <> " instead of 2.")
                    
   -- make sure that all assignees are simply symbols
   ensureSymbol (JESymbol s) = newProcVar s
   ensureSymbol JEHole = holeVar
   ensureSymbol (JETypeAnnotation _ _) = parseError "Type annotations on variables are not supported."
   ensureSymbol (JENotRelevant _ _) = parseError "Type annotations on variables are not supported."
   ensureSymbol x = parseError ("Invalid assignee " <> (show x) <> ", must be a variable.")

   in do
      inside <- use insideAssignment
      case inside of
           True -> parseError ("Assignments within assignments are forbidden, but variables " <> show assignees <> " are assigned to.")
           False -> do
                      assignee_vars <- mapM ensureSymbol assignees

                      case assignment of
                                        JECall (JESymbol (Symbol "sample")) args -> do
                                               smp <- pSample args
                                               return (Extra (ProcTLetBase SampleLet assignee_vars smp))
                                        _ -> do  -- parse assignment, tail; and build term
                                               enterAssignment
                                               dasgmt <- pSingle_Loc assignment
                                               exitAssignment
                                               return (Extra (ProcTLetBase PureLet assignee_vars dasgmt))


pJFLet name assignment =
  case name of
    JESymbol (Symbol n) -> case H.member n builtins of
                                True -> parseError $ "Adding methods to/replacing builtin function " <> show n <> " is not permitted."
                                False -> do
                                   enterFunction (Symbol n)
                                   dasgmt <- pSingle_Loc assignment
                                   exitFunction
                                   return (Extra (ProcFLet (UserProcVar (Symbol n)) dasgmt))
    _ -> parseError $ "Invalid function name expression " <> show name <> ", must be a symbol."


pJBlackBox name args =
  case name of
    JESymbol (Symbol n) -> case H.member n builtins of
                                True -> parseError $ "Adding methods to/replacing builtin function " <> show n <> " is not permitted."
                                False -> do
                                   inside <- use outerFuncNames
                                   case inside of
                                        [] -> do
                                                   pargs <- mapM pArg args
                                                   return (Extra (ProcBBLet (UserProcVar (Symbol n)) [t | (_ ::- t) <- pargs]))
                                        _  -> parseError ("Black boxes can only be defined on top-level scope.")
    _ -> parseError $ "Invalid function name expression " <> show name <> ", must be a symbol."


pClip :: JExpr -> ParseTC (DMTypeOf NormKind)
pClip (JESymbol (Symbol "L1"))   = pure L1
pClip (JESymbol (Symbol "L2"))   = pure L2
pClip (JESymbol (Symbol "LInf")) = pure LInf
pClip term = parseError $ "The term " <> show term <> "is not a valid clip value. Must be one of L1, L2 or LInf."


pJBBCall :: JExpr -> [JExpr] -> JuliaType -> [JExpr] -> ParseTC (ProcDMTerm)
pJBBCall name args rt size = do
    let kind = case size of
                 [] -> pure $ (BBSimple rt)
                 [JETup [s1, s2]] -> BBMatrix <$> pure rt <*> pSingle_Loc s1 <*> pSingle_Loc s2
                 [s] -> BBVecLike <$> pure rt <*> pSingle_Loc s
                 a -> parseError $ "Invalid call of `unbox`, expected one argument for the return container's dimension but got " <> show a
    (Extra <$> (ProcBBApply <$> pSingle_Loc name <*> mapM pSingle_Loc args <*> kind))

-- supported builtins and their parsers
builtins = H.fromList
  [ ("undisc_container!", pUnary MutUndiscM)
  , ("undisc_container", pUnary UndiscM)
  , ("size", pUnary Size)
  , ("length", pUnary Length)
  , ("zero_gradient", pUnary ZeroGrad)
  , ("internal_expect_const", pUnary InternalExpectConst)
  , ("internal_mutate!", pUnary InternalMutate)
  , ("clone", pUnary Clone)
  , ("row_to_vec", pUnary MakeVec)
  , ("vec_to_row", pUnary MakeRow)
  , ("disc", pUnary Disc)
  , ("undisc", pUnary Undisc)
  , ("ceil", pUnary (\a -> Op (IsUnary DMOpCeil) [a]))

  , ("subtract_gradient!", pBinary MutSubGrad)
  , ("subtract_gradient", pBinary SubGrad)
  , ("scale_gradient!", pBinary ScaleGrad)
  , ("sum_gradients", pBinary SumGrads)
  , ("map", pBinary MMap)
  , ("map_rows", pBinary MapRows)
  , ("map_cols", pBinary MapCols)
  , ("reduce_cols", pBinary PReduceCols)
  , ("clip!", pBuiltinClip MutClipM)
  , ("clip", pBuiltinClip ClipM)
  , ("norm_convert!", pBuiltinClip MutConvertM)
  , ("norm_convert", pBuiltinClip ConvertM)
  , ("count", pBinary Count)
  , ("/", pBinary (\a b -> Op (IsBinary DMOpDiv) [a,b]))
  , ("-", pBinary (\a b -> Op (IsBinary DMOpSub) [a,b]))
  , ("%", pBinary (\a b -> Op (IsBinary DMOpMod) [a,b]))
  , ("==", pBinary (\a b -> Op (IsBinary DMOpEq) [a,b]))
  
  , ("index", pTernary Index)
  , ("laplacian_mechanism!", pTernary MutLaplace)
  , ("laplacian_mechanism", pTernary Laplace)
  , ("fold", pTernary MFold)
  , ("map_cols_binary", pTernary MapCols2)
  , ("map_rows_binary", pTernary MapRows2)
  , ("clipn", pTernary ClipN)

  , ("gaussian_mechanism!", pQuaternary MutGauss)
  , ("gaussian_mechanism", pQuaternary Gauss)
  , ("above_threshold", pQuaternary AboveThresh)
--  , ("exponential_mechanism", pQuaternary Exponential)
  , ("parallel_private_fold_rows", pQuaternary PFoldRows)
  
  , ("+", pMultiary (\a b -> Op (IsBinary DMOpAdd) [a,b]))
  , ("*", pMultiary (\a b -> Op (IsBinary DMOpMul) [a,b]))
  ]



builtinErr t n args = parseError $ "The builtin (" <> T.unpack t <> ") requires " <> n <> " arguments, but has been given " <> show (length args)

-- build parser for builtins
pQuaternary ctor _ [a1, a2, a3, a4] _ = ctor <$> pSingle_Loc a1 <*> pSingle_Loc a2 <*> pSingle_Loc a3 <*> pSingle_Loc a4
pQuaternary ctor t args _             = builtinErr t "4" args

pTernary ctor _ [a1, a2, a3] _ = ctor <$> pSingle_Loc a1 <*> pSingle_Loc a2 <*> pSingle_Loc a3
pTernary ctor t args _         = builtinErr t "3" args

pBinary ctor _ [a1, a2] _ = ctor <$> pSingle_Loc a1 <*> pSingle_Loc a2
pBinary ctor t args _     = builtinErr t "2" args

pUnary ctor _ [a1] _ = ctor <$> pSingle_Loc a1
pUnary ctor t args _ = builtinErr t "1" args

pMultiary ctor t [] _       = builtinErr t "at least 2" []
pMultiary ctor t [a] _      = builtinErr t "at least 2" [a]
pMultiary ctor _ args myloc = getLocated <$> foldl1 (\a b -> Located myloc (ctor a b)) <$> (mapM pSingle_Loc args)

-- clip gets a special bc one argument is Clip not DMTerm
pBuiltinClip ctor _ [a1, a2] _ = ctor <$> pClip a1 <*> pSingle_Loc a2
pBuiltinClip ctor t args _       = builtinErr t "2" args


-- parse function call
pJCall :: JExpr -> [JExpr] -> ParseTC ProcDMTerm
-- if the term is a symbol, we check if it
-- is a builtin/op, if so, we construct the appropriate DMTerm
pJCall (JESymbol (Symbol sym)) args = do
  myloc <- getCurrentLoc
  case H.lookup sym builtins of
       Just ctor -> ctor sym args myloc -- parse using parser given in the builtins hash map
       Nothing   -> do -- all other symbols turn into calls on TeVars
                      inside <- use outerFuncNames
                      case ((Symbol sym) `elem` inside) of
                         False -> do
                             v <- newProcVar (Symbol sym)
                             (Apply (Located myloc (Extra (ProcVarTerm v))) <$> mapM pSingle_Loc args)
                         True -> parseError $ "Recursive call of " <> show sym <> " is not permitted."

-- all other terms turn into calls
pJCall term args = Apply <$> pSingle_Loc term <*> mapM pSingle_Loc args


parseDMTermFromJExpr :: JExpr -> TC LocProcDMTerm
parseDMTermFromJExpr expr = liftNewLightTC (pSingle_Loc expr)
-- parseDMTermFromJExpr expr = traceShow expr $ liftNewLightTC (pSingle_Loc expr)
