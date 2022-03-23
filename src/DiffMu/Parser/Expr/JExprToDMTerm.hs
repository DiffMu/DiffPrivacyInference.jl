
{-# LANGUAGE TemplateHaskell #-}

module DiffMu.Parser.Expr.JExprToDMTerm where
    
import DiffMu.Prelude
import DiffMu.Abstract
import DiffMu.Core
import DiffMu.Core.Logging
import DiffMu.Core.TC
import DiffMu.Parser.Expr.FromString
import DiffMu.Typecheck.Preprocess.Common
import qualified Data.Text as T
import qualified Prelude as P

import Debug.Trace



data ParseFull = ParseFull
  {
    _location :: (String, Int), -- filename and line number
    _outerFuncNames :: [Symbol], -- to error upon non-toplevel back box definitions and simple recursion
    _insideAssignment :: Bool, -- to error upon assignemnts within assignments (like x = y = 100).
    _holeNames :: NameCtx -- generate new names for holes
  }

instance Default ParseFull where
    def = ParseFull ("unknown",0) [] False def

type ParseTC = LightTC Location_Parse ParseFull

$(makeLenses ''ParseFull)

newProcVar :: (MonadState ParseFull m) => Text -> m (ProcVar)
newProcVar hint = holeNames %%= (first GenProcVar . (newName hint))

parseError :: String -> ParseTC a
parseError message = do
                       (file, line) <- use location
                       loc <- getCurrentLoc

                       throwError (withContext (ParseError message file line) loc)
                        
                        -- [("While parsing this line", loc)])

                      --  throwOriginalError (ParseError message file line)


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
  (file,line) <- use location
  return $ ExactLoc (SourceLoc file (line,0) (line P.+ 1,0))


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
                 JESymbol s -> return  (Extra (ProcVarTerm (UserProcVar s)))
                 JETup elems -> (Tup <$> (mapM pSingle_Loc elems))
                 JERef name refs -> pJRef name refs
                 JECall name args -> pJCall name args
                 
                 JEBlock stmts -> Extra <$> (Block <$> pList stmts)
                 JELam args ret body -> pJLam args ret body
                 JELamStar args ret body -> pJLamStar args ret  body
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
                 JEColon -> parseError "Colon (:) can only be used to access matrix rows like in M[1,:]."
                 JETypeAnnotation _ _ -> parseError "Type annotations are only supported on function arguments."
                 JENotRelevant _ _ -> parseError "Type annotations are only supported on function arguments."
                 JELineNumber _ _ -> throwUnlocatedError (InternalError "What now?") -- TODO
                 JEImport -> parseError "import statement is not allowed here."
                 JEUse -> parseError "`using` statement is not allowed here."



-- pList_Loc :: [JExpr] -> ParseTC [LocProcDMTerm]
-- pList_Loc = undefined

pList :: [JExpr] -> ParseTC [LocProcDMTerm]
pList [] = pure []
pList (JEBlock stmts : tail) = pList (stmts ++ tail) -- handle nested blocks
pList (JEImport : tail) = pList tail -- ignore imports
pList (JEUse : tail) = pList tail -- ignore "using DiffPrivacyInference"
pList (s : tail) = do
    ps <- case s of
               JELineNumber file line -> location .= (file, line) >> return Nothing
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
                       [JEColon,_] -> parseError "Acessing columns of matrices as Vectors is not permitted."
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
                     JEHole -> (::- JTAny) <$> newProcVar "hole"
                     JESymbol s -> return ((UserProcVar s) ::- JTAny)
                     JETypeAnnotation (JESymbol s) τ -> return ((UserProcVar s) ::- τ)
                     JENotRelevant _ _ -> parseError ("Relevance annotation on a sensitivity function is not permitted.")
                     a -> parseError ("Invalid function argument " <> show a)

pArgRel arg = case arg of
                       JEHole -> (::- (JTAny, IsRelevant)) <$> newProcVar "hole"
                       JESymbol s -> return ((UserProcVar s) ::- (JTAny, IsRelevant))
                       JETypeAnnotation (JESymbol s) τ -> return ((UserProcVar s) ::- (τ, IsRelevant))
                       JENotRelevant (JESymbol s) τ -> return ((UserProcVar s) ::- (τ, NotRelevant))
                       a -> parseError ("Invalid function argument " <> show a)


pJLam args ret body = do
                   dargs <- mapM pArg args
                   dbody <- pSingle_Loc body
                   return (Extra (ProcLam dargs ret dbody))

pJLamStar args ret body = do
                       dargs <- mapM pArgRel args
                       dbody <- pSingle_Loc body
                       return (Extra (ProcLamStar dargs ret dbody))



pJLoop ivar iter body =
  let pIter start step end = do
       dstart <- pSingle_Loc start
       dstep <- pSingle_Loc step
       dend <- pSingle_Loc end
       myloc <- getCurrentLoc
       let div  = Located myloc . Op (IsBinary DMOpDiv)
       let sub  = Located myloc . Op (IsBinary DMOpSub)
       let ceil = Located myloc . Op (IsUnary DMOpCeil)
       return (ceil [div [sub [dend, sub [dstart, (Located myloc (Sng 1 JTInt))]], dstep]]) -- compute number of steps
  in case iter of
       JEIter start step end -> do
                                 dbody <- pSingle_Loc body
                                 nit <- pIter start step end
                                 i <- case ivar of
                                              JEHole -> newProcVar "hole"
                                              JESymbol s -> pure $ (UserProcVar $ s)
                                              i -> parseError ("Invalid iteration variable " <> (show i) <> ".")
                                 return (Extra (ProcPreLoop nit i dbody))
       it -> parseError ("Invalid iterator " <> show it <> ", must be a range.")


pJLet assignee assignment = do
   inside <- use insideAssignment
   case inside of
        True -> parseError ("Assignments within assignments are forbidden, but variable " <> show assignee <> " is assigned to.")
        False -> do
                   enterAssignment
                   dasgmt <- pSingle_Loc assignment
                   exitAssignment
                   case assignee of
                        JEHole     -> (\p -> Extra (ProcSLetBase PureLet p dasgmt)) <$> newProcVar "hole"
                        JESymbol s -> return (Extra (ProcSLetBase PureLet (UserProcVar s) dasgmt))
                        JETypeAnnotation _ _ -> parseError "Type annotations on variables are not supported."
                        JENotRelevant _ _    -> parseError "Type annotations on variables are not supported."
                        _                    -> parseError ("Invalid assignee " <> (show assignee) <> ", must be a variable.")


pJTLet :: [JExpr] -> JExpr -> ParseTC ProcDMTerm
pJTLet assignees assignment = let
   pSample args = case args of
                    [n, m1, m2] -> do
                                     tn <- pSingle_Loc n
                                     tm1 <- pSingle_Loc m1
                                     tm2 <- pSingle_Loc m2
                                     return (Located (NotImplementedLoc "Sample location") (Sample tn tm1 tm2))
                    _ -> parseError ("Invalid number of arguments for sample, namely " <> (show (length args)) <> " instead of 2.")
                    
   -- make sure that all assignees are simply symbols
   ensureSymbol (JESymbol s) = return ((UserProcVar s))
   ensureSymbol JEHole = newProcVar "hole"
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
    JESymbol n -> do
                       enterFunction n
                       dasgmt <- pSingle_Loc assignment
                       exitFunction
                       return (Extra (ProcFLet (UserProcVar n) dasgmt))
    _ -> parseError $ "Invalid function name expression " <> show name <> ", must be a symbol."


pJBlackBox name args =
  case name of
    JESymbol pname -> do
                    inside <- use outerFuncNames
                    case inside of
                         [] -> do
                                    pargs <- mapM pArg args
                                    return (Extra (ProcBBLet (UserProcVar pname) [t | (_ ::- t) <- pargs]))
                         _  -> parseError ("Black boxes can only be defined on top-level scope.")
    _ -> parseError $ "Invalid function name expression " <> show name <> ", must be a symbol."


pClip :: JExpr -> ParseTC (DMTypeOf ClipKind)
pClip (JESymbol (Symbol "L1"))   = pure (Clip L1)
pClip (JESymbol (Symbol "L2"))   = pure (Clip L2)
pClip (JESymbol (Symbol "LInf")) = pure (Clip LInf)
pClip term = parseError $ "The term " <> show term <> "is not a valid clip value."


pJBBCall :: JExpr -> [JExpr] -> JuliaType -> [JExpr] -> ParseTC (ProcDMTerm)
pJBBCall name args rt size = do
    let kind = case size of
                 [] -> pure $ (BBSimple rt)
                 [JETup [s1, s2]] -> BBMatrix <$> pure rt <*> pSingle_Loc s1 <*> pSingle_Loc s2
                 [s] -> BBVecLike <$> pure rt <*> pSingle_Loc s
                 a -> parseError $ "Invalid call of `unbox`, expected one argument for the return container's dimension but got " <> show a
    (Extra <$> (ProcBBApply <$> pSingle_Loc name <*> mapM pSingle_Loc args <*> kind))

    --      | ProcBBApply a [a] (BBKind ProceduralExtension))


pJCall :: JExpr -> [JExpr] -> ParseTC ProcDMTerm
-- if the term is a symbol, we check if it
-- is a builtin/op, if so, we construct the appropriate DMTerm
pJCall (JESymbol (Symbol sym)) args = do
  myloc <- getCurrentLoc
  case (sym,args) of

  -----------------
  -- binding builtins (use lambdas)
  --
  -- NOTE: This is term is currently not generated on the julia side
  --

  {-
  (t@"mcreate", [a1, a2, a3]) -> f <$> pSingle a1 <*> pSingle a2 <*> extractLambdaArgs a3
    where
      f a b (c,d) = MCreate a b c d
      extractLambdaArgs (JELam args body) = case args of
        -- 2 bound vars? yes
        [v1,v2] -> case (v1,v2) of

          -- symbols? yes
          (JESymbol v1, JESymbol v2) -> do
            body' <- pSingle body
            pure ((UserProcVar v1, UserProcVar v2) , body')

          -- symbols? no => error
          (v1,v2) -> parseError $ "In the 3rd argument of " <> T.unpack t
                                  <> ", could not parse the bound variables: " <> show (v1,v2)

        -- 2 bound vars? no => error
        args -> parseError $ "In the 3rd argument of " <> T.unpack t
                              <> ", expected a lambda term which binds two variables, but the one given binds: "
                              <> show (length args)

      -- lambda? no => error
      extractLambdaArgs term = parseError $ "In the 3rd argument of " <> T.unpack t
                                            <> ", expected a lambda term, got: " <> show term
  -- 3 args? no => error
  (t@"mcreate", args) -> parseError $ "The builtin (" <> T.unpack t <> ") requires 3 arguments, but has been given " <> show (length args)

-}

    ------------
    -- the non binding builtins

    -- 4 arguments
    (t@"gaussian_mechanism!", [a1, a2, a3, a4]) -> MutGauss <$> pSingle_Loc a1 <*> pSingle_Loc a2 <*> pSingle_Loc a3 <*> pSingle_Loc a4
    (t@"gaussian_mechanism!", args) -> parseError $ "The builtin (" <> T.unpack t <> ") requires 4 arguments, but has been given " <> show (length args)

    (t@"gaussian_mechanism", [a1, a2, a3, a4]) -> Gauss <$> pSingle_Loc a1 <*> pSingle_Loc a2 <*> pSingle_Loc a3 <*> pSingle_Loc a4
    (t@"gaussian_mechanism", args) -> parseError $ "The builtin (" <> T.unpack t <> ") requires 4 arguments, but has been given " <> show (length args)

    (t@"above_threshold", [a1, a2, a3, a4]) -> AboveThresh <$> pSingle_Loc a1 <*> pSingle_Loc a2 <*> pSingle_Loc a3 <*> pSingle_Loc a4
    (t@"above_threshold", args) -> parseError $ "The builtin (" <> T.unpack t <> ") requires 4 arguments, but has been given " <> show (length args)

    (t@"exponential_mechanism", [a1, a2, a3, a4]) -> Exponential <$> pSingle_Loc a1 <*> pSingle_Loc a2 <*> pSingle_Loc a3 <*> pSingle_Loc a4
    (t@"exponential_mechanism", args) -> parseError $ "The builtin (" <> T.unpack t <> ") requires 4 arguments, but has been given " <> show (length args)

    (t@"parallel_private_fold_rows", [a1, a2, a3, a4]) -> PFoldRows <$> pSingle_Loc a1 <*> pSingle_Loc a2 <*> pSingle_Loc a3 <*> pSingle_Loc a4
    (t@"parallel_private_fold_rows", args) -> parseError $ "The builtin (" <> T.unpack t <> ") requires 4 arguments, but has been given " <> show (length args)

    (t@"parallel_private_fold_rows!", [a1, a2, a3, a4]) -> MutPFoldRows <$> pSingle_Loc a1 <*> pSingle_Loc a2 <*> pSingle_Loc a3 <*> pSingle_Loc a4
    (t@"parallel_private_fold_rows!", args) -> parseError $ "The builtin (" <> T.unpack t <> ") requires 4 arguments, but has been given " <> show (length args)

    -- 3 arguments
    (t@"index", [a1, a2, a3]) -> Index <$> pSingle_Loc a1 <*> pSingle_Loc a2 <*> pSingle_Loc a3
    (t@"index", args) -> parseError $ "The builtin (" <> T.unpack t <> ") requires 3 arguments, but has been given " <> show (length args)

    (t@"laplacian_mechanism!", [a1, a2, a3]) -> MutLaplace <$> pSingle_Loc a1 <*> pSingle_Loc a2 <*> pSingle_Loc a3
    (t@"laplacian_mechanism!", args) -> parseError $ "The builtin (" <> T.unpack t <> ") requires 3 arguments, but has been given " <> show (length args)

    (t@"laplacian_mechanism", [a1, a2, a3]) -> Laplace <$> pSingle_Loc a1 <*> pSingle_Loc a2 <*> pSingle_Loc a3
    (t@"laplacian_mechanism", args) -> parseError $ "The builtin (" <> T.unpack t <> ") requires 3 arguments, but has been given " <> show (length args)

    (t@"fold", [a1, a2, a3]) -> MFold <$> pSingle_Loc a1 <*> pSingle_Loc a2 <*> pSingle_Loc a3
    (t@"fold", args) -> parseError $ "The builtin (" <> T.unpack t <> ") requires 3 arguments, but has been given " <> show (length args)

    (t@"map_cols_binary", [a1, a2, a3]) -> MapCols2 <$> pSingle_Loc a1 <*> pSingle_Loc a2 <*> pSingle_Loc a3
    (t@"map_cols_binary", args) -> parseError $ "The builtin (" <> T.unpack t <> ") requires 3 arguments, but has been given " <> show (length args)

    (t@"map_rows_binary", [a1, a2, a3]) -> MapRows2 <$> pSingle_Loc a1 <*> pSingle_Loc a2 <*> pSingle_Loc a3
    (t@"map_rows_binary", args) -> parseError $ "The builtin (" <> T.unpack t <> ") requires 3 arguments, but has been given " <> show (length args)

    (t@"clip", [a1, a2, a3]) -> ClipN <$> pSingle_Loc a1 <*> pSingle_Loc a2 <*> pSingle_Loc a3


--   2 arguments

    (t@"subtract_gradient!", [a1, a2]) -> MutSubGrad <$> pSingle_Loc a1 <*> pSingle_Loc a2
    (t@"subtract_gradient!", args) -> parseError $ "The builtin (" <> T.unpack t <> ") requires 2 arguments, but has been given " <> show (length args)

    (t@"subtract_gradient", [a1, a2]) -> SubGrad <$> pSingle_Loc a1 <*> pSingle_Loc a2
    (t@"subtract_gradient", args) -> parseError $ "The builtin (" <> T.unpack t <> ") requires 2 arguments, but has been given " <> show (length args)

    (t@"scale_gradient!", [a1, a2]) -> ScaleGrad <$> pSingle_Loc a1 <*> pSingle_Loc a2
    (t@"scale_gradient!", args) -> parseError $ "The builtin (" <> T.unpack t <> ") requires 2 arguments, but has been given " <> show (length args)

    (t@"sum_gradients", [a1, a2]) -> SumGrads <$> pSingle_Loc a1 <*> pSingle_Loc a2
    (t@"sum_gradients", args) -> parseError $ "The builtin (" <> T.unpack t <> ") requires 2 argument, but has been given " <> show (length args)

    (t@"map", [a1, a2]) -> MMap <$> pSingle_Loc a1 <*> pSingle_Loc a2
    (t@"map", args) -> parseError $ "The builtin (" <> T.unpack t <> ") requires 2 argument, but has been given " <> show (length args)

    (t@"map_rows", [a1, a2]) -> MapRows <$> pSingle_Loc a1 <*> pSingle_Loc a2
    (t@"map_rows", args) -> parseError $ "The builtin (" <> T.unpack t <> ") requires 2 argument, but has been given " <> show (length args)

    (t@"map_cols", [a1, a2]) -> MapCols <$> pSingle_Loc a1 <*> pSingle_Loc a2
    (t@"map_cols", args) -> parseError $ "The builtin (" <> T.unpack t <> ") requires 2 argument, but has been given " <> show (length args)

    (t@"reduce_cols", [a1, a2]) -> PReduceCols <$> pSingle_Loc a1 <*> pSingle_Loc a2
    (t@"reduce_cols", args) -> parseError $ "The builtin (" <> T.unpack t <> ") requires 2 argument, but has been given " <> show (length args)

    (t@"clip!", [a1,a2]) -> MutClipM <$> pClip a1 <*> pSingle_Loc a2
    (t@"clip!", args) -> parseError $ "The builtin (" <> T.unpack t <> ") requires 2 arguments, but has been given " <> show (length args)
    (t@"clip", [a1,a2]) -> ClipM <$> pClip a1 <*> pSingle_Loc a2
    (t@"clip", args) -> parseError $ "The builtin (" <> T.unpack t <> ") requires 2 arguments, but has been given " <> show (length args)

    (t@"count", [a1, a2]) -> Count <$> pSingle_Loc a1 <*> pSingle_Loc a2
    (t@"count", args) -> parseError $ "The builtin (" <> T.unpack t <> ") requires 2 argument, but has been given " <> show (length args)

    -- 1 argument
    (t@"norm_convert!", [a1]) -> MutConvertM <$> pSingle_Loc a1
    (t@"norm_convert!", args) -> parseError $ "The builtin (" <> T.unpack t <> ") requires 1 arguments, but has been given " <> show (length args)

    (t@"norm_convert", [a1]) -> ConvertM <$> pSingle_Loc a1
    (t@"norm_convert", args) -> parseError $ "The builtin (" <> T.unpack t <> ") requires 1 arguments, but has been given " <> show (length args)

    (t@"transpose", [a1]) -> Transpose <$> pSingle_Loc a1
    (t@"transpose", args) -> parseError $ "The builtin (" <> T.unpack t <> ") requires 1 arguments, but has been given " <> show (length args)

    (t@"size", [a1]) -> Size <$> pSingle_Loc a1
    (t@"size", args) -> parseError $ "The builtin (" <> T.unpack t <> ") requires 1 arguments, but has been given " <> show (length args)

    (t@"length", [a1]) -> Length <$> pSingle_Loc a1
    (t@"length", args) -> parseError $ "The builtin (" <> T.unpack t <> ") requires 1 arguments, but has been given " <> show (length args)
  
    (t@"zero_gradient", [a]) -> ZeroGrad <$> pSingle_Loc a
    (t@"zero_gradient", args) -> parseError $ "The builtin (" <> T.unpack t <> ") requires 1 arguments, but has been given " <> show (length args)

    (t@"internal_expect_const", [a1]) -> InternalExpectConst <$> pSingle_Loc a1
    (t@"internal_expect_const", args) -> parseError $ "The builtin (" <> T.unpack t <> ") requires 1 arguments, but has been given " <> show (length args)

    (t@"internal_mutate!", [a1]) -> InternalMutate <$> pSingle_Loc a1
    (t@"internal_mutate!", args) -> parseError $ "The builtin (" <> T.unpack t <> ") requires 1 arguments, but has been given " <> show (length args)

    (t@"clone", [a]) -> Clone <$> pSingle_Loc a
    (t@"clone", args) -> parseError $ "The builtin (" <> T.unpack t <> ") requires 1 arguments, but has been given " <> show (length args)

    (t@"row_to_vec", [a]) -> MakeVec <$> pSingle_Loc a
    (t@"row_to_vec", args) -> parseError $ "The builtin (" <> T.unpack t <> ") requires 1 arguments, but has been given " <> show (length args)

    (t@"vec_to_row", [a]) -> MakeRow <$> pSingle_Loc a
    (t@"vec_to_row", args) -> parseError $ "The builtin (" <> T.unpack t <> ") requires 1 arguments, but has been given " <> show (length args)

    (t@"disc", [a1]) -> Disc <$> pSingle_Loc a1
    (t@"disc", args) -> parseError $ "The builtin (" <> T.unpack t <> ") requires 1 arguments, but has been given " <> show (length args)

    ----------------------
    -- the ops
    -- the + and * operators allow lists as arguments
    (t@"+", [])   -> parseError "The builtin operation (+) requires at least 2 arguments, but has been given none."
    (t@"+", [a])  -> parseError "The builtin operation (+) requires at least 2 arguments, but has only been given 1."
    (t@"+", args) -> getLocated <$> foldl1 (\a b -> Located myloc (Op (IsBinary DMOpAdd) [a,b])) <$> (mapM pSingle_Loc args)


    (t@"*", [])   -> parseError "The builtin operation (*) requires at least 2 arguments, but has been given none."
    (t@"*", [a])  -> parseError "The builtin operation (*) requires at least 2 arguments, but has only been given 1."
    (t@"*", args) -> getLocated <$> foldl1 (\a b -> Located myloc (Op (IsBinary DMOpMul) [a,b])) <$> (mapM pSingle_Loc args)

    -- all unary operations.
    (t@"ceil", [a])  -> (\a -> Op (IsUnary DMOpCeil) [a]) <$> pSingle_Loc a
    (t@"ceil", args) -> parseError $ "The builtin operation (ceil) requires exactly 1 argument, but it has been given " <> show (length args)

    -- all binary operations.
    (t@"/", [a,b]) -> (\a b -> Op (IsBinary DMOpDiv) [a,b]) <$> pSingle_Loc a <*> pSingle_Loc b
    (t@"/", args)  -> parseError $ "The builtin operation (/) requires exactly 2 arguments, but it has been given " <> show (length args)

    (t@"-", [a,b]) -> (\a b -> Op (IsBinary DMOpSub) [a,b]) <$> pSingle_Loc a <*> pSingle_Loc b
    (t@"-", args)  -> parseError $ "The builtin operation (-) requires exactly 2 arguments, but it has been given " <> show (length args)

    (t@"%", [a,b]) -> (\a b -> Op (IsBinary DMOpMod) [a,b]) <$> pSingle_Loc a <*> pSingle_Loc b
    (t@"%", args)  -> parseError $ "The builtin operation (%) requires exactly 2 arguments, but it has been given " <> show (length args)

    (t@"==", [a,b]) -> (\a b -> Op (IsBinary DMOpEq) [a,b]) <$> pSingle_Loc a <*> pSingle_Loc b
    (t@"==", args)  -> parseError $ "The builtin operation (==) requires exactly 2 arguments, but it has been given " <> show (length args)

    ---------------------
    -- other symbols
    --
    -- all other symbols turn into calls on TeVars
    (sym, args) -> do
        inside <- use outerFuncNames
        case ((Symbol sym) `elem` inside) of
           False -> (Apply (Located myloc (Extra (ProcVarTerm (UserProcVar (Symbol sym))))) <$> mapM pSingle_Loc args)
           True -> parseError $ "Recursive call of " <> show sym <> " is not permitted."

-- all other terms turn into calls
pJCall term args = Apply <$> pSingle_Loc term <*> mapM pSingle_Loc args

--(arseDMTermFromJExpr :: JExpr -> Either DMException ProcDMTerm
--parseDMTermFromJExpr expr = liftLightTC (ParseFull  (\_ -> ()) (pSingle_Loc expr)

parseDMTermFromJExpr :: JExpr -> TC LocProcDMTerm
parseDMTermFromJExpr expr = liftNewLightTC (pSingle_Loc expr)
