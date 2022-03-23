
module DiffMu.Parser.Expr.FromString where

import DiffMu.Prelude
import DiffMu.Core
import DiffMu.Abstract.Data.Error

import Text.Megaparsec
import Text.Megaparsec.Char
import Text.Megaparsec.Debug
import Text.Megaparsec.Char.Lexer

import Data.Either

import qualified Data.Text as T
import Debug.Trace(trace, traceM)

--------------------------------------------------------------------------------
-- a straightforward representation of julia Expr.
-- this parser takes a string and mostly seperates the expression head into a constructor.
-- it also parses numbers properly.

data JTree =
     JLineNumber String Int
   | JHole
   | JTrue
   | JFalse
   | JSym String
   | JInteger Float
   | JReal Float
   | JColon
   | JSubtype [JTree]
   | JCall [JTree]
   | JCurly [JTree]
   | JArrow [JTree]
   | JFunction [JTree]
   | JAssign [JTree]
   | JTypeAssign [JTree]
   | JRef [JTree]
   | JIf [JTree]
   | JLoop [JTree]
   | JBlock [JTree]
   | JTup [JTree]
   | JNothing
   | JReturn [JTree]
   | JImport [String]
   | JUse [String]
   | JModule [JTree]
   | JUnsupported String
   deriving Show

type Parser = Parsec Void String


pTLineNumber :: Parser JTree
pTLineNumber = let pLocation = do
                                filename <- some (noneOf @[] " :")
                                char ':'
                                n <- decimal
                                return (filename, n)
              in do
                   (filename, n) <- (char ':') >> (between (string "(#= ") (string " =#)") pLocation)
                   return (JLineNumber filename n)

with :: String -> Parser a -> Parser a
with name content = between (wskipc '(') (wskipc ')') (((string name) >> sep) >> content)

skippable :: Parser String
skippable = (many (oneOf @[] " \n"))

wskip c = between skippable skippable c
wskipc c = wskip (char c)

sep :: Parser Char
sep = wskipc ','

pIdentifier :: Parser String
pIdentifier = skippable *> some (noneOf @[] "(),[]=#:\" \n") <* skippable

pSymbolString :: Parser String
pSymbolString =    (try (char ':' *> pIdentifier)
                <|> try (string "Symbol" *> between (string "(\"") (string "\")") pIdentifier))

-- any string that is well-paranthesised
pAny :: Parser String
pAny = let noParen = (some (noneOf @[] "()"))
       in (join <$> some (noParen <|> between (wskipc '(') (wskipc ')') pAny))

pAnymo :: Parser String
pAnymo = let noParen = (some (noneOf @[] "()"))
       in (join <$> some (noParen <|> between (wskipc '(') (wskipc ')') pAny))

pWithCtor :: String -> ([JTree] -> JTree) -> Parser JTree
pWithCtor name ctor = name `with` (ctor <$> (pTree `sepBy` sep))

pTree :: Parser JTree
pTree =     try pTLineNumber
        <|> try (string ":_" >> return JHole)
        <|> try ((wskip (string ":True")) >> return JTrue)
        <|> try ((wskip (string ":False")) >> return JFalse)
        <|> try (string ":(==)" >> return (JSym "=="))
        <|> try (wskip (string ":nothing") >> return JNothing)
        <|> try (wskip (string "nothing") >> return JNothing)
        <|> try (JSym <$> pSymbolString)
        <|> try (JReal <$> (wskip float))
        <|> try ((JInteger . fromIntegral) <$> (wskip decimal))
        <|> try (":import"   `with` (JImport <$> between (wskipc '(') (wskipc ')') (some (noneOf @[] "()\n,") `sepBy` sep)))
        <|> try (":import"   `with` (JImport <$> some pAny))
        <|> try (":using"   `with` (JUse <$> some pAny))
        <|> try (":module"   `pWithCtor` JModule)
        <|> try (":return"   `pWithCtor` JReturn)
        <|> try (":call"     `pWithCtor` JCall)
        <|> try (":curly"    `pWithCtor` JCurly)
        <|> try (":<:"       `pWithCtor` JSubtype)
        <|> try (":->"       `pWithCtor` JArrow)
        <|> try (":function" `pWithCtor` JFunction)
        <|> try (":(=)"      `pWithCtor` JAssign)
        <|> try (":(::)"     `pWithCtor` JTypeAssign)
        <|> try (string ":(:)" >> return JColon)
        <|> try (":ref"      `pWithCtor` JRef)
        <|> try (":if"       `pWithCtor` JIf)
        <|> try (":elseif"   `pWithCtor` JIf)
        <|> try (":for"      `pWithCtor` JLoop)
        <|> try (":block"    `pWithCtor` JBlock)
        <|> try (":tuple"    `pWithCtor` JTup)
        <|> try ((wskip (string "true")) >> return (JUnsupported "true"))
        <|> try ((wskip (string "false")) >> return (JUnsupported "false"))
        <|> JUnsupported <$> pAny


parseJTreeFromString :: String -> Either DMException JTree
parseJTreeFromString input =
  -- let res = runParser pTree "jl-hs-communication" (trace ("Parsing input:\n------------\n" <> input <> "\n---------------") input)
  let res = runParser pTree "jl-hs-communication" input
  in case res of
    Left e  -> Left (InternalError $ "Communication Error: Could not parse JExpr from string\n\n----------------------\n" <> input <> "\n---------------------------\n" <> errorBundlePretty e)
    Right a -> Right a


--------------------------------------------------------------------------------------------
-- parse a JTree (which has the same structure as julia Expr) and
--  - distinguish slet, tlet and bind
--  - distinguish black boxes, sensitivity and privacy lambdas
--  - tidy up loops
--  - catch a few invalid cases
--  - parse symbols in places where types are expected into JuliaTypes
-- the result gets put into a JExpr so it can be used for proper assignment nesting.


-- parse state is (filename, line number, are we inside a function)
-- it's also used for the next step, we don't need th
type JEParseState = (StateT (String,Int) (Except DMException))

jParseError :: String -> JEParseState a
jParseError message = do
                       (file,line) <- get
                       throwOriginalError (ParseError message file line)

data JExpr =
     JEInteger Float
   | JEReal Float
   | JESymbol Symbol
   | JEHole
   | JETrue
   | JEFalse
   | JEColon
   | JELineNumber String Int
   | JEUnsupported String
   | JECall JExpr [JExpr]
   | JEBlock [JExpr]
   | JEBlackBox JExpr [JExpr]
   | JEBBCall JExpr [JExpr] JuliaType [JExpr]
   | JETypeAnnotation JExpr JuliaType
   | JENotRelevant JExpr JuliaType
   | JEIter JExpr JExpr JExpr
   | JELoop JExpr JExpr JExpr
   | JELam [JExpr] JuliaType JExpr
   | JELamStar [JExpr] JuliaType JExpr
   | JEFunction JExpr JExpr
   | JEAssignment JExpr JExpr
   | JETup [JExpr]
   | JETupAssignment [JExpr] JExpr
   | JEIfElse JExpr JExpr (Maybe JExpr)
   | JERef JExpr [JExpr]
   | JEImport
   | JEUse
   | JEReturn
   deriving Show


pJuliaType :: JTree -> JEParseState JuliaType
pJuliaType (JSym name) = case name of
    "Any"             -> pure JTAny
    "Bool"            -> pure JTBool
    "Integer"         -> pure JTInt
    "Real"            -> pure JTReal
    "Data"            -> pure JTData
    "Function"        -> pure JTFunction
    "PrivacyFunction" -> pure JTPFunction
    "Vector"          -> pure (JTVector JTAny)
    "Matrix"          -> pure (JTMatrix JTAny)
    "DMModel"         -> pure JTModel
    "DMGrads"         -> pure JTGrads
    _                 -> jParseError ("Unsupported julia type " <> show name)
pJuliaType (JCurly (name : args)) = pJuliaCurly (name:args)
pJuliaType (JCall [JSym "MetricMatrix", t, n]) = JTMetricMatrix <$> pJuliaType t <*> pNorm n
pJuliaType (JCall [JSym "MetricVector", t, n]) = JTMetricVector <$> pJuliaType t <*> pNorm n
pJuliaType (JCall [JSym "MetricGradient", t, n]) = JTMetricGradient <$> pJuliaType t <*> pNorm n
pJuliaType t = jParseError ("Expected a julia type, got " <> show t)

pNorm (JSym "L1") = pure L1
pNorm (JSym "L2") = pure L2
pNorm (JSym "LInf") = pure LInf
pNorm t = jParseError ("Expected a Norm (L1, L2 or LInf), got " <> show t)

pJuliaSubtype (JSubtype [t]) = pJuliaType t
pJuliaSubtype (JSubtype t) = jParseError ("Invalid subtype statement " <> show t)
pJuliaSubtype t = jParseError ("Expected a subtype statement, but found " <> show t)

pJuliaCurly [] = jParseError ("Invalid empty type")
pJuliaCurly (name : args) = case name of
    JSym "Tuple"  -> (JTTuple <$> (mapM pJuliaType args))
    JSym "Matrix" -> case args of
        []  -> pure (JTMatrix JTAny)
        [a] -> (JTMatrix <$> (pJuliaSubtype a))
        _   -> jParseError ("Too many type parameters for matrix type in Matrix{" <> show name <> "}")
    JSym "Vector" -> case args of
        []  -> pure(JTVector JTAny)
        [a] -> (JTVector <$> (pJuliaSubtype a))
        _   -> jParseError ("Too many type parameters for vector type in Vector{" <> show name <> "}")
    _             -> jParseError ("Unsupported parametrised julia type" <> show name)



pSymbol :: Parser Symbol
pSymbol = (Symbol . T.pack) <$> (try (char ':' *> pIdentifier)
                                 <|> try (string "Symbol" *> between (string "(\"") (string "\")") pIdentifier))

pArgs :: [JTree] -> JEParseState [JExpr]
pArgs args = let pArg arg = case arg of
                     JSym _ -> pTreeToJExpr arg
                     JTypeAssign [s, JCall [JSym "Static"]] -> JENotRelevant <$> pTreeToJExpr s <*> pure JTAny
                     JTypeAssign [s, JCall [JSym "Static", t]] -> JENotRelevant <$> pTreeToJExpr s <*> pJuliaType t
                     JTypeAssign [s, t] -> JETypeAnnotation <$> pTreeToJExpr s <*> pJuliaType t
                     JHole -> pure JEHole
                     _ -> jParseError ("Invalid function argument " <> show arg)
             in mapM pArg args

pFLet :: JTree -> JTree -> JEParseState JExpr
pFLet call body = case call of
    JCall (JSym name : args) -> JEFunction <$> pTreeToJExpr (JSym name) <*> (JELam <$> pArgs args <*> pure JTAny <*> pTreeToJExpr body)
    JTypeAssign [JCall (JSym name : args), ann] -> case ann of
        JCall [JSym "BlackBox"] -> JEBlackBox <$> pTreeToJExpr (JSym name) <*> pArgs args
        JCall [JSym "Priv"] -> JEFunction <$> pTreeToJExpr (JSym name) <*> (JELamStar <$> pArgs args <*> pure JTAny <*> pTreeToJExpr body)
        JCall [JSym "Priv", annt] -> JEFunction <$> pTreeToJExpr (JSym name) <*> (JELamStar <$> pArgs args <*> pJuliaType annt <*> pTreeToJExpr body)
        _ -> JEFunction <$> pTreeToJExpr (JSym name) <*> (JELam <$> pArgs args <*> pJuliaType ann <*> pTreeToJExpr body)
    _ -> error ("invalid shape of function definition " <> show call)

pAss :: JTree -> JTree -> JEParseState JExpr
pAss asg asm = case asg of
    JHole -> (JEAssignment JEHole <$> pTreeToJExpr asm)
    JSym _ -> (JEAssignment <$> pTreeToJExpr asg <*> pTreeToJExpr asm)
    JCall _ -> pFLet asg asm
    JTup ts -> (JETupAssignment <$> mapM pTreeToJExpr ts <*> pTreeToJExpr asm)
    JTypeAssign [(JCall _), (JCall [JSym "BlackBox"])] -> pFLet asg asm
    JTypeAssign _ -> jParseError ("Type annotations on variable assignments not yet supported in assignment of " <> show asg)
    _ -> jParseError ("Unsupported assignment " <> show asg)


pIter :: [JTree] -> JEParseState JExpr
pIter as = case as of
    [start, end] -> JEIter <$> pTreeToJExpr start <*> (pure $ JEInteger 1) <*> pTreeToJExpr end
    [start, step, end] -> JEIter <$> pTreeToJExpr start <*> pTreeToJExpr step <*> pTreeToJExpr end
    _ -> jParseError ("Unsupported iteration statement " <> show (JCall (JColon : as)))


pUnbox :: [JTree] -> JEParseState JExpr
pUnbox (JCall (box : box_args) : rt : args) = JEBBCall <$> pTreeToJExpr box <*> mapM pTreeToJExpr box_args <*> pJuliaType rt <*> mapM pTreeToJExpr args
pUnbox a = jParseError $ "Invalid call of `unbox`. Expected a call of a black box function as first argument, but got " <> show a <> "."

pTreeToJExpr :: JTree -> JEParseState JExpr
pTreeToJExpr tree = case tree of
     JLineNumber f l -> do -- put line number in the state for exquisit error messages
                                 put (f, l)
                                 return (JELineNumber f l)
     JSym s          -> pure (JESymbol ((Symbol . T.pack) s))
     JInteger i      -> pure $ JEInteger i
     JReal r         -> pure (JEReal r)
     JBlock as       -> JEBlock <$> (mapM pTreeToJExpr as)
     JTup ts         -> JETup <$> (mapM pTreeToJExpr ts)
     JUnsupported s  -> pure $ JEUnsupported s
     JCall as        -> case as of
         (JSym "unbox" : args) -> pUnbox args
         (callee : args) -> JECall <$> pTreeToJExpr callee <*> mapM pTreeToJExpr args
         []              -> error "empty call"
     JArrow as       -> case as of
         [JTup args, body] -> JELam <$> pArgs args <*> pure JTAny <*> pTreeToJExpr body
         [s, body]         -> JELam <$> pArgs [s] <*> pure JTAny <*> pTreeToJExpr body
         _                 -> error ("invalid shape or number of args in lam " <> show tree)
     JIf as          -> case as of
         [cond, tr, fs] -> JEIfElse <$> pTreeToJExpr cond <*> (pTreeToJExpr tr) <*> (Just <$> (pTreeToJExpr fs))
         [cond, tr]     -> JEIfElse <$> pTreeToJExpr cond <*> (pTreeToJExpr tr) <*> pure Nothing
         _              -> error ("wrong number of arguments in ifelse expression " <> show tree)
     JFunction as    -> case as of
         [call, body] -> pFLet call body
         _            -> error ("invalid shape of function definition in " <> show tree)
     JAssign as -> case as of
         [asg, asm] -> pAss asg asm
         _ -> error ("invalid shape of assignment in " <> show tree)
     JRef as         -> case as of
         (name:refs) -> JERef <$> pTreeToJExpr name <*> mapM pTreeToJExpr refs
         _ -> error ("unsupported reference " <> show tree)
     JHole           -> pure JEHole
     JTrue           -> pure JETrue
     JFalse          -> pure JEFalse
     JNothing        -> jParseError ("Found nothing outside of a return statement. That's not supported.")
     JColon          -> pure JEColon
     JReturn v -> case v of
         [JNothing] -> pure JEReturn
         v -> jParseError ("Returning of values (like " <> show v <> ") is not permitted. You may only return \'nothing\'.")
     JImport v -> case v of
         [":.",s] -> pure JEImport -- just ignore imports
         v -> jParseError ("Only standalone imports are allowed. You tried to import specific names: " <> show v)
     JUse v -> case v of
         [":., :DiffPrivacyInference"] -> pure JEUse -- ignore `using DiffPrivacyInference`, all other using is forbidden.
         v -> jParseError ("You tried to load a module except DiffPrivacyInference with `using`. Please use standalone imports instead.: " <> show v)
     JLoop as        -> case as of
         [(JAssign [ivar, JCall (JColon: iter)]), body] -> JELoop <$> pTreeToJExpr ivar <*> pIter iter <*> pTreeToJExpr body
         [(JAssign [_, iter]), _] -> jParseError ("Iterator has to be a range! Not like " <> show iter)
         _ -> jParseError ("unsupported loop statement " <> show tree)
     JCurly _        -> jParseError ("Did not expect a julia type but got " <> show tree)
     JSubtype _        -> jParseError ("Did not expect a julia type but got " <> show tree)
     JTypeAssign _   -> jParseError ("Type annotations are not supported here: " <> show tree)
     JModule _ -> jParseError ("You can have only one module that contains all the code you want to typecheck.")


pModuleToJExpr :: JTree -> JEParseState JExpr
pModuleToJExpr (JBlock [_,m]) = pModuleToJExpr m
pModuleToJExpr (JModule [_,_,m]) = pTreeToJExpr m
pModuleToJExpr t = jParseError ("All typechecked code must be within a module! Instead got " <> show t)




parseJExprFromJTree :: JTree -> Either DMException JExpr
parseJExprFromJTree tree =
  let x = runStateT (pModuleToJExpr tree) ("unknown", 0)
      y = case runExcept x of
        Left err -> Left err
        Right (term, _) -> Right term
  in y
