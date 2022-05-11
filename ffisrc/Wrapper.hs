
{-# LANGUAGE CPP                      #-}
{-# LANGUAGE DeriveAnyClass           #-}
{-# LANGUAGE DeriveGeneric            #-}
{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE TemplateHaskell          #-}
{-# OPTIONS_GHC -fno-warn-unused-top-binds #-}

module Wrapper where

import DiffMu.Prelude

import           Foreign.C.Types
import           Foreign.Ptr
import           Foreign.StablePtr
import           Foreign.C.String
import           Foreign.Marshal.Unsafe

-- import           Control.DeepSeq
import           Control.Lens
import           Control.Exception
import           Data.Int          (Int32)
import           GHC.Generics      (Generic)



import Data.IORef

import DiffMu.Runner
import DiffMu.Core.Definitions
import DiffMu.Typecheck.JuliaType
import DiffMu.Parser.FromString
import DiffMu.Parser.JExprToDMTerm

import Spec

foreign import ccall "dynamic" mkFun :: FunPtr (CInt -> CInt) -> (CInt -> CInt)


type SubtypingCallbackFun = CString -> CString -> Bool
type TermParserCallbackFun = CString -> IO CString

callWithCString :: FunPtr SubtypingCallbackFun -> String -> String -> Bool
callWithCString f a b = unsafeLocalState $ do
  withCString a (\ca -> withCString b (\cb -> return $ call_StringStringBool f ca cb))


typecheckFromCString_DMTerm_Debug :: FunPtr SubtypingCallbackFun -> CString -> CString -> IO ()
typecheckFromCString_DMTerm_Debug fun str rawsource = do
  putStrLn "hello!"

  writeIORef global_callback_issubtype (makeDMEnv (fun))
  str' <- peekCString str
  rawsource' <- peekCString rawsource
  typecheckFromString_DMTerm_Debug str' rawsource' `catchAny` \e -> do
    putStrLn "======================================="
    putStrLn $ "Call to haskell resulted in exception (" <> displayException e <> ")."

foreign export ccall typecheckFromCString_DMTerm_Debug :: FunPtr SubtypingCallbackFun -> CString -> CString -> IO ()

typecheckFromCString_DMTerm_Detailed :: FunPtr SubtypingCallbackFun -> CString -> CString -> IO ()
typecheckFromCString_DMTerm_Detailed fun str rawsource = do
  writeIORef global_callback_issubtype (makeDMEnv (fun))
  str' <- peekCString str
  rawsource' <- peekCString rawsource
  typecheckFromString_DMTerm_Simple PrintConstraintHistory str' rawsource' `catchAny` \e -> do
    putStrLn "======================================="
    putStrLn $ "Call to haskell resulted in exception (" <> displayException e <> ")."

foreign export ccall typecheckFromCString_DMTerm_Detailed :: FunPtr SubtypingCallbackFun -> CString -> CString -> IO ()

typecheckFromCString_DMTerm :: FunPtr SubtypingCallbackFun -> CString -> CString -> IO ()
typecheckFromCString_DMTerm fun str rawsource = do
  writeIORef global_callback_issubtype (makeDMEnv (fun))
  str' <- peekCString str
  rawsource' <- peekCString rawsource
  typecheckFromString_DMTerm_Simple DontPrintConstraintHistory str' rawsource' `catchAny` \e -> do
    putStrLn "======================================="
    putStrLn $ "Call to haskell resulted in exception (" <> displayException e <> ")."

foreign export ccall typecheckFromCString_DMTerm :: FunPtr SubtypingCallbackFun -> CString -> CString -> IO ()

catchAny :: IO a -> (SomeException -> IO a) -> IO a
catchAny = Control.Exception.catch

callTermParserCallback :: FunPtr TermParserCallbackFun -> String -> IO String
callTermParserCallback parse input = do
  withCString input (\input -> (do
                        res <- (call_StringString parse input)
                        peekCString res) `catchAny` (\_ -> return "exception in julia"))

runHaskellTests :: FunPtr SubtypingCallbackFun -> FunPtr TermParserCallbackFun -> IO ()
runHaskellTests sub parse = do
  putStrLn "We are testing now!"
  writeIORef global_callback_issubtype (makeDMEnv (sub))
  runAllTests (callTermParserCallback parse) `catchAny` \e -> do
    putStrLn "======================================="
    putStrLn $ "Call to haskell resulted in exception (" <> displayException e <> ")."

foreign import ccall "dynamic" call_StringString :: FunPtr (CString -> IO CString) -> CString -> IO CString
foreign export ccall runHaskellTests :: FunPtr SubtypingCallbackFun -> FunPtr TermParserCallbackFun -> IO ()


runSingleHaskellTest :: FunPtr SubtypingCallbackFun -> FunPtr TermParserCallbackFun -> IO ()
runSingleHaskellTest sub parse = do
  putStrLn "We are testing now!"
  writeIORef global_callback_issubtype (makeDMEnv (sub))
  runSingleTest (callTermParserCallback parse) `catchAny` \e -> do
    putStrLn "======================================="
    putStrLn $ "Call to haskell resulted in exception (" <> displayException e <> ")."

foreign export ccall runSingleHaskellTest :: FunPtr SubtypingCallbackFun -> FunPtr TermParserCallbackFun -> IO ()



runExprParser :: CString -> IO ()
runExprParser str = do
  putStrLn "Running the Expr parser now!"
  str' <- peekCString str

  let parseAndPrint = do
--      let res = parseJExprFromString str' >>= parseDMTermFromJExpr
        let res = parseJTreeFromString str' >>= parseJExprFromJTree
        case res of
          Left e -> putStrLn $ "Error: " <> show e
          Right e -> putStrLn $ "Expr: " <> show e

  parseAndPrint `catchAny` \e -> do
    putStrLn "======================================="
    putStrLn $ "Call to haskell resulted in exception (" <> displayException e <> ")."


foreign export ccall runExprParser :: CString -> IO ()




