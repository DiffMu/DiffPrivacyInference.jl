
{-# OPTIONS_GHC -fno-cse #-}

module Spec.Unsafe where

import Spec.Base


-- testUnsafeTeVarGeneration = do
--   describe "unsafe tevar generation" $ do
--     it "generates different names" $ do
--       () <- reset_tevar_counter
--       let a = unsafe_newTeVar "a"
--           b = unsafe_newTeVar "a"
--           c = unsafe_newTeVar "a"
--       (a == b, b == c, a == c) `shouldBe` (False, False, False)

testUnsafe = return ()
-- do
--   testUnsafeTeVarGeneration

