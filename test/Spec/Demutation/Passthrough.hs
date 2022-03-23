

module Spec.Demutation.Passthrough where

import Spec.Base
import DiffMu.Core.Definitions


testDemutation_Passthrough pp = do
  describe "Functions cannot pass through values" $ do
    testPass01 pp

testPass01 pp = do

  let exa = "function test(a)\n\
               \  a           \n\ 
               \end"

  let exb = "function test(a)\n\
               \  clone(a)           \n\
               \end"

  let exc = " function f(a)       \n\
           \   x = a              \n\
           \   x                  \n\
           \ end                  "

  let exd = " function f(a)       \n\
           \   x = a              \n\
           \   a = x              \n\
           \   a                  \n\
           \ end                  "

  let ty_b = do
                (t1 :: DMType) <- newVar
                return (Fun [([NoFun(t1) :@ oneId] :->: NoFun(t1)) :@ Just [JTAny]])

  parseEvalFail pp "01a errors (straightforward passthrough)" exa (DemutationError "")
  parseEvalUnify pp "01b succeeds (clone passthrough)" exb (ty_b)
  parseEvalFail pp "01c errors (passthrough of moved var)" exc (DemutationError "")
  parseEvalFail pp "01d errors (passthrough after double move)" exd (DemutationError "")

