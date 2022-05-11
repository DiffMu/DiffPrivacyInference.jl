
module Spec.Demutation.AliasedVectorIndexing where

import Spec.Base
import DiffMu.Core.Definitions


testScoping_AliasedVectorIndexing pp = do
  describe "Values acquired by vector indexing cannot be mutated" $ do
    testAVI01 pp

testAVI01 pp = do
  let exa = " function test()        \n\
            \   function f!(a)       \n\
            \     x = a[1,1]         \n\
            \     undisc_container!(x)   \n\
            \     x                  \n\
            \   end                  \n\
            \ end                    "


  let exb = " function test()        \n\
            \   function f!(a)       \n\
            \     x = a[1]           \n\
            \     undisc_container!(x)   \n\
            \     x                  \n\
            \   end                  \n\
            \ end                    "


  let exc = " function test()        \n\
            \   function f!(a)       \n\
            \     x = a[1,:]         \n\
            \     undisc_container!(x)   \n\
            \     x                  \n\
            \   end                  \n\
            \ end                    "

  let exd = " function test()        \n\
            \   function f!(a)       \n\
            \     (x,y) = a[1,1]     \n\
            \     a = x              \n\
            \     undisc_container!(a)   \n\
            \     a                  \n\
            \   end                  \n\
            \ end                    "

  parseEvalFail pp "01a errors (Index)" exa (DemutationError "")
  parseEvalFail pp "01b errors (VIndex)" exb (DemutationError "")
  parseEvalFail pp "01c errors (Row)" exc (DemutationError "")
  parseEvalFail pp "01d errors (mutation after splitting after Index)" exd (DemutationError "")

