
module Spec.Demutation.NonAliasedMutatingArguments where

import Spec.Base
import DiffMu.Core.Definitions


testScoping_NonAliasedMutatingArguments pp = do
  describe "All arguments passed in mutating positions need to be non-aliased (#177)" $ do
    testNAMA01 pp

testNAMA01 pp = do
  let exa = " function test()         \n\
            \   function g!(a,b)      \n\
            \     norm_convert!(a)    \n\
            \     norm_convert!(b)    \n\
            \     return nothing      \n\
            \   end                   \n\
            \   function f!(a)        \n\
            \     g!(a,a)             \n\
            \     return              \n\
            \   end                   \n\
            \ end                     "

  let exb = " function test()              \n\
            \   z = 1                      \n\
            \   function g!(a,b)           \n\
            \     norm_convert!(a)         \n\
            \     (x,y) = b                \n\
            \     scale_gradient!(x,a)     \n\
            \     return                   \n\
            \   end                        \n\
            \   function f!(a)             \n\
            \     g!(a,a)                  \n\
            \     return                   \n\
            \   end                        \n\
            \   f!(z)                      \n\
            \   5                          \n\
            \ end                          "


  let exc = " function test()              \n\
            \   z = 1                      \n\
            \   function g!(a,b)           \n\
            \     norm_convert!(a)         \n\
            \     (x,y) = b                \n\
            \     scale_gradient!(x,a)     \n\
            \     return                   \n\
            \   end                        \n\
            \   function f!(a)             \n\
            \     g!(a,((a,a),0))          \n\
            \     return                   \n\
            \   end                        \n\
            \   f!(z)                      \n\
            \   5                          \n\
            \ end                          "

  parseEvalFail pp "01a errors (same argument in mutating/mutating is not allowed)" exa (DemutationNonAliasedMutatingArgumentError "")
  parseEvalFail pp "01b errors (same argument in mutating/non-mutating is not allowed)" exb (DemutationNonAliasedMutatingArgumentError "")
  parseEvalFail pp "01c errors (same argument in mutating/non-mutating (inside tuple) is not allowed)" exc (DemutationNonAliasedMutatingArgumentError "")

