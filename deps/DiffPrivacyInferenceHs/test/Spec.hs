
module Spec where

import Spec.Base
import Spec.Subtyping
import Spec.Supremum
import Spec.Rules
import Spec.Scoping
import Spec.Demutation.AssignmentMoveSemantics
import Spec.Demutation.NonAliasedMutatingArguments
import Spec.Demutation.AliasedVectorIndexing
import Spec.Demutation.Passthrough
import Spec.OriginalScoping
import Spec.TypecheckingExamples
import Spec.Unsafe
import Spec.Unification
import Spec.Issues
-- import Spec.Parsing
import Spec.Demutation
import Spec.DemutationScoping
import Spec.SingleRun

-- import Test.QuickCheck hiding (Fun)

defaultspec spec = do
  summary <- runSpec spec defaultConfig
  evaluateSummary summary
  --     getArgs
  -- >>= readConfig defaultConfig
  -- >>= withArgs [] . runSpec spec
  -- >>= evaluateSummary

runSingleTest :: (String -> IO String) -> IO ()
runSingleTest parse = defaultspec $ testSingleRun parse


runAllTests :: (String -> IO String) -> IO ()
runAllTests parse = defaultspec $ do
  testUnsafe
  testUnification
  testSubtyping
  testSubtyping_MaxMinCases
  testSubtyping_Cycles
  testSubtyping_ContractEdge
  testSupremum
  testCheck_Rules
  testScoping parse
  testDemutation parse
  testDemutationScoping parse
  testOriginalScoping parse
  testScoping_AssignmentMoveSemantics parse
  testScoping_NonAliasedMutatingArguments parse
  testScoping_AliasedVectorIndexing parse
  testDemutation_Passthrough parse
  testTypecheckingExamples parse
  testIssues parse
  -- testParsing parse




