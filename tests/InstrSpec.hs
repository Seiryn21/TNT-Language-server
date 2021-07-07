{-# LANGUAGE OverloadedStrings #-}

module InstrSpec where

import qualified Data.Map    as Map
import           Test.HUnit
import           TLS.Types
import           TLS.Instr
import           TLS.Errors

testAxiom :: Test
testAxiom = TestCase $ do assertEqual "axiom 1" (Scope Map.empty Nothing 2 0 [(1, Forall A (Not (Eq (Succ (Var A)) Zero)))]) (axiom 1 emptyScope)
                          assertEqual "axiom 2" (Scope Map.empty Nothing 2 0 [(1, Forall A (Eq (Add (Var A) Zero ) (Var A)))]) (axiom 2 emptyScope)
                          assertEqual "axiom 3" (Scope Map.empty Nothing 2 0 [(1, Forall A (Forall B (Eq (Add (Var A) (Succ (Var B))) (Succ (Add (Var A) (Var B))))))]) (axiom 3 emptyScope)
                          assertEqual "axiom 4" (Scope Map.empty Nothing 2 0 [(1, Forall A (Eq (Mul (Var A) Zero) Zero))]) (axiom 4 emptyScope)
                          assertEqual "axiom 5" (Scope Map.empty Nothing 2 0 [(1, Forall A (Forall B (Eq (Mul (Var A) (Succ (Var B))) (Add (Mul (Var A) (Var B)) (Var A)))))]) (axiom 5 emptyScope)
                          assertEqual "axiom range error" (Scope Map.empty Nothing 2 0 [(1, Error axiomRangeError)]) (axiom 6 emptyScope)

testTheorem :: Test
testTheorem = TestCase $ do let theoremMap = Map.fromList [("proven", (True,Eq (Var A) (Var B))), ("unproven", (False, Eq (Var C) (Var D)))]
                            assertEqual "theorem proven"     (Scope theoremMap Nothing 2 0 [(1, Eq (Var A) (Var B))]) (theorem "proven" (Scope theoremMap Nothing 1 0 []))
                            assertEqual "theorem unproven"   (Scope theoremMap Nothing 2 0 [(1, Warning theoremUnprovenWarning $ Eq (Var C) (Var D))]) (theorem "unproven" (Scope theoremMap Nothing 1 0 []))
                            assertEqual "theorem inexistant" (Scope theoremMap Nothing 2 0 [(1, Error theoremMeBeDeclaredAboveError)]) (theorem "inexistant" (Scope theoremMap Nothing 1 0 []))


instrSpec :: [Test]
instrSpec = [ TestLabel "Axiom" testAxiom
            , TestLabel "Theorem" testTheorem
            ]