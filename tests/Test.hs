module Main where

import           System.Exit
import           Test.HUnit
import           InstrSpec

tests :: [Test]
tests = instrSpec

runAllTest :: [Test] -> Counts -> IO Counts
runAllTest [] counts = return counts
runAllTest (test:ts) (Counts c t e f) = do (Counts c' t' e' f') <- runTestTT test
                                           runAllTest ts (Counts (c + c') (t + t') (e + e') (f + f'))

main :: IO ()
main = do counts <- runAllTest tests (Counts 0 0 0 0)
          putStrLn $ "Total: Cases: " ++ show (cases counts) ++ " Tried: " ++ show (tried counts) ++ " Errors: " ++ show (errors counts) ++ " Failures: "++ show (failures counts)
          if (failures counts + errors counts) > 0
            then exitFailure
            else exitSuccess