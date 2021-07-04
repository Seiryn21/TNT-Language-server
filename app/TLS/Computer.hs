{-# LANGUAGE OverloadedStrings #-}

module TLS.Computer where

import           Data.List
import qualified Data.Map           as Map
import qualified Data.Text          as T
import qualified Language.LSP.Types as LSP
import           Text.Printf
import           TLS.Types

emptyScope :: Scope
emptyScope = Scope Map.empty Nothing 1 0 []

addTheoremToScope :: Scope -> Identifier -> Maybe Formula -> Scope
addTheoremToScope (Scope map sc n l lines) name theorem = Scope (Map.insert name theorem map) sc n l lines

printOpenFantasy :: Int -> Int -> T.Text
printOpenFantasy ind tab = T.pack $ printf "%*s[" (ind + tab + 1) ("" :: String)

printCloseFantasy :: Int -> Int -> T.Text
printCloseFantasy ind tab = T.pack $ printf "%*s]" (ind + tab) ("" :: String)

printFormula :: Int -> Int -> Int -> Formula -> T.Text
printFormula ind n tab f = T.pack $ printf "%*d%*s%s" ind n (tab + 1) ("" :: String) (show f)

diagnosticsFromError :: LSP.Range -> T.Text -> LSP.Diagnostic
diagnosticsFromError range error = LSP.Diagnostic range (Just LSP.DsError) Nothing (Just "TNT-prover") error Nothing Nothing

diagnosticUnproven :: LSP.Range -> LSP.Diagnostic
diagnosticUnproven range = LSP.Diagnostic range (Just LSP.DsWarning) Nothing (Just "TNT-prover") "Theorem isn't proven" Nothing Nothing

diagnosticAlreadyProven :: LSP.Range -> LSP.Diagnostic
diagnosticAlreadyProven range = LSP.Diagnostic range (Just LSP.DsInfo) Nothing (Just "TNT-prover") "Theorem is already proven" Nothing Nothing

computeInstr :: Int -> Scope -> InstrBlock -> Either (Scope, [Line]) (LSP.Range, T.Text)
computeInstr _ sc (Nothing, range,_ ) = Left (sc, [Line (Just range) "" True])
computeInstr ind sc@(Scope _ _ n l _) (Just f,displayRange,errRange) = case f sc of
  (Scope _ _ _ _ ((_,Error error):lines)) -> Right (errRange, error)
  sc@(Scope _ _ n' l' ((_, f):_)) -> Left (sc, case compare l l' of
    LT -> [Line Nothing (printOpenFantasy ind l) False, Line (Just displayRange) (printFormula ind n l' f) False]
    GT -> [Line Nothing (printCloseFantasy ind l) False, Line (Just displayRange) (printFormula ind n l' f) False]
    EQ -> [Line (Just displayRange) (printFormula ind n l' f) False])

computeTheorem :: Scope -> Theorem -> (Maybe LSP.Diagnostic, Bool, ComputedTheorem)
computeTheorem sc (Theorem r r' id f instrs) = let ind = length $ show $ length instrs in
                                               computeTheorem' ind sc False [] instrs
                                               where computeTheorem' ind sc False lines [] = (Just $ diagnosticUnproven r, False, ComputedTheorem (Just r') (Just lines))
                                                     computeTheorem' ind sc True lines  [] = (Nothing, True, ComputedTheorem (Just r') (Just lines))
                                                     computeTheorem' ind sc True lines  ((Just _, _, range):_) = (Just $ diagnosticAlreadyProven range, True, ComputedTheorem (Just r') (Just lines))
                                                     computeTheorem' ind sc _ lines (instr:instrs) = case computeInstr ind sc instr of
                                                         Right (range, error) -> (Just $ diagnosticsFromError range error, False, ComputedTheorem (Just r') (Just lines))
                                                         Left (sc'@(Scope _ _ _ l ((_,f'):_)), lines') -> if l == 0 && f == f'
                                                                                                          then computeTheorem' ind sc' True (lines++lines') instrs
                                                                                                          else computeTheorem' ind sc' False (lines++lines') instrs
foldTheorems :: (Scope, [LSP.Diagnostic], [ComputedTheorem]) -> Theorem ->  (Scope, [LSP.Diagnostic], [ComputedTheorem])
foldTheorems (sc, diags, cpt) th@(Theorem _ _ id f _) = let (diag, isProved, computed) = computeTheorem sc th in
                                                        case diag of
                                                            Nothing -> (addTheoremToScope sc id (Just f), diags, computed:cpt) 
                                                            Just diag -> (addTheoremToScope sc id Nothing, diag:diags, computed:cpt) 

computeTheorems :: [Theorem] -> ([LSP.Diagnostic], [ComputedTheorem])
computeTheorems theorems = let (finalScope, diags, computed) = foldl foldTheorems (emptyScope, [], []) theorems in
                           (diags, computed)