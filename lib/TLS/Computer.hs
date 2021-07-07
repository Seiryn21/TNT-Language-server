{-# LANGUAGE OverloadedStrings #-}

module TLS.Computer where

import           Data.List
import qualified Data.Map           as Map
import qualified Data.Text          as T
import qualified Language.LSP.Types as LSP
import           Text.Printf
import           TLS.Types

addTheoremToScope :: Scope -> Identifier -> (Bool, Formula) -> Scope
addTheoremToScope (Scope map sc n l lines) name theorem = Scope (Map.insert name theorem map) sc n l lines

printOpenFantasy :: Int -> Int -> T.Text
printOpenFantasy ind tab = T.pack $ printf "%*s[" (ind + tab + 1) ("" :: String)

printCloseFantasy :: Int -> Int -> T.Text
printCloseFantasy ind tab = T.pack $ printf "%*s]" (ind + tab) ("" :: String)

printFormula :: Int -> Int -> Int -> Formula -> T.Text
printFormula ind n tab f = T.pack $ printf "%*d%*s%s" ind n (tab + 1) ("" :: String) (show f)

printError :: Int -> Int -> Int -> T.Text
printError ind n tab = T.pack $ printf "%*d%*sError" ind n (tab + 1) ("" :: String)

diagnosticFromError :: LSP.Range -> T.Text -> LSP.Diagnostic
diagnosticFromError range error = LSP.Diagnostic range (Just LSP.DsError) Nothing (Just "TNT-prover") error Nothing Nothing

diagnosticFromWarning :: LSP.Range -> T.Text -> LSP.Diagnostic
diagnosticFromWarning range warning = LSP.Diagnostic range (Just LSP.DsWarning ) Nothing (Just "TNT-prover") warning Nothing Nothing

diagnosticUnproven :: LSP.Range -> LSP.Diagnostic
diagnosticUnproven range = LSP.Diagnostic range (Just LSP.DsWarning) Nothing (Just "TNT-prover") "Theorem isn't proven" Nothing Nothing

diagnosticAlreadyProven :: LSP.Range -> LSP.Diagnostic
diagnosticAlreadyProven range = LSP.Diagnostic range (Just LSP.DsInfo) Nothing (Just "TNT-prover") "Theorem is already proven" Nothing Nothing

computeInstr :: Int -> Scope -> InstrBlock -> (Maybe LSP.Diagnostic, Scope, [Line])
computeInstr _   sc (Nothing, range,_ ) = (Nothing, sc, [Line (Just range) "" True])
computeInstr ind sc@(Scope _ _ n l _) (Just f,displayRange,errRange) = case f sc of
  sc@(Scope _ _ n' l' ((_,Error error):lines)) -> (Just $ diagnosticFromWarning errRange error, sc, [Line (Just displayRange) (printError ind n l) False])
  sc@(Scope _ _ n' l' ((_,Warning error f):lines)) -> (Just $ diagnosticFromWarning errRange error, sc, [Line (Just displayRange) (printFormula ind n l f) False])
  sc@(Scope _ _ n' l' ((_, f):_)) -> (Nothing, sc, case compare l l' of
    LT -> [Line Nothing (printOpenFantasy ind l) False, Line (Just displayRange) (printFormula ind n l' f) False]
    GT -> [Line Nothing (printCloseFantasy ind l) False, Line (Just displayRange) (printFormula ind n l' f) False]
    EQ -> [Line (Just displayRange) (printFormula ind n l' f) False])

computeTheorem :: Scope -> Theorem -> ([LSP.Diagnostic], Bool, ComputedTheorem)
computeTheorem sc (Theorem r r' id f instrs) = let ind = length $ show $ length instrs in
                                               computeTheorem' ind sc False [] instrs []
                                               where computeTheorem' ind sc False lines [] diags = (diagnosticUnproven r:diags, False, ComputedTheorem (Just r') (Just lines))
                                                     computeTheorem' ind sc True  lines [] diags = (diags, True, ComputedTheorem (Just r') (Just lines))
                                                     computeTheorem' ind sc True  lines ((Just _, _, range):_) diags = (diagnosticAlreadyProven range:diags, True, ComputedTheorem (Just r') (Just lines))
                                                     computeTheorem' ind sc _     lines (instr:instrs) diags = case computeInstr ind sc instr of
                                                         (Just diag, sc', lines') -> computeTheorem' ind sc' False (lines++lines') instrs (diag:diags)
                                                         (Nothing, sc'@(Scope _ _ _ l []), lines') -> computeTheorem' ind sc' False (lines++lines') instrs diags
                                                         (Nothing, sc'@(Scope _ _ _ l ((_,f'):_)), lines') -> if l == 0 && f == f'
                                                                                                          then computeTheorem' ind sc' True (lines++lines') instrs diags
                                                                                                          else computeTheorem' ind sc' False (lines++lines') instrs diags
foldTheorems :: (Scope, [LSP.Diagnostic], [ComputedTheorem]) -> Theorem ->  (Scope, [LSP.Diagnostic], [ComputedTheorem])
foldTheorems (sc, diags, cpt) th@(Theorem _ _ id f _) = let (diags', isProved, computed) = computeTheorem sc th in
                                                        (addTheoremToScope sc id (isProved, f), diags++diags', computed:cpt)

computeTheorems :: [Theorem] -> ([LSP.Diagnostic], [ComputedTheorem])
computeTheorems theorems = let (finalScope, diags, computed) = foldl foldTheorems (emptyScope, [], []) theorems in
                           (diags, computed)