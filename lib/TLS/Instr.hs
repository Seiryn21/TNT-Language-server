{-# LANGUAGE OverloadedStrings #-}

module TLS.Instr where

import           Control.Applicative
import           Data.Maybe
import           Data.List
import qualified Data.Map as Map
import qualified Data.Text as T
import           TLS.Types
import           TLS.Errors

getFromLines :: Lines -> Int -> Maybe Formula
getFromLines [] _ = Nothing
getFromLines ((n, f):l) n' = if n == n' then Just f else getFromLines l n'

getFromScope :: Scope -> Int -> Maybe Formula
getFromScope (Scope _ Nothing _ _ lines)   n = getFromLines lines n
getFromScope (Scope _ (Just sc) _ _ lines) n = getFromLines lines n <|> getFromScope sc n

addToScope :: Formula -> Scope -> Scope
addToScope f (Scope ths sc n l lines) = Scope ths sc (n+1) l ((n, f):lines)

addError :: T.Text -> Scope -> Scope
addError e (Scope ths sc n l lines) = Scope ths sc (n+1) l ((n, Error e):lines)

addWarning :: T.Text -> Formula -> Scope -> Scope
addWarning e f (Scope ths sc n l lines) = Scope ths sc (n+1) l ((n, Warning e f):lines)

axiom :: Int -> Scope -> Scope
axiom n
  | n == 1 = addToScope $ Forall A $ Not $ Eq (Succ (Var A)) Zero
  | n == 2 = addToScope $ Forall A $ Eq (Add (Var A) Zero) (Var A)
  | n == 3 = addToScope $ Forall A $ Forall B $ Eq (Add (Var A) (Succ $ Var B)) (Succ $ Add (Var A) (Var B))
  | n == 4 = addToScope $ Forall A $ Eq (Mul (Var A) Zero) Zero
  | n == 5 = addToScope $ Forall A $ Forall B $ Eq (Mul (Var A) (Succ $ Var B)) (Add (Mul (Var A) (Var B)) (Var A))
  | otherwise = addError axiomRangeError

theorem :: Identifier -> Scope -> Scope
theorem id sc@(Scope map _ _ _ _) = case Map.lookup id map of
                                      Nothing -> addError theoremMeBeDeclaredAboveError sc
                                      Just (False, f) -> addWarning theoremUnprovenWarning f sc
                                      Just (True,  f) -> addToScope f sc

openFantasy :: Formula -> Scope -> Scope
openFantasy f sc@(Scope ths _ n l _) = addToScope f (Scope ths (Just sc) n (l+1) [])

getPremise :: Lines -> Formula
getPremise [(n,f)] = f
getPremise (l:ls) = getPremise ls

getConclusion :: Lines -> Formula
getConclusion ((n,f):l) = f

closeFantasy :: Scope -> Scope
closeFantasy (Scope ths (Just (Scope _ sc _ l lines)) n _ lines') = addToScope (Implie (getPremise lines') (getConclusion lines')) (Scope ths sc n l lines)
closeFantasy sc = addError "Not in a fantasy" sc

outOfScope :: Scope -> Scope
outOfScope = addError "Theorem out of scope"

mustBeEq :: Scope -> Scope
mustBeEq = addError "Theorem must be an equation"

symmetry :: Int -> Scope -> Scope
symmetry n sc = case getFromScope sc n of
                  Nothing -> outOfScope sc
                  Just (Eq t1 t2) -> addToScope (Eq t2 t1) sc
                  _ -> mustBeEq sc

transitivity :: Int -> Int -> Scope -> Scope
transitivity m n sc = case getFromScope sc m of
                        Nothing -> outOfScope sc
                        Just (Eq t1 t2) -> case getFromScope sc n of
                                             Nothing -> outOfScope sc
                                             Just (Eq t1' t2') -> if t2 == t1'
                                                                  then addToScope (Eq t1 t2') sc
                                                                  else addError "Right side of the first equation and left side of the second equation must be equal" sc
                                             _ -> mustBeEq sc
                        _ -> mustBeEq sc

addSucc :: Int -> Scope -> Scope
addSucc n sc = case getFromScope sc n of
                 Nothing -> outOfScope sc
                 Just (Eq t1 t2) -> addToScope (Eq (Succ t1) (Succ t2)) sc
                 _ -> mustBeEq sc

removeSucc :: Int -> Scope -> Scope
removeSucc n sc = case getFromScope sc n of
                    Nothing -> outOfScope sc
                    Just (Eq (Succ t1) (Succ t2)) -> addToScope (Eq t1 t2) sc
                    _ -> addError "Theorem must be an equation with S on both side" sc

join :: Int -> Int -> Scope -> Scope
join m n sc = case getFromScope sc m of
  Nothing -> outOfScope sc
  Just f1 -> case getFromScope sc n of
    Nothing -> outOfScope sc
    Just f2 -> addToScope (And f1 f2) sc

separe :: Int -> Int -> Scope -> Scope
separe m n sc = case getFromScope sc m of
  Nothing -> outOfScope sc
  Just (And f1 f2) -> case n of
    1 -> addToScope f1 sc
    2 -> addToScope f2 sc
    _ -> addError "You must choose the first or the second side of the formula" sc
  _ -> addError "Theorem must be an and" sc

detach :: Int -> Int -> Scope -> Scope
detach m n sc = case getFromScope sc m of
                  Nothing -> outOfScope sc
                  Just (Implie t1 t2) -> case getFromScope sc n of
                                           Nothing -> outOfScope sc
                                           Just f -> if f == t1
                                                     then addToScope t2 sc
                                                     else addError "Theorem must be equal to the left side of the implication" sc
                  _ -> addError "Theorem must be an implication" sc

contrapose :: Int -> Scope -> Scope
contrapose n sc = case getFromScope sc n of
                    Nothing -> outOfScope sc
                    Just (Implie t1 t2) -> addToScope (Implie (Not t2) (Not t1)) sc
                    _ -> addError "Theorem must be an implication" sc

getAllPremise :: Scope -> [Formula]
getAllPremise (Scope ths Nothing n l lines) = []
getAllPremise (Scope ths (Just sc) n l lines) = getPremise lines:getAllPremise sc

getAllVarTerm :: Term -> [Var]
getAllVarTerm Zero        = []
getAllVarTerm (Var v)     = [v]
getAllVarTerm (Succ t)    = getAllVarTerm t
getAllVarTerm (Add t1 t2) = nub $ getAllVarTerm t1 ++ getAllVarTerm t2
getAllVarTerm (Mul t1 t2) = nub $ getAllVarTerm t1 ++ getAllVarTerm t2

getAllVar :: Formula -> [Var]
getAllVar (Not f)        = getAllVar f
getAllVar (Eq t1 t2)     = nub $ getAllVarTerm t1 ++ getAllVarTerm t2
getAllVar (And f1 f2)    = nub $ getAllVar f1 ++ getAllVar f2
getAllVar (Or f1 f2)     = nub $ getAllVar f1 ++ getAllVar f2
getAllVar (Implie f1 f2) = nub $ getAllVar f1 ++ getAllVar f2
getAllVar (Forall v f)   = nub $ v:getAllVar f
getAllVar (Exist v f)    = nub $ v:getAllVar f

getAllBound :: Formula -> [Var]
getAllBound (Eq t1 t2)     = []
getAllBound (Not f)        = getAllBound f
getAllBound (And f1 f2)    = nub $ getAllBound f1 ++ getAllBound f2
getAllBound (Or f1 f2)     = nub $ getAllBound f1 ++ getAllBound f2
getAllBound (Implie f1 f2) = nub $ getAllBound f1 ++ getAllBound f2
getAllBound (Forall v f)   = v:getAllBound f
getAllBound (Exist v f)    = v:getAllBound f

getAllFree :: Formula -> [Var]
getAllFree f = getAllVar f \\ getAllBound f

replaceAllTerm :: Term -> Term -> Term -> Term
replaceAllTerm s r t = if s == t
                       then r
                       else case t of
                              (Succ t') -> Succ $ replaceAllTerm s r t'
                              (Add t1 t2) -> Add (replaceAllTerm s r t1) (replaceAllTerm s r t2)
                              (Mul t1 t2) -> Mul (replaceAllTerm s r t1) (replaceAllTerm s r t2)
                              t' -> t'

replaceAll :: Term -> Term -> Formula -> Formula
replaceAll s r (Eq     t1 t2) = Eq       (replaceAllTerm s r t1) (replaceAllTerm s r t2)
replaceAll s r (Not    f)     = Not      (replaceAll s r f)
replaceAll s r (Exist  v f)   = Exist  v (replaceAll s r f)
replaceAll s r (Forall v f)   = Forall v (replaceAll s r f)
replaceAll s r (And    f1 f2) = And      (replaceAll s r f1) (replaceAll s r f2)
replaceAll s r (Or     f1 f2) = Or       (replaceAll s r f1) (replaceAll s r f2)
replaceAll s r (Implie f1 f2) = Implie   (replaceAll s r f1) (replaceAll s r f2)

specialize :: Int -> Term -> Scope -> Scope
specialize n t sc = case getFromScope sc n of
                      Nothing -> outOfScope sc
                      Just (Forall v f) -> case getAllVarTerm t `intersect` getAllBound f of
                                         []  -> addToScope (replaceAll (Var v) t f) sc
                                         l -> addError "Term contain bound variables" sc
                      _ -> addError "Theorem must begin by a forall quantifier" sc

generalize :: Int -> Var -> Scope -> Scope
generalize n v sc = case getFromScope sc n of
                      Nothing -> outOfScope sc
                      Just f -> if elem v $ getAllPremise sc >>= getAllFree
                                then addError "The variable is free in a premise" sc
                                else if elem v $ getAllBound f
                                     then addError "The variable must be free in the theorem" sc
                                     else addToScope (Forall v f) sc

replaceSomeTerm :: Term -> Term -> Term -> [Int] -> ([Int], Term)
replaceSomeTerm s r t [] = ([], t)
replaceSomeTerm s r t (occ:occs) = if s == t
                                   then if occ == 1
                                        then ((\x -> x-1) <$> occs, r)
                                        else (occ-1:((\x -> x-1) <$> occs), t)
                                   else case t of
                                    (Succ t') -> replaceSomeTerm s r t' (occ:occs)
                                    (Add t1 t2) -> let (remainingOcc, t1') = replaceSomeTerm s r t1 (occ:occs) in
                                                   let (remainingOcc', t2') = replaceSomeTerm s r t2 remainingOcc in
                                                   (remainingOcc', Add t1' t2')
                                    (Mul t1 t2) -> let (remainingOcc, t1') = replaceSomeTerm s r t1 (occ:occs) in
                                                   let (remainingOcc', t2') = replaceSomeTerm s r t2 remainingOcc in
                                                   (remainingOcc', Mul t1' t2')
                                    t' -> (occ:occs, t')

replaceSome :: Term -> Term -> [Int] -> Formula -> ([Int], Formula)
replaceSome _ _ [] f = ([],f)
replaceSome s r occ (Eq t1 t2) = let (remainingOcc, t1') = replaceSomeTerm s r t1 occ in
                                 let (remainingOcc', t2') = replaceSomeTerm s r t2 remainingOcc in
                                 (remainingOcc', Eq t1' t2')
replaceSome s r occ (Not f) = let (remainingOcc, f') = replaceSome s r occ f in
                              (remainingOcc, Not f')
replaceSome s r occ (Exist v f) = let (remainingOcc, f') = replaceSome s r occ f in
                                  (remainingOcc, Exist v f')
replaceSome s r occ (Forall v f) = let (remainingOcc, f') = replaceSome s r occ f in
                                   (remainingOcc, Forall v f')
replaceSome s r occ (And f1 f2) = let (remainingOcc, f1') = replaceSome s r occ f1 in
                                  let (remainingOcc', f2') = replaceSome s r remainingOcc f2 in
                                  (remainingOcc', And f1' f2')
replaceSome s r occ (Or f1 f2) = let (remainingOcc, f1') = replaceSome s r occ f1 in
                                 let (remainingOcc', f2') = replaceSome s r remainingOcc f2 in
                                 (remainingOcc', Or f1' f2')
replaceSome s r occ (Implie f1 f2) = let (remainingOcc, f1') = replaceSome s r occ f1 in
                                     let (remainingOcc', f2') = replaceSome s r remainingOcc f2 in
                                     (remainingOcc', Implie f1' f2')

existence :: Int -> Term -> Var -> [Int] -> Scope -> Scope
existence n t v occ sc = case getFromScope sc n of
                            Nothing -> outOfScope sc
                            Just f -> let bounds = getAllBound f in
                                if v `elem` bounds
                                then addError "The variable must be free" sc
                                else case intersect bounds $ getAllVarTerm t of
                                    [] -> case replaceSome t (Var v) (sort occ) f of
                                        ([],f) -> addToScope (Exist v f) sc
                                        _ -> addError "Can't find all occurences" sc
                                    l  -> addError "Term containt bound variables" sc

recurence :: Int -> Int -> Formula -> Scope -> Scope
recurence n m (Forall v f) sc = case getFromScope sc n of
                                Nothing -> outOfScope sc
                                Just f1 -> case getFromScope sc m of
                                  Nothing -> outOfScope sc
                                  Just f2 -> if f1 == replaceAll (Var v) Zero f
                                             then if f2 == Forall v (Implie f (replaceAll (Var v) (Succ (Var v)) f))
                                                  then addToScope (Forall v f) sc
                                                  else addError "Recursion doesn't match goal theorem" sc
                                             else addError "Inititialization doesn't match goal theorem" sc
recurence n m _ sc = addError "Theorem must begin by a forall quantifier" sc

replaceNth :: Formula -> Formula -> Formula -> Maybe Int -> (Maybe Int, Formula)
replaceNth s r t Nothing = (Nothing, t)
replaceNth s r t (Just n) = if t == s
                            then if n == 1
                                 then (Nothing, r)
                                 else (Just (n-1), t)
                            else case t of
                                  Eq _ _ -> (Just n, t)
                                  Not f -> let (n', f') = replaceNth s r f (Just n) in
                                           (n', Not f')
                                  Exist v f -> let (n', f') = replaceNth s r f (Just n) in
                                               (n', Exist v f')
                                  Forall v f -> let (n', f') = replaceNth s r f (Just n) in
                                                (n', Forall v f')
                                  And f1 f2 -> let (n', f1') = replaceNth s r f1 (Just n) in
                                               let (n'', f2') = replaceNth s r f2 n' in
                                               (n'', And f1' f2')
                                  Or f1 f2 -> let (n', f1') = replaceNth s r f1 (Just n) in
                                              let (n'', f2') = replaceNth s r f2 n' in
                                              (n'', Or f1' f2')
                                  Implie f1 f2 -> let (n', f1') = replaceNth s r f1 (Just n) in
                                                  let (n'', f2') = replaceNth s r f2 n' in
                                                  (n'', Implie f1' f2')

addDoubleNeg :: Int -> Formula -> Int -> Scope -> Scope
addDoubleNeg n f m sc = case getFromScope sc n of
                            Nothing -> outOfScope sc
                            Just f' -> case replaceNth f (Not (Not f)) f' (Just m) of
                                        (Just n, _) -> addError "Can't find specified occurence" sc
                                        (Nothing, f'') -> addToScope f'' sc

removeDoubleNeg :: Int -> Formula -> Int -> Scope -> Scope
removeDoubleNeg n (Not (Not f)) m sc = case getFromScope sc n of
                                        Nothing -> outOfScope sc
                                        Just f' -> case replaceNth (Not (Not f)) f f' (Just m) of
                                                    (Just _, _) -> addError "Can't find specified occurence" sc
                                                    (Nothing, f'') -> addToScope f'' sc
removeDoubleNeg n f m sc = addError "Formula must begin by two negation" sc

notOrToAndNot :: Int -> Formula -> Int -> Scope -> Scope
notOrToAndNot n (Not (Or f1 f2)) m sc = case getFromScope sc n of
                                        Nothing -> outOfScope sc
                                        Just f -> case replaceNth (Not (Or f1 f2)) (And (Not f1) (Not f2)) f (Just m) of
                                            (Just _, _) -> addError "Can't find specified occurence" sc
                                            (Nothing, f') -> addToScope f' sc
notOrToAndNot n f m sc = addError "Formula must be the negation of an or formula" sc

andNotToNotOr :: Int -> Formula -> Int -> Scope -> Scope
andNotToNotOr n (And (Not f1) (Not f2)) m sc = case getFromScope sc n of
                                                Nothing -> outOfScope sc
                                                Just f -> case replaceNth (And (Not f1) (Not f2)) (Not (Or f1 f2)) f (Just m) of
                                                    (Just _, _) -> addError "Can't find specified occurence" sc
                                                    (Nothing, f') -> addToScope f' sc
andNotToNotOr n f m sc = addError "Formula must be the negation of an or formula" sc

notExistToForallNot :: Int -> Formula -> Int -> Scope -> Scope
notExistToForallNot n (Not (Exist v f)) m sc = case getFromScope sc n of
                                                Nothing -> outOfScope sc
                                                Just f' -> case replaceNth (Not (Exist v f)) (Forall v (Not f)) f' (Just m) of
                                                            (Just _, _) -> addError "Can't find specified occurence" sc
                                                            (Nothing , f'') -> addToScope f'' sc
notExistToForallNot n f m sc = addError "Formula must begin by not exist" sc

forallNotToNotExist :: Int -> Formula -> Int -> Scope -> Scope
forallNotToNotExist n (Forall v (Not f)) m sc = case getFromScope sc n of
                                                    Nothing -> outOfScope sc
                                                    Just f' -> case replaceNth (Forall v (Not f)) (Not (Exist v f)) f' (Just m) of
                                                                (Just _, _) -> addError "Can't find specified occurence" sc
                                                                (Nothing , f'') -> addToScope f'' sc
forallNotToNotExist n f m sc = addError "Formula must begin by not exist" sc

