module TLS.Parser where

import qualified Language.LSP.Types as LSP
import           Text.Parsec.Pos
import           Text.Parsec.Prim
import           Text.Parsec.Combinator
import           TLS.Instr
import           TLS.Tokenizer
import           TLS.Types

type Parser = Parsec [Token] ()

sourcePosToPosition :: SourcePos -> LSP.Position
sourcePosToPosition pos = LSP.Position (sourceLine pos) (sourceColumn pos)

showTok :: Token -> String
showTok (end,t) = show t

posFromTok :: SourcePos -> Token -> [Token] -> SourcePos
posFromTok pos (end, t) _ = end

keyword :: String -> Parser ()
keyword keyword = tokenPrim showTok posFromTok testTok <?> keyword
                  where testTok (end, t) = case t of
                                             Keyword keyword' -> if keyword == keyword' then Just () else Nothing
                                             _ -> Nothing

identifier :: Parser Identifier
identifier = do tokenPrim showTok posFromTok testTok <?> "identifier"
                where testTok (end, t) = case t of
                                           Id id -> Just id
                                           _ -> Nothing

number :: Parser Int
number = tokenPrim showTok posFromTok testTok <?> "litteral"
         where testTok (end, t) = case t of
                                    Litteral n -> Just n
                                    _ -> Nothing

symbol :: Char -> Parser Char
symbol c = tokenPrim showTok posFromTok testTok <?> [c]
           where testTok (end, t) = case t of
                                      Symbol c' -> if c == c' then Just c else Nothing
                                      _ -> Nothing

spaces :: Parser ()
spaces = tokenPrim showTok posFromTok testTok <?> "space"
         where testTok (end, t) = case t of
                                    Spaces -> Just ()
                                    _ -> Nothing

numbers :: Parser [Int]
numbers = (do n <- number
              return [n])
      <|> (do symbol '['
              n <- sepBy1 (optional spaces *> number <* optional spaces) (symbol ',')
              symbol ']'
              return n)

parseZero :: Parser Term
parseZero = do symbol '0'
               return Zero

parseSuccsFold :: Maybe (Term -> Term) -> Char -> Maybe (Term -> Term)
parseSuccsFold Nothing _ = Nothing
parseSuccsFold (Just f) 'S' = Just $ Succ . f
parseSuccsFold (Just f) _ = Nothing

parseSuccs :: Parser (Term -> Term)
parseSuccs = try $ do iden <- identifier
                      maybe parserZero return (foldl parseSuccsFold (Just id) iden)

parseSucc :: Parser Term
parseSucc = do succs <- parseSuccs
               succs <$> parseTerm

parseAddMul :: Parser Term
parseAddMul = do symbol '('
                 t1 <- parseTerm
                 c <- symbol '+' <|> symbol '*'
                 t2 <- parseTerm
                 symbol ')'
                 case c of
                   '+' -> return $ Add t1 t2
                   '*' -> return $ Mul t1 t2

parsePrime :: Var -> Parser Var
parsePrime v = symbol '\'' *> parsePrime (Prime v)
           <|> return v

parseVarFold :: (Maybe (Term -> Term), Maybe Var) -> Char -> (Maybe (Term -> Term), Maybe Var)
parseVarFold (Nothing, _)  _ = (Nothing, Nothing)
parseVarFold (Just f, Nothing) 'S' = (Just $ Succ . f, Nothing)
parseVarFold (Just f, Nothing) 'a' = (Just f, Just A)
parseVarFold (Just f, Nothing) 'b' = (Just f, Just B)
parseVarFold (Just f, Nothing) 'c' = (Just f, Just C)
parseVarFold (Just f, Nothing) 'd' = (Just f, Just D)
parseVarFold (Just f, Nothing) 'e' = (Just f, Just E)
parseVarFold (Just f, _) _ = (Nothing, Nothing)

parseTermVar ::  Parser Term
parseTermVar = do (f,v) <- try $ do iden <- identifier
                                    case foldl parseVarFold (Just id,Nothing) iden of
                                      (Nothing, Nothing) -> parserZero
                                      (Just f, Just v) -> return(f, v)
                  primes <- many (symbol '\'')
                  return $ f $ Var $ foldl (\a _ -> Prime a) v primes



parseTerm :: Parser Term
parseTerm = do parseZero
           <|> parseSucc
           <|> parseAddMul
           <|> parseTermVar

parseEq :: Parser Formula
parseEq = do t1 <- parseTerm
             symbol '='
             Eq t1 <$> parseTerm

parseNot :: Parser Formula
parseNot = do symbol '~'
              Not <$> parseFormula

parseAndOrImplie :: Parser Formula
parseAndOrImplie = do symbol '<'
                      f1 <- parseFormula
                      c <- symbol '&' <|> symbol '|' <|> symbol '⊂'
                      f2 <- parseFormula
                      symbol '>'
                      case c of
                        '&' -> return (And f1 f2)
                        '|' -> return (Or f1 f2)
                        '⊂' -> return (Implie f1 f2)

parseVar :: Parser Var
parseVar = do v <- try $ do id <- identifier
                            case id of
                              "a" -> return A
                              "b" -> return B
                              "c" -> return C
                              "d" -> return D
                              "e" -> return E
                              _ -> parserZero
              primes <- many (symbol '\'')
              return (foldl (\a _ -> Prime a) v primes)

parseForall :: Parser Formula
parseForall = do symbol '∀'
                 v <- parseVar
                 symbol ':'
                 Forall v <$> parseFormula

parseExist :: Parser Formula
parseExist = do symbol '∃'
                v <- parseVar
                symbol ':'
                Exist v <$> parseFormula

parseFormula :: Parser Formula
parseFormula = parseEq
           <|> parseNot
           <|> parseAndOrImplie
           <|> parseForall
           <|> parseExist

parseAxiom :: Parser Instr
parseAxiom = do keyword "axiom"
                spaces
                axiom <$> number

parseAddTheorem :: Parser Instr
parseAddTheorem = do keyword "theorem"
                     spaces
                     theorem <$> identifier

parseOpenFantasy :: Parser Instr
parseOpenFantasy = do keyword "openFantasy"
                      spaces
                      openFantasy <$> parseFormula

parseCloseFantasy :: Parser Instr
parseCloseFantasy = do keyword "closeFantasy"
                       return closeFantasy

parseSymmetry :: Parser Instr
parseSymmetry = do keyword "symmetry"
                   spaces
                   symmetry <$> number

parseTransitivity :: Parser Instr
parseTransitivity = do keyword "transitivity"
                       spaces
                       ab <- number
                       spaces
                       transitivity ab <$> number

parseAddSucc :: Parser Instr
parseAddSucc = do keyword "addSucc"
                  spaces
                  addSucc <$> number

parseRemoveSucc :: Parser Instr
parseRemoveSucc = do keyword "addSucc"
                     spaces
                     removeSucc <$> number

parseJoin :: Parser Instr
parseJoin = do keyword "join"
               spaces
               m <- number
               spaces
               join m <$> number

parseSepare :: Parser Instr
parseSepare = do keyword "separe"
                 spaces
                 m <- number
                 spaces
                 separe m <$> number

parseDetach :: Parser Instr
parseDetach = do keyword "detach"
                 spaces
                 m <- number
                 spaces
                 detach m <$> number

parseContrapose :: Parser Instr
parseContrapose = do keyword "contrapose"
                     spaces
                     contrapose <$> number

parseSpecialize :: Parser Instr
parseSpecialize = do keyword "specialize"
                     spaces
                     n <- number
                     spaces
                     specialize n <$> parseTerm

parseGeneralize :: Parser Instr
parseGeneralize = do keyword "generalize"
                     spaces
                     n <- number
                     spaces
                     generalize n <$> parseVar

parseExistence :: Parser Instr
parseExistence = do keyword "existence"
                    spaces
                    n <- number
                    spaces
                    t <- parseTerm
                    spaces
                    v <- parseVar
                    existence n t v <$> numbers

parseRecurence :: Parser Instr
parseRecurence = do keyword "recurence"
                    spaces
                    m <- number
                    spaces
                    n <- number
                    spaces
                    recurence m n <$> parseFormula

parseAddDoubleNeg :: Parser Instr
parseAddDoubleNeg = do keyword "addDoubleNeg"
                       spaces
                       m <- number
                       spaces
                       f <- parseFormula
                       spaces
                       addDoubleNeg m f <$> number

parseRemoveDoubleNeg :: Parser Instr 
parseRemoveDoubleNeg = do keyword "removeDoubleNeg"
                          spaces
                          m <- number
                          spaces
                          f <- parseFormula
                          spaces
                          removeDoubleNeg m f <$> number

parseNotOrToAndNot :: Parser Instr
parseNotOrToAndNot = do keyword "notOrToAndNot"
                        spaces
                        m <- number
                        spaces
                        f <- parseFormula
                        spaces
                        notOrToAndNot m f <$> number
 
parseAndNotToNotOr :: Parser Instr
parseAndNotToNotOr = do keyword "andNotToNotOr"
                        spaces
                        m <- number
                        spaces
                        f <- parseFormula
                        spaces
                        andNotToNotOr m f <$> number

parseNotExistToForallNot :: Parser Instr
parseNotExistToForallNot = do keyword "notExistToForallNot"
                              spaces
                              m <- number
                              spaces
                              f <- parseFormula
                              spaces
                              notExistToForallNot m f <$> number

parseForallNotToNotExist :: Parser Instr
parseForallNotToNotExist = do keyword "forallNotToNotExist"
                              spaces
                              m <- number
                              spaces
                              f <- parseFormula
                              spaces
                              forallNotToNotExist m f <$> number

parseInstr :: Parser Instr
parseInstr = parseAxiom
         <|> parseAddTheorem
         <|> parseOpenFantasy
         <|> parseCloseFantasy
         <|> parseSymmetry
         <|> parseTransitivity
         <|> parseAddSucc
         <|> parseRemoveSucc
         <|> parseJoin
         <|> parseSepare
         <|> parseDetach
         <|> parseContrapose
         <|> parseSpecialize
         <|> parseGeneralize
         <|> parseExistence
         <|> parseRecurence
         <|> parseAddDoubleNeg
         <|> parseRemoveDoubleNeg
         <|> parseNotOrToAndNot
         <|> parseAndNotToNotOr
         <|> parseNotExistToForallNot
         <|> parseForallNotToNotExist
         <?> "command"

parseInstrBlock :: Parser InstrBlock
parseInstrBlock = do p1 <- getPosition
                     optional spaces
                     p1' <- getPosition
                     instr <- optionMaybe parseInstr
                     p2' <- getPosition
                     optional spaces
                     p2 <- getPosition
                     return (instr, LSP.Range (sourcePosToPosition p1) (sourcePosToPosition p2),
                                    LSP.Range (sourcePosToPosition p1') (sourcePosToPosition p2'))

parseTheorem :: Parser Theorem
parseTheorem = do keyword "theorem"
                  spaces
                  p1 <- getPosition
                  identifier <- identifier
                  p2 <- getPosition
                  spaces
                  formula <- parseFormula
                  spaces
                  keyword "begin"
                  p3 <- getPosition
                  instrBlocks <- try parseInstrBlock `sepBy` symbol ','
                  p4 <- getPosition
                  keyword "end"
                  return $ Theorem (LSP.Range (sourcePosToPosition p1) (sourcePosToPosition p2)) (LSP.Range (sourcePosToPosition p3) (sourcePosToPosition p4)) identifier formula instrBlocks

parseFile :: Parser [Theorem]
parseFile = many (optional spaces *> parseTheorem <* optional spaces)
