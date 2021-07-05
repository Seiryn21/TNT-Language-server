module TLS.Tokenizer where

import           Data.Char
import qualified Data.Text as T
import           Text.Parsec.Pos
import           TLS.Types

data TokenType = Keyword String
               | Id String
               | Litteral Int
               | Symbol Char
               | Spaces
               deriving (Show)

type Consummed = (T.Text, SourcePos, Token)
type Consummer = T.Text -> SourcePos -> Maybe Consummed
type Token = (SourcePos, TokenType)

data TokenizeError = TokenizeError SourcePos Char deriving (Show)

addColumn :: SourcePos -> SourcePos
addColumn pos = incSourceColumn pos 1

addLine :: SourcePos -> SourcePos
addLine pos = incSourceLine (setSourceColumn pos 0) 1

checkSpecial :: String -> TokenType
checkSpecial "theorem" = Keyword "theorem"
checkSpecial "begin" = Keyword "begin"
checkSpecial "end" = Keyword "end"
checkSpecial str = if str `elem` instrs
                   then Keyword str
                   else Id str

consumeIdentifier :: Consummer
consumeIdentifier s pos = case T.uncons s of
                            Nothing -> Nothing
                            Just (c, s') -> if isLetter c
                                            then consumeIdentifier' [c] s' (addColumn pos)
                                            else Nothing
                          where consumeIdentifier' res s pos = case T.uncons s of
                                  Nothing -> Just (s, pos, (pos, checkSpecial $ reverse res))
                                  Just (c, s') -> if isLetter c
                                                  then consumeIdentifier' (c:res) s' (addColumn pos)
                                                  else Just (s, pos, (pos, checkSpecial $ reverse res))

consumeLitteral :: Consummer
consumeLitteral s pos = case T.uncons s of
                            Nothing -> Nothing
                            Just (c, s') -> if c == '0'
                                            then Just (s', addColumn pos, (addColumn pos, Symbol '0'))
                                            else if isDigit c
                                                 then consumeIdentifier' (digitToInt c) s' (addColumn pos)
                                                 else Nothing
                          where consumeIdentifier' res s pos = case T.uncons s of
                                  Nothing -> Just (s, pos, (pos, Litteral res))
                                  Just (c, s') -> if isDigit c
                                                  then consumeIdentifier' (res * 10 + digitToInt c) s' (addColumn pos)
                                                  else Just (s, pos, (pos, Litteral res))

consumeSymbol :: Consummer
consumeSymbol s pos = case T.uncons s of
                        Just ('+', s') -> Just (s', addColumn pos, (addColumn pos, Symbol '+'))
                        Just ('*', s') -> Just (s', addColumn pos, (addColumn pos, Symbol '*'))
                        Just ('(', s') -> Just (s', addColumn pos, (addColumn pos, Symbol '('))
                        Just (')', s') -> Just (s', addColumn pos, (addColumn pos, Symbol ')'))
                        Just ('=', s') -> Just (s', addColumn pos, (addColumn pos, Symbol '='))
                        Just ('~', s') -> Just (s', addColumn pos, (addColumn pos, Symbol '~'))
                        Just ('&', s') -> Just (s', addColumn pos, (addColumn pos, Symbol '&'))
                        Just ('|', s') -> Just (s', addColumn pos, (addColumn pos, Symbol '|'))
                        Just ('⊂', s') -> Just (s', addColumn pos, (addColumn pos, Symbol '⊂'))
                        Just ('<', s') -> Just (s', addColumn pos, (addColumn pos, Symbol '<'))
                        Just ('>', s') -> Just (s', addColumn pos, (addColumn pos, Symbol '>'))
                        Just ('\'', s') -> Just (s', addColumn pos, (addColumn pos, Symbol '\''))
                        Just ('∀', s') -> Just (s', addColumn pos, (addColumn pos, Symbol '∀'))
                        Just ('∃', s') -> Just (s', addColumn pos, (addColumn pos, Symbol '∃'))
                        Just (':', s') -> Just (s', addColumn pos, (addColumn pos, Symbol ':'))
                        Just ('[', s') -> Just (s', addColumn pos, (addColumn pos, Symbol '['))
                        Just (']', s') -> Just (s', addColumn pos, (addColumn pos, Symbol ']'))
                        Just (',', s') -> Just (s', addColumn pos, (addColumn pos, Symbol ','))
                        _ -> Nothing

consumeSpace :: Consummer
consumeSpace s pos = case T.uncons s of
                        Nothing -> Nothing
                        Just ('\n', s') -> consumeSpace' s' (addLine pos)
                        Just ('\r', s') -> case T.uncons s' of
                                                Just ('\n', s'') -> consumeSpace' s'' (addLine pos)
                                                _ -> consumeSpace' s' (addLine pos)
                        Just (c, s') -> if isSpace c
                                        then consumeSpace' s' (addColumn pos)
                                        else Nothing
                        where consumeSpace' s pos = case T.uncons s of
                                                        Nothing -> Just (s, pos, (pos, Spaces))
                                                        Just ('\n', s') -> consumeSpace' s' (addLine pos)
                                                        Just ('\r', s') -> case T.uncons s' of
                                                                              Just ('\n', s'') -> consumeSpace' s'' (addLine pos)
                                                                              _ -> consumeSpace' s' (addLine pos)
                                                        Just (c, s') -> if isSpace c
                                                                        then consumeSpace' s' (addColumn pos)
                                                                        else Just (s, pos, (pos, Spaces))

allConsummer :: [Consummer]
allConsummer = [ consumeLitteral
               , consumeIdentifier
               , consumeSymbol
               , consumeSpace
               ]

foldConsummer :: T.Text -> SourcePos -> Maybe Consummed -> Consummer -> Maybe Consummed
foldConsummer s pos Nothing  consummer = consummer s pos
foldConsummer s pos (Just r) consummer = Just r

consume :: SourcePos -> T.Text -> Either Consummed TokenizeError
consume pos s = let Just (c, s') = T.uncons s in
                case foldl (foldConsummer s pos) Nothing allConsummer of
                      Nothing -> Right (TokenizeError pos c)
                      Just result -> Left result


tokenize :: SourcePos -> T.Text -> Either [Token] TokenizeError
tokenize pos s = case T.uncons s of
                    Nothing -> Left []
                    _ -> case consume pos s of
                            Left (remain, pos', token) -> case tokenize pos' remain of
                                Left tokens -> Left (token:tokens)
                                Right error -> Right error
                            Right error -> Right error

tokenizeFile :: String -> T.Text -> Either [Token] TokenizeError
tokenizeFile str = tokenize $ newPos str 0 0