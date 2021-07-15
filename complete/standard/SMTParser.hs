module SMTParser where

import Text.ParserCombinators.Parsec
import TRS

type SMTOutput = Maybe [(String, Int)]

parseVarVal :: Parser (String, Int)
parseVarVal = do
    spaces 
    char '('
    x <- many1 (noneOf " ")
    spaces
    n <- number
    char ')'
    return (x,n)

parseSat :: Parser SMTOutput
parseSat = do
    string "sat"
    newline
    char '('
    ps <- sepBy1 parseVarVal (char '\n')
    char ')'
    return (Just ps)

parseUnsat :: Parser SMTOutput
parseUnsat = do
    string "unsat"
    return Nothing

-- 数字を読み取る
number :: Parser Int
number = do
    s <- many1 digit
    return (read s :: Int)
    
parseSMTOutput :: Parser SMTOutput
parseSMTOutput = try parseSat <|> parseUnsat