module TPDBParser where

import Text.ParserCombinators.Parsec
import TRS

ident :: Parser String
ident = do
  c <- noneOf "()"
  x <- many (alphaNum <|> char '_')
  return (c : x)

-- 数字を読み取る
number :: Parser Int
number = do
  s <- digit
  ss <- many digit
  return (read (s:ss) :: Int)


parseTerm :: [String] -> Parser Term
parseTerm vs = try parseNum <|> parseVF vs

parseVF :: [String] -> Parser Term
parseVF vs = do
  spaces
  i <- ident
  ts <- option [] (parseArgs vs)
  spaces
  return (if null ts && elem i vs then (V i) else (F i ts))

parseArgs :: [String] -> Parser [Term]
parseArgs xs = do
  char '('
  ts <- sepBy (parseTerm xs) (char ',')
  char ')'
  return ts

-- 数字のパーサー
parseNum :: Parser Term
parseNum = do
  spaces
  n <- number
  spaces
  return (intToPeano n)

-- 数字をペアノ数に変換
intToPeano :: Int -> Term
intToPeano 0 = (F "0" [])
intToPeano n = (F "s" [intToPeano (n-1)])
 
parseVAR :: Parser [String]
parseVAR = do
  spaces
  char '('
  string "VAR"
  many1 space
  vs <- parseVAR'
  return vs

parseVAR' :: Parser [String]
parseVAR' = do
  try (do {char ')'; return []})
      <|> do {v <- many1 alphaNum; spaces; vs <- parseVAR'; return (v:vs)}

parseRule :: [String] -> Parser Rule
parseRule vs = do
  l <- parseTerm vs
  string "->"
  r <- parseTerm vs
  return (l,r)

parseRULES :: [String] -> Parser TRS
parseRULES vs = do
  spaces
  char '('
  string "RULES"
  many1 (try space <|> newline)
  rs <- parseRULES' vs
  return rs

parseRULES' :: [String] -> Parser TRS
parseRULES' vs = do
  try (do {char ')'; return []})
      <|> do {r <- parseRule vs; spaces; rs <- parseRULES' vs; return (r:rs)}

-- コメント処理
parseCOMMENT :: Parser ()
parseCOMMENT = do
  string "COMMENT"
  newline
  many1 (noneOf "()")
  return ()

parseStatement :: Parser a -> Parser a
parseStatement p = do
  spaces
  char '('
  s <- p
  char ')'
  spaces
  return s

parseTPDB :: Parser TRS
parseTPDB = do
  vs <- parseVAR
  rs <- parseRULES vs
  return rs
