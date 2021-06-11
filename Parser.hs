module Parser where

import Text.ParserCombinators.Parsec
import TRS
import AST

lident :: Parser String
lident = do
  whitespaces
  c <- lower
  x <- many (alphaNum <|> char '_')
  whitespaces
  return (c : x)

uident :: Parser String
uident = do
  whitespaces
  c <- upper
  x <- many alphaNum
  whitespaces
  return (c : x)

keyword :: String -> Parser ()
keyword s = do
  spaces
  _ <- string s
  spaces
  return ()

num :: Parser Int
num = do
  whitespaces
  s <- many1 digit
  whitespaces
  return (read s :: Int)

parseTerm :: Parser Term
parseTerm = try parseFunction <|> parseInParentheses <|> parseVariable <|> parseNum <|> parseList
 
parseVariable :: Parser Term
parseVariable = do
  x <- uident
  return (V x)

parseFunction :: Parser Term
parseFunction = do
  f <- lident
  return (F f [])

parseTerms :: Parser Term
parseTerms = do
  f <- parseTerm
  ts <- sepBy parseTerm whitespaces
  return (apply f ts)

parseInParentheses :: Parser Term
parseInParentheses = do
    keyword "("
    f <- parseTerms
    keyword ")"
    return f

apply :: Term -> [Term] -> Term
apply f [] = f
apply f (t:ts) = apply (F "app" [f,t]) ts

parseNum :: Parser Term
parseNum = do
  n <- num
  return (peano n)

-- 数字をペアノ数に変換
peano :: Int -> Term
peano 0 = (F "zero" [])
peano n = (F "app" [F "s" [], peano (n-1)])

-- リストのパーサー
parseList :: Parser Term
parseList = do
  keyword "["
  ts <- sepBy parseTerm (keyword ",")
  keyword "]"
  return (listTerm ts)

-- リストをcons関数に変換
listTerm :: [Term] -> Term
listTerm [] = F "nil" []
listTerm (t:ts) = F "app" [F "app" [F "cons" [], t], listTerm ts]

-- parserProgram
-- parserRule,parserRedの返り値の型を修正しparserStatement,parserProgramを作成
parseRule :: Parser Statement
parseRule = do
  keyword "eq"
  l <- parseTerms
  keyword "="
  r <- parseTerms
  keyword "."
  whitespaces
  return (Eq (l,r))

parseRed :: Parser Statement
parseRed = do
  keyword "red"
  t <- parseTerms
  keyword "."
  whitespaces
  return (Red_Lo t)

parseCheckLeftLinearity :: Parser Statement
parseCheckLeftLinearity = do
  keyword "check_left_linearity ."
  whitespaces
  return Check_Left_Linearity

parseOrthogonality :: Parser Statement
parseOrthogonality = do
  keyword "orthogonality ."
  whitespaces
  return Check_Orthogonality

parseCriticalPairs :: Parser Statement
parseCriticalPairs = do
  keyword "critical_pairs ."
  whitespaces
  return Critical_Pairs

parseCheckLeftNormality :: Parser Statement
parseCheckLeftNormality = do
  keyword "left_normality ."
  whitespaces
  return Check_Left_Normality

parseStatement :: Parser Statement
parseStatement = try parseRule <|> parseRed <|> parseCheckLeftNormality <|> parseOrthogonality <|> parseCriticalPairs

parseProgram :: Parser Program
parseProgram = many parseStatement

-- コメント処理
comment :: Parser ()
comment = do
  keyword "--"
  c <- manyTill anyChar (try (char '\n'))
  return ()

-- スペース1文字に対し()を返す
skipSpace :: Parser ()
skipSpace = do
  space
  return ()

whitespaces = many (skipSpace <|> comment)