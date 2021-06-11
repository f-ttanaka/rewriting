import TRS
import AST
import Parser
import Text.ParserCombinators.Parsec
import System.Environment

main :: IO ()
main = do
  file : _ <- getArgs
  text <- readFile file
  case parse parseProgram file text of
    Left e -> error (show e)
    Right program -> evalProgram [] program

-- evalProgram
evalProgram :: TRS -> Program -> IO ()
evalProgram _ [] = putStrLn ""
evalProgram trs (s:ss)
  | (Eq r) <- s = do
      putStrLn (show s)
      evalProgram (r:trs) ss
  | (Red_Li t) <- s = do
      putStrLn (show s)
      putStrLn (show (nf_li trs t))
      evalProgram trs ss
  | (Red_Lo t) <- s = do
      putStrLn (show s)
      putStrLn (show (nf_lo trs t))
      evalProgram trs ss
  | Check_Left_Linearity <- s = do
      putStrLn (show s)
      putStrLn (show (leftLinear trs))
      evalProgram trs ss
  | Check_Orthogonality <- s = do
      putStrLn (show s)
      putStrLn (show (orthogonal trs))
      evalProgram trs ss
  | Critical_Pairs <- s = do
      putStrLn (show s)
      putStrLn (show (criticalPairs trs))
      evalProgram trs ss
  | Check_Left_Normality <- s = do
      putStrLn (show s)
      putStrLn (show (left_normal trs))
      evalProgram trs ss