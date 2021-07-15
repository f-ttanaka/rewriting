import GHC.IO.Handle
import System.Process
import Text.ParserCombinators.Parsec
import System.Environment
import Data.List (sortBy, intercalate, nub)
import Data.Ord (comparing)
import TPDBParser
import TRS
import SMTParser
import TPDBOutput

main = do
  file : _ <- getArgs
  text <- readFile file
  case parse parseTPDB file text of
    Left e -> error (show e)
    Right (es,ps) -> let result = complete ps es in case result of
      Success trs -> mapM print (trsToTPDB trs)
      Fail trs -> do
        putStrLn "Fail"
        mapM print [show l ++ " , " ++ show r | (l,r) <- trs]