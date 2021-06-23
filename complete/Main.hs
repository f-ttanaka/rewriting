import GHC.IO.Handle
import System.Process
import Text.ParserCombinators.Parsec
import System.Environment
import Data.List (sortBy, intercalate)
import Data.Ord (comparing)
import TPDBParser
import TRS
import SMTParser

-- main = do
--   file : _ <- getArgs
--   text <- readFile file
--   case parse parseTPDB file text of
--     Left e -> error (show e)
--     Right trs -> do
--         writeFile "output.smt2" (concat [show f | f <- terminatingSMT trs])
--         (_, Just out, _, _) <- createProcess (proc "z3" ["output.smt2"]){ std_out = CreatePipe }
--         s <- hGetContents out
--         writeFile "precedence.txt" s
--         p <- readFile "precedence.txt"
--         case parse parseSMTOutput "precedence.txt" p of
--           Left e -> error (show e)
--           Right r -> case r of
--             Just ps -> let ps' = sortBy (\(f1,n1) (f2,n2) -> compare n1 n2) ps
--                            pr  = fst (unzip ps') in
--                        writeFile "complete.txt" (intercalate "\n" [show l ++ " -> " ++ show r| (l,r) <- complete pr trs])
--             Nothing -> putStrLn "unsat"

main = do
  file : _ <- getArgs
  text <- readFile file
  case parse parseTPDB file text of
    Left e -> error (show e)
    Right trs -> do
      writeFile "complete.txt" (intercalate "\n" [show l  ++ " -> " ++ show r | (l,r) <- complete ["i","*","e","g","f"] trs])