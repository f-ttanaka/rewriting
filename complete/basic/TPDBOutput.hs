module TPDBOutput where

import Data.List(intercalate,nub)
import TRS

data Format = Vars [String]
            | LPO Precedence
            | Rules TRS

extractVars :: TRS -> [String]
extractVars trs = nub [x | (l,r) <- trs, x <- nub (variables l ++ variables r)]

instance Show Format where
    show (Vars xs) = "(VAR " ++ (intercalate " " xs) ++ ")"
    show (LPO fs)  = "(LPO " ++ (intercalate " " fs) ++ ")"
    show (Rules trs) = "(RULES\n" ++ (intercalate "\n" [show l ++ " -> " ++ show r | (l,r) <- trs]) ++ "\n)"

trsToTPDB :: TRS -> [Format]
trsToTPDB trs = [Vars (extractVars trs)] ++ [Rules trs]