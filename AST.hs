module AST where

import TRS

data Statement = Eq Rule | Red_Li Term | Red_Lo Term | Check_Left_Linearity | Check_Orthogonality | Critical_Pairs | Check_Left_Normality
type Program = [Statement]

instance Show Statement where
    show (Eq (l,r)) = "eq " ++ show l ++ " = " ++ show r ++ " ."
    show (Red_Li t) = "red_li " ++ show t ++ " ."
    show (Red_Lo t) = "red_lo " ++ show t ++ " ."
    show Check_Left_Linearity = "check_left_linearity ."
    show Check_Orthogonality = "check_orthogonality ."
    show Critical_Pairs = "critical_pairs ."
    show Check_Left_Normality = "check_left_normality ."

showProgram :: Program -> String
showProgram p = unlines [show s | s <- p]