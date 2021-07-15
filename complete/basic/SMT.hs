module SMT where

data Exp = Var String | Val Int | Plus [Exp]

data Formula = And [Formula]
             | Or [Formula]
             | Not Formula
             | Distinct [Exp]
             | Geq Exp Exp
             | Eq Exp Exp
             | FTrue --真
             | FFalse --偽
             | DeclareFun Exp
             | Assert Formula
             | CheckSat
             | GetValue [Exp]

instance Show Exp where
    show (Var f) = f
    show (Val n) = show n
    show (Plus es) = "(+ " ++ unwords [show e | e <- es] ++ ")"

instance Show Formula where
    show (And []) = "(= 0 0)"
    show (And fs) = "(and " ++ concat [show f | f <- fs] ++ ")"
    show (Or []) = "(not (= 0 0))"
    show (Or fs) = "(or " ++ concat [show f | f <- fs] ++ ")"
    show (Not f) = "(not " ++ show f ++ ")"
    show (Distinct es) = "(distinct " ++ unwords [show e | e <- es] ++ ")"
    show (Geq e1 e2) = "(>= " ++ show e1 ++ " " ++ show e2 ++ ")"
    show (Eq e1 e2) = "(= " ++ show e1 ++ " " ++ show e2 ++ ")"
    show FTrue = "(= 0 0)"
    show FFalse = "(not (= 0 0))"
    show (DeclareFun x) = "(declare-fun " ++ show x ++ " () Int)"
    show (Assert f) = "(assert " ++ show f ++ ")"
    show CheckSat = "(check-sat)"
    show (GetValue vs) = "(get-value (" ++ unwords [show v | v <- vs] ++ "))"