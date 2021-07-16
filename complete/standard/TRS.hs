module TRS where

import Data.List
import Data.Maybe

import SMT

data Term = V String | F String [Term] 
            deriving Eq

instance Show Term where
    show (V x) = x
    show (F f ts) = f ++ "(" ++ intercalate "," [show t | t <- ts] ++ ")"

type Position = [Int]

positions :: Term -> [Position]
positions (V _) = [[]]
positions (F _ ts) = [] : [i:p | (i,t) <- zip [0..] ts, p <- positions t]

subtermAt :: Term -> Position -> Term
subtermAt t [] = t
subtermAt (F _ ts) (n:ns) = subtermAt (ts !! n) ns
subtermAt (V _) (_:_) = error "subtermAt"

replace :: Term -> Term -> Position -> Term
replace _ t [] = t
replace (F f ss) t (n:ns) =
    F f [if i == n then replace si t ns else si | (i,si) <- zip [0..] ss]
replace (V _) _ (_:_) = error "replace"

type Subst = [(String,Term)]

substitute :: Term -> Subst -> Term
substitute t [] = t
substitute t@(V x) sigma
  | Just t' <- lookup x sigma = t'
  | otherwise                 = t
substitute (F f ts) sigma = F f [substitute t sigma | t <- ts]

match' :: Subst -> [(Term, Term)] -> Maybe Subst
match' sigma [] = Just sigma
match' sigma ((V x, t):ps)
  | Nothing <- m = match' (sigma ++ [(x, t)]) ps
  | Just u <- m, t == u = match' sigma ps
  | otherwise = Nothing
    where m = lookup x sigma
match' sigma ((F f ss, F g ts) : ps)
  | f == g = match' sigma ((zip ss ts) ++ ps)
  | otherwise = Nothing
match' _ _ = Nothing

match :: Term -> Term -> Maybe Subst
match s t = match' [] [(s,t)]

type Rule = (Term,Term)
type TRS = [Rule]

reducts :: TRS -> Term -> [Term]
reducts [] _ = []
reducts rs t = 
  [replace t (substitute t_r sigma) p | p <- positions t, (t_l,t_r) <- rs, Just sigma <- [match t_l (subtermAt t p)]]

reducible :: TRS -> Term -> Bool
reducible rs t
  | (_:_) <- reducts rs t = True
  | otherwise = False

rewrite :: TRS -> Term -> Maybe Term
rewrite rs t
  | (u:_) <- reducts rs t = Just u
  | otherwise = Nothing

nf :: TRS -> Term -> Term
nf rs t
  | Just u <- rewrite rs t = nf rs u
  | otherwise = t

compose :: Subst -> Subst -> Subst
compose [] tau = tau
compose sigma tau =
    [(x, substitute s tau) | (x,s) <- sigma] ++ [(y,t) | (y,t) <- tau, isNothing (lookup y sigma)]

variables :: Term -> [String]
variables (V x) = [x]
variables (F _ ts) = nub (concat [variables t | t <- ts])

functions :: Term -> [String]
functions (V _) = []
functions (F f ts) = nub (f: concat [functions t | t <- ts])

occurs :: String -> Term -> Bool
occurs x (V y) = x == y
occurs x (F _ ts) = any (occurs x) ts

mgu' :: [Subst] -> [(Term, Term)] -> Maybe Subst
mgu' sigmas [] = Just (foldl compose [] sigmas)
mgu' sigmas ((V x, t):ps)
  | (V y) <- t, x == y = mgu' sigmas ps
  | occurs x t = Nothing
  | otherwise = mgu' (sigmas ++ [[(x, t)]]) [(substitute l [(x,t)], substitute r [(x,t)]) | (l,r) <- ps]
mgu' sigmas ((t, V y):ps) = mgu' sigmas ((V y, t):ps)
mgu' sigmas ((F f ss, F g ts) : ps)
  | f == g = mgu' sigmas (union (zip ss ts) ps)
  | otherwise = Nothing

mgu :: Term -> Term -> Maybe Subst
mgu s t = mgu' [] [(s,t)]

rename' :: [(String,Int)] -> String -> Term -> Term
rename' vs x (V y)
  | Just i <- lookup y vs = V (x ++ show i)
  | otherwise = V y
rename' vs x (F f ts) = F f [rename' vs x t | t <- ts]

rename :: Int -> String -> Term -> Term
rename n x t = rename' (zip (variables t) [n..]) x t

renameRule' :: [(String,Int)] -> String -> Rule -> Rule
renameRule' vs x (l,r) = (rename' vs x l, rename' vs x r)

renameRule :: String -> Int -> Rule -> Rule
renameRule x n (l,r) =
  renameRule' (zip (union (variables l) (variables r)) [n..]) x (l,r)

nonVariable :: Term -> Bool
nonVariable (V _) = False
nonVariable (F _ _) = True

sameRules :: Rule -> Rule -> Bool
sameRules r1 r2 = renameRule "x" 0 r1 == renameRule "x" 0 r2  

cp :: TRS -> TRS
cp trs =
  [(substitute r1 sigma, substitute (replace l1 r2 p) sigma)
                    | r  <- trs,
                      r' <- trs,
                      let (l1, r1) = renameRule "x" 0 r,
                      let (l2, r2) = renameRule "y" 0 r',
                      p <- positions l1,
                      let l1' = subtermAt l1 p,
                      nonVariable l1',
                      Just sigma <- [mgu l1' l2]]

type Precedence = [String]

gtLpo :: Precedence -> Term -> Term -> Bool
gtLpo _ s t@(V x) = elem x (variables s) && s /= t
gtLpo p s@(F f ss) t@(F g ts) =
    or [gtLpo p si t | si <- ss]
    || gtFunction p f g && and [gtLpo p s tj | tj <- ts]
    || f == g && and [gtLpo p s tj | tj <- ts] && gtArgs p ss ts
gtLpo _ (V _) (F _ _) = False

gtFunction :: Precedence -> String -> String -> Bool
gtFunction p f g = length (takeWhile (/= g) p) > length (takeWhile (/= f) p)

gtArgs :: Precedence -> [Term] -> [Term] -> Bool
gtArgs _ [] [] = True
gtArgs _ [] _ = False
gtArgs _ _ [] = True
gtArgs p (a:as) (b:bs) | a == b    = gtArgs p as bs
                       | otherwise = gtLpo p a b

gtLpoFormula :: Term -> Term -> Formula
gtLpoFormula s t@(V x) | elem x (variables s) && s /= t = FTrue 
                       | otherwise                      = FFalse  
gtLpoFormula s@(F f ss) t@(F g ts) =
    Or [Or [gtLpoFormula si t | si <- ss]
       ,c]
    where
        c = if f /= g
            then And [Geq (Var f) (Var g), And [gtLpoFormula s tj | tj <- ts]]
            else And [And [gtLpoFormula s tj | tj <- ts], gtArgsFormula ss ts]
gtLpoFormula (V _) _ = FFalse

gtArgsFormula :: [Term] -> [Term] -> Formula
gtArgsFormula [] _ = FFalse 
gtArgsFormula _ [] = FFalse 
gtArgsFormula (si:ss) (ti:ts) | si == ti  = gtArgsFormula ss ts
                              | otherwise = gtLpoFormula si ti

termToFunctionList :: Term -> [String]
termToFunctionList (V _) = []
termToFunctionList (F f ts) = nub (f : concat [termToFunctionList t | t <- ts])

trsToFunctionList :: TRS -> [String]
trsToFunctionList trs = nub (concat [union (functions l) (functions r) | (l,r) <- trs])

varConditions :: [Exp] -> Formula
varConditions fs = And [And [And [Geq (Val n) f, Geq f (Val 1)] | let n = length fs, f <- fs]
                       ,Distinct fs]

trsFormula :: TRS -> Formula
trsFormula rs = And [gtLpoFormula l r | (l,r) <- rs]

terminatingSMT :: TRS -> [Formula]
terminatingSMT rs = 
    [DeclareFun f | f <- fs] ++
    [Assert (And [varConditions fs, trsFormula rs]),
     CheckSat,
     GetValue fs]
     where
         fs = [Var f | f <- trsToFunctionList rs]

samePair :: Term -> Term -> Bool
samePair s t = rename 0 "x" s == rename 0 "x" t

sameTRS :: TRS -> TRS -> Bool
sameTRS rs1 rs2 =
  all (\r1 -> any (sameRules r1) rs2) rs1 && all (\r2 -> any (sameRules r2) rs1) rs2

data ProcessResult = Success TRS | Fail TRS

size :: Term -> Int
size (V _) = 1
size (F _ []) = 1
size (F _ ts) = sum [size t | t <- ts]

choose :: Precedence -> [(Term,Term)] -> Maybe (Rule, [(Term,Term)])
choose _ [] = error "choose"
choose p es
  | gtLpo p u v = Just ((u,v),es')
  | gtLpo p v u = Just ((v,u),es')
  | otherwise   = Nothing
  where
    ((u,v):es') = sortBy (\(s,t) (s',t') -> compare (size s + size t) (size s' + size t')) es

addEquations :: Rule -> TRS -> [(Term,Term)]
addEquations rr trs = [(nf [rr] l, r) | (l,r) <- trs, reducible [rr] l]

simplifyTRS :: TRS -> TRS
simplifyTRS trs = [(l, nf trs r) | (l,r) <- trs]

simplifyEquations :: TRS -> [(Term,Term)] -> [(Term,Term)]
simplifyEquations trs es = [(s', t') | (s,t) <- es,
                                       let s' = nf trs s,
                                       let t' = nf trs t,
                                       s' /= t']

-- complete' p ei ri
complete' :: Precedence -> TRS -> TRS -> Maybe TRS
complete' _ [] ri = Just ri
complete' p ei ri
  | Just ((l,r),ei') <- choose p ei =
    let ri' = unionBy sameRules ri [(l,r)]
        e1 = addEquations (l,r) ri
        e2 = cp ri'
        rj = simplifyTRS ri'
        ej = simplifyEquations rj (ei ++ e1 ++ e2)
    in complete' p ej rj
  | otherwise = Nothing

complete :: Precedence -> TRS -> ProcessResult
complete p trs
  | Just trs' <- complete' p trs [] = Success trs'
  | otherwise = Fail []