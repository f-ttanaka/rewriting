module TRS where

import Data.List

data Term = V String | F String [Term] deriving Eq

type Position = [Int]

instance Show Term where
  show t = showTerm1 t

termToInt :: Term -> Maybe Int
termToInt (F "zero" []) = Just 0
termToInt (F "app" [F "s" [], t]) = case termToInt t of
  Just n -> Just (1+n)
  Nothing -> Nothing
termToInt _ = Nothing

termToList :: Term -> Maybe [Term]
termToList (F "nil" []) = Just []
termToList (F "app" [F "app" [F "cons" _, car], cdr]) = case termToList cdr of
  Just lst -> Just (car : lst)
  Nothing -> Nothing
termToList _ = Nothing

notNumber :: Term -> Bool
notNumber t
  | Nothing <- termToInt t = True
  | otherwise = False

notList :: Term -> Bool
notList t
  | Nothing <- termToList t = True
  | otherwise = False

showTerm1 :: Term -> String
showTerm1 t@(F "app" [t1, t2])
  | notNumber t && notList t = showTerm1 t1 ++ " " ++ showTerm2 t2 
showTerm1 t = showTerm2 t

showTerm2 :: Term -> String
showTerm2 t
  | Just n <- termToInt t = show n
  | Just l <- termToList t = "[" ++ intercalate "," [showTerm1 e | e <- l] ++ "]"
showTerm2 (V x) = x
showTerm2 (F c []) = c
showTerm2 (F _ ts) = "(" ++ intercalate " " [showTerm1 t | t <- ts] ++ ")"


-- Pos(t) 最左最内戦略の場合
positions_li :: Term -> [Position]
positions_li (V _) = [[]]
positions_li (F _ ts) = [ i : p | (i, t) <- zip [0..] ts, p <- positions_li t ] ++ [[]]

-- Pos(t) 最左最外戦略の場合
positions_lo :: Term -> [Position]
positions_lo (V _) = [[]]
positions_lo (F _ ts) = [] : [ i : p | (i, t) <- zip [0..] ts, p <- positions_lo t ]

-- subtermAt t p = t|_p
subtermAt :: Term -> Position -> Term
subtermAt t [] = t
subtermAt (F _ ts) (i:p) = subtermAt (ts !! i) p

-- replace t u p = t[u]_p
replace :: Term -> Term -> Position -> Term
replace t s [] = s
replace (F f ts) s (i : q) =
   F f [ if i == j then replace tj s q else tj | (j, tj) <- zip [0..] ts]

type Subst = [(String, Term)]

-- substitute t σ= tσ
substitute :: Term -> Subst -> Term
substitute t [] = t
substitute t@(V x) sigma
  | Just t_s <- lookup x sigma = t_s
  | otherwise = t
substitute (F f ts) ss = F f [substitute t ss | t <- ts]

-- match l t = Just σ, if lσ = t for some σ 
-- match l t = Nothing, otherwise
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

type Rule  = (Term, Term)
type TRS = [Rule]

-- showTRS
showRule :: Rule -> String
showRule (l,r) = show l ++ "->" ++ show r

showTRS :: TRS -> String
showTRS trs = unlines [showRule rule | rule <- trs]

reducts_li :: TRS -> Term -> [Term]
reducts_li [] _ = []
reducts_li rs t = 
  [replace t (substitute t_r sigma) p | p <- positions_li t, (t_l,t_r) <- rs, Just sigma <- [match t_l (subtermAt t p)]]

rewrite_li :: TRS -> Term -> Maybe Term
rewrite_li rs t
  | (u:_) <- reducts_li rs t = Just u
  | otherwise = Nothing

nf_li :: TRS -> Term -> Term
nf_li rs t
  | Just u <- rewrite_li rs t = nf_li rs u
  | otherwise = t

reducts_lo :: TRS -> Term -> [Term]
reducts_lo [] _ = []
reducts_lo rs t = 
  [replace t (substitute t_r sigma) p | p <- positions_lo t,　(t_l,t_r) <- rs, Just sigma <- [match t_l (subtermAt t p)]]

rewrite_lo :: TRS -> Term -> Maybe Term
rewrite_lo rs t
  | (u:_) <- reducts_lo rs t = Just u
  | otherwise = Nothing

nf_lo :: TRS -> Term -> Term
nf_lo rs t
  | Just u <- rewrite_lo rs t = nf_lo rs u
  | otherwise = t

-- Term内のVariableのリストを返す
variables :: Term -> [String]
variables (V x) = [x]
variables (F _ ts) = [x | t <- ts, x <- variables t]

-- リスト内に重複する要素があればTrue,そうでなければFalseを返す
redundant :: Eq a => [a] -> Bool
redundant [] = True
redundant (x:xs)
  | elem x xs = False
  | otherwise = redundant xs

-- あるTermが重複するVariableを持たない場合はTrue,それでなければFalseを返す
linear :: Term -> Bool
linear t
  | vs@(_:_) <- variables t = redundant vs
  | otherwise = True

leftLinear :: TRS -> Bool
leftLinear [] = True
leftLinear ((l,_):trs) = linear l && leftLinear trs

domain :: Subst -> Subst
domain sigma = [(x, t) | (x, t) <- sigma, (V x) /= t]

unionSubst :: Subst -> Subst -> Subst
unionSubst s1 s2 = s1 ++ [(x, t) | (x, t) <- s2, Nothing <- [lookup x s1]]

-- 
compose :: Subst -> Subst -> Subst
compose [] tau = tau
compose sigma tau = [(x, substitute t tau) | (x, t) <- dom]
  where dom = unionSubst (domain sigma) (domain tau)

-- occurs x t
-- if x occurs in Var(t) then True else False
occurs :: String -> Term -> Bool
occurs x t = elem x (variables t)

-- unificate and reserve Subst
mgu' :: [Subst] -> [(Term, Term)] -> Maybe Subst
mgu' sigmas [] = Just (foldl compose [] sigmas)
mgu' sigmas ((V x, t):ps)
  | (V y) <- t, x == y = mgu' sigmas ps -- Delete
  | occurs x t = Nothing
  | otherwise = mgu' (sigmas ++ [[(x, t)]]) [(substitute l [(x,t)], substitute r [(x,t)]) | (l,r) <- ps] -- Eliminate
mgu' sigmas ((t, V y):ps) = mgu' sigmas ((V y, t):ps) -- Orient
mgu' sigmas ((F f ss, F g ts) : ps)
  | f == g = mgu' sigmas ((zip ss ts) ++ ps) -- Decompose
  | otherwise = Nothing

mgu :: Term -> Term -> Maybe Subst
mgu s t = mgu' [] [(s,t)]

-- 変数名とindexの連想リストを受け取り、Term内の変数名を(x ++ show i)と書き換えていく
rename' :: String -> [(String, Int)] -> Term -> Term
rename' x ps (V y)
  | Just i <- lookup y ps = V (x ++ show i)
  | otherwise = V x
rename' x ps (F f ts) = F f [rename' x ps t | t <- ts]

rename :: String -> Int -> Term -> Term
rename x n t = rename' x indexList t
  where indexList = zip (nub (variables t)) [n..]

renameTRS :: String -> TRS -> TRS
renameTRS x trs = [(rename x 0 l, rename x 0 r) | (l, r) <- trs]

nonVariable :: Term -> Bool
nonVariable t
  | V _ <- t = False
  | otherwise = True

-- (l1, r1)と(l2, r2)が、同じ形であるかどうか調べる
sameRule :: Rule -> Rule -> Bool
sameRule (l1, r1) (l2, r2) = rename "x" 0 l1 == rename "x" 0 l2 && rename "x" 0 r1 == rename "x" 0 r2

criticalPairs :: TRS -> [(Term, Term)]
criticalPairs trs =
  [(substitute (replace l2 r1 p) sigma, substitute r2 sigma)
  | (l1, r1) <- renameTRS "x" trs,
    (l2, r2) <- renameTRS "y" trs,
    p <- positions_lo l2,
    nonVariable (subtermAt l2 p),
    if null p then not (sameRule (l1, r1) (l2, r2)) else True,
    Just sigma <- [mgu l1 (subtermAt l2 p)]]

orthogonal :: TRS -> Bool
orthogonal trs = leftLinear trs && null (criticalPairs trs)

-- 項がGroundかどうか判定
isGround :: Term -> Bool
isGround (V _) = False
isGround (F _ []) = True
isGround (F _ ts) = all isGround ts

-- 項の集合が変数のみからなるものかどうか判定
isOnlyVariables :: [Term] -> Bool
isOnlyVariables [] = True
isOnlyVariables ((V _):ts) = isOnlyVariables ts
isOnlyVariables ((F _ _):_) = False

-- 項の引数がleft_normalを満たすかどうか調べる補助関数
normalArgs :: [Term] -> Bool
normalArgs [] = True
normalArgs (t:args)
  | isGround t = normalArgs args
  | normal t = isOnlyVariables args
  | otherwise = False

normal :: Term -> Bool
normal (V _) = True
normal (F _ ts) = normalArgs ts

left_normal :: TRS -> Bool
left_normal [] = True
left_normal ((l,_):trs) = normal l && left_normal trs 