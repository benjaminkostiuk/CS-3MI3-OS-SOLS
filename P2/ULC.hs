module ULC where

import Data.List
import Data.Char

-- Terms in λ-calculus
data Term =
      Var Var
    | Lam Var Term
    | App Term Term
    deriving (Eq)

-- Pretty-print terms
instance Show Term where
    show (Var v) = map toLower (show v)
    show (Lam v t) = "(\\" ++ (map toLower (show v)) ++ ". " ++ show t ++ ")"
    show (App t1 a@(App _ _)) = show t1 ++ " (" ++ show a ++ ")"
    show (App t1 t2) = show t1 ++ " " ++ show t2

-- Variables
data Var = A | B | C | D | E | F | G | H | I | J | K | L | M | N | O | P | Q | R | S | T | U | V | W | X | Y | Z
    deriving (Show, Eq)

-- List of all possible variable names
variables :: [Var]
variables = [A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q, R, S, T, U, V, W, X, Y, Z]

-- Return the list of ALL variables used in a λ-calculus term
vars :: Term -> [Var]
vars (Var x) = [x]
vars (Lam x t) = vars t `union` [x]
vars (App t1 t2) = vars t1 `union` vars t2

-- Given a list of terms return a variable unused by any term
-- If there is no unused varaible throw an error
unusedVar :: [Term] -> Var
unusedVar [] = head variables
unusedVar xs
    | available == [] = error "No available unused variables"
    | otherwise = head available
    where
        available = variables \\ (foldr (\t v -> vars t `union` v) [] xs)

-- Returns the set of free variables in a λ-calculus term
fv :: Term -> [Var]
fv (Var x) = [x]
fv (Lam x t) = fv t \\ [x]
fv (App t1 t2) = fv t1 `union` fv t2

-- Replace all occurences of variable `a` with variable `b` in the given Term
-- Assumes all occurences of the variable are bound
relabel :: Term -> Var -> Var -> Term
relabel v@(Var x) a b = if a == x then Var b else v
relabel (Lam x t) a b = if a == x then Lam b (relabel t a b) else Lam x (relabel t a b)
relabel (App t1 t2) a b = App (relabel t1 a b) (relabel t2 a b)

-- Perform a substitution over a term, replacing a variable with another
-- If conflicts occur in substitution replace variable under abstraction with unsed variable
sub :: Term -> Var -> Term -> Term
sub v@(Var var) x s = if var == x then s else v
sub (App t1 t2) x s = App (sub t1 x s) (sub t2 x s)
sub l@(Lam y t) x s
    | elem y (fv s) = Lam y' $ sub t' x s
    | x == y = l
    | otherwise = Lam y $ sub t x s
    where
        (Lam y' t') = relabel l y w
        w = unusedVar [l, s, Var x]

-- Check whether a term is in normal form or not
isNF :: Term -> Bool
isNF (Var _) = True
isNF (Lam _ _) = True
isNF (App (Lam _ _) _) = False
isNF (App (Var _) (Lam _ _)) = True
isNF (App t1 t2) = isNF t1 && isNF t2

-- Output the result of applying a single step of the call-by-value evaluation strategy
ssos :: Term -> Term
ssos t@(App t1 t2)
    | isNF t1 && isNF t2 = case t1 of 
        (Lam var inner) -> sub inner var t2     -- E-AppAbs
        _ -> t                                  -- Reflexivity
    | isNF t1 = App t1 (ssos t2)                -- E-App2
    | otherwise = App (ssos t1) t2              -- E-App1
ssos t = t                                      -- Reflexivity

-- Fully evaluate a λ-calculus term
eval :: Term -> Term
eval t = if isNF t then t else eval $ ssos t